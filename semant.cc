#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <map>
#include <set>
#include <vector>

extern int semant_debug;
extern char *curr_filename;

static Symbol 
    arg, arg2, Bool, concat, cool_abort, copy, Int, in_int, in_string, IO,
    length, Main, main_meth, No_class, No_type, Object, out_int, out_string,
    prim_slot, self, SELF_TYPE, Str, str_field, substr, type_name, val;

static void initialize_constants(void) {
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

// ====================================================================================
// FASE 1: Construcción y validación del grafo de herencia
// ====================================================================================

ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {
    install_basic_classes();

    // 1. Recolectar clases definidas por el usuario (en el orden del programa)
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ curr = classes->nth(i);
        Symbol name = curr->get_name();

        // Verificar redefinición de clases básicas o ya existentes
        if (name == Object || name == IO || name == Int || name == Bool || name == Str || name == SELF_TYPE) {
            semant_error(curr) << "Redefinition of basic class " << name << ".\n";
        } else if (class_map.find(name) != class_map.end()) {
            semant_error(curr) << "Class " << name << " was previously defined.\n";
        } else {
            class_map[name] = curr;
            user_classes.push_back(curr);
        }
    }

    // Si hay errores en las definiciones base, detenerse
    if (errors()) return;

    // 2. Verificar herencias inválidas (No se puede heredar de Int, Bool, String, SELF_TYPE)
    for (size_t i = 0; i < user_classes.size(); i++) {
        Class_ c = user_classes[i];
        Symbol parent = c->get_parent();
        if (parent == Int || parent == Bool || parent == Str || parent == SELF_TYPE) {
            semant_error(c) << "Class " << c->get_name() << " cannot inherit class " << parent << ".\n";
        }
    }
    if (errors()) return;

    // 3. Verificar que las clases padre existan y detectar ciclos de herencia
    for (size_t i = 0; i < user_classes.size(); i++) {
        Class_ c = user_classes[i];
        Symbol curr_name = c->get_name();
        Symbol parent_name = c->get_parent();
        
        std::set<Symbol> visited;
        visited.insert(curr_name);
        
        while (parent_name != No_class && parent_name != Object) {
            if (class_map.find(parent_name) == class_map.end()) {
                semant_error(c) << "Class " << curr_name << " inherits from an undefined class " << parent_name << ".\n";
                break;
            }
            if (visited.find(parent_name) != visited.end()) {
                semant_error(c) << "Class " << curr_name << ", or an ancestor of " << curr_name << ", is involved in an inheritance cycle.\n";
                break;
            }
            visited.insert(parent_name);
            parent_name = class_map[parent_name]->get_parent();
        }
    }

    // 4. Verificar existencia de la clase Main
    if (class_map.find(Main) == class_map.end()) {
        semant_error() << "Class Main is not defined.\n";
    }
}

void ClassTable::install_basic_classes() {
    curr_filename = "<basic class>";
    Symbol filename = stringtable.add_string("<basic class>");

    Class_ Object_class = class_(Object, No_class,
        append_Features(append_Features(
            single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
            single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
            single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
        filename);

    Class_ IO_class = class_(IO, Object,
        append_Features(append_Features(append_Features(
            single_Features(method(out_string, single_Formals(formal(arg, Str)), SELF_TYPE, no_expr())),
            single_Features(method(out_int, single_Formals(formal(arg, Int)), SELF_TYPE, no_expr()))),
            single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
            single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
        filename);

    Class_ Int_class = class_(Int, Object, single_Features(attr(val, prim_slot, no_expr())), filename);
    Class_ Bool_class = class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())), filename);
    
    Class_ Str_class = class_(Str, Object,
        append_Features(append_Features(append_Features(append_Features(
            single_Features(attr(val, Int, no_expr())),
            single_Features(attr(str_field, prim_slot, no_expr()))),
            single_Features(method(length, nil_Formals(), Int, no_expr()))),
            single_Features(method(concat, single_Formals(formal(arg, Str)), Str, no_expr()))),
            single_Features(method(substr, append_Formals(single_Formals(formal(arg, Int)), single_Formals(formal(arg2, Int))), Str, no_expr()))),
        filename);

    class_map[Object] = Object_class;
    class_map[IO] = IO_class;
    class_map[Int] = Int_class;
    class_map[Bool] = Bool_class;
    class_map[Str] = Str_class;
}

ostream& ClassTable::semant_error(Class_ c) {                                                             
    return semant_error(c->get_filename(), c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t) {
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error() {                                                 
    semant_errors++;                            
    return error_stream;
} 

// ====================================================================================
// Métodos auxiliares de la tabla de clases
// ====================================================================================

bool ClassTable::class_exists(Symbol type) {
    return class_map.find(type) != class_map.end();
}

bool ClassTable::type_defined(Symbol type) {
    return type == SELF_TYPE || class_exists(type);
}

// Devuelve [clase, padre, abuelo, ..., Object]
std::vector<Symbol> ClassTable::ancestors(Symbol class_name) {
    std::vector<Symbol> result;
    std::set<Symbol> seen;
    Symbol c = class_name;
    while (c != No_class && class_exists(c) && seen.find(c) == seen.end()) {
        result.push_back(c);
        seen.insert(c);
        c = class_map[c]->get_parent();
    }
    return result;
}

// type1 <= type2 (type1 conforma con type2), teniendo en cuenta SELF_TYPE
bool ClassTable::is_subtype(Symbol type1, Symbol type2, class__class* curr_class) {
    if (type1 == No_type) return true;        // no_expr / errores previos
    if (type1 == SELF_TYPE && type2 == SELF_TYPE) return true;
    if (type2 == SELF_TYPE) return false;
    if (type1 == SELF_TYPE) type1 = curr_class->get_name();

    // Tipos no definidos: el error ya se reportó en otro lugar, evitar cascadas
    if (!class_exists(type1) || !class_exists(type2)) return true;

    std::vector<Symbol> anc = ancestors(type1);
    for (size_t i = 0; i < anc.size(); i++)
        if (anc[i] == type2) return true;
    return false;
}

Symbol ClassTable::least_common_ancestor(Symbol type1, Symbol type2, class__class* curr_class) {
    if (type1 == No_type) return type2;
    if (type2 == No_type) return type1;
    if (type1 == SELF_TYPE && type2 == SELF_TYPE) return SELF_TYPE;
    if (type1 == SELF_TYPE) type1 = curr_class->get_name();
    if (type2 == SELF_TYPE) type2 = curr_class->get_name();

    std::vector<Symbol> anc1 = ancestors(type1);
    std::set<Symbol> set1(anc1.begin(), anc1.end());
    std::vector<Symbol> anc2 = ancestors(type2);
    for (size_t i = 0; i < anc2.size(); i++)
        if (set1.find(anc2[i]) != set1.end()) return anc2[i];
    return Object;
}

// Busca un método en la clase y sus ancestros
MethodSignature* ClassTable::lookup_method(Symbol class_name, Symbol method_name) {
    std::vector<Symbol> anc = ancestors(class_name);
    for (size_t i = 0; i < anc.size(); i++) {
        std::map<Symbol, std::map<Symbol, MethodSignature> >::iterator ct = method_table.find(anc[i]);
        if (ct == method_table.end()) continue;
        std::map<Symbol, MethodSignature>::iterator mt = ct->second.find(method_name);
        if (mt != ct->second.end()) return &(mt->second);
    }
    return NULL;
}

// Busca un atributo en la clase y sus ancestros. Devuelve su tipo o NULL.
Symbol ClassTable::lookup_attr(Symbol class_name, Symbol attr_name) {
    std::vector<Symbol> anc = ancestors(class_name);
    for (size_t i = 0; i < anc.size(); i++) {
        std::map<Symbol, std::map<Symbol, Symbol> >::iterator ct = attr_table.find(anc[i]);
        if (ct == attr_table.end()) continue;
        std::map<Symbol, Symbol>::iterator at = ct->second.find(attr_name);
        if (at != ct->second.end()) return at->second;
    }
    return NULL;
}

// FASE 2: recolectar firmas de métodos y atributos de todas las clases
void ClassTable::gather_all_features() {
    Symbol basics[] = { Object, IO, Int, Bool, Str };
    for (int i = 0; i < 5; i++)
        class_map[basics[i]]->gather_features(this);
    for (size_t i = 0; i < user_classes.size(); i++)
        user_classes[i]->gather_features(this);

    // La clase Main debe tener un método main
    if (class_exists(Main) && lookup_method(Main, main_meth) == NULL) {
        semant_error(class_map[Main]) << "No 'main' method in class Main.\n";
    }
}

// FASE 3: chequeo de tipos de todas las clases del usuario
void ClassTable::type_check_all() {
    for (size_t i = 0; i < user_classes.size(); i++)
        user_classes[i]->type_check(this);
}

// ====================================================================================
// Punto de entrada del analizador semántico
// ====================================================================================
void program_class::semant() {
    initialize_constants();
    ClassTable *classtable = new ClassTable(classes);

    if (classtable->errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
    
    classtable->gather_all_features();
    classtable->type_check_all();

    if (classtable->errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}

// ====================================================================================
// Getters
// ====================================================================================
Symbol class__class::get_name() { return name; }
Symbol class__class::get_parent() { return parent; }
Features class__class::get_features() { return features; }

Symbol formal_class::get_name() { return name; }
Symbol formal_class::get_type() { return type_decl; }

// ====================================================================================
// Recolección de features (Fase 2)
// ====================================================================================
void class__class::gather_features(ClassTable* ct) {
    // Asegurar que la clase tenga entrada en las tablas aunque no tenga features
    ct->method_table[name];
    ct->attr_table[name];
    for (int i = features->first(); features->more(i); i = features->next(i))
        features->nth(i)->gather_features(ct, this);
}

void method_class::gather_features(ClassTable* ct, class__class* c) {
    std::map<Symbol, MethodSignature>& methods = ct->method_table[c->get_name()];
    if (methods.find(name) != methods.end()) {
        ct->semant_error(c->get_filename(), this) << "Method " << name << " is multiply defined.\n";
        return;
    }
    MethodSignature sig;
    sig.return_type = return_type;
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        sig.arg_types.push_back(formals->nth(i)->get_type());
        sig.arg_names.push_back(formals->nth(i)->get_name());
    }
    methods[name] = sig;
}

void attr_class::gather_features(ClassTable* ct, class__class* c) {
    if (name == self) {
        ct->semant_error(c->get_filename(), this) << "'self' cannot be the name of an attribute.\n";
        return;
    }
    std::map<Symbol, Symbol>& attrs = ct->attr_table[c->get_name()];
    if (attrs.find(name) != attrs.end()) {
        ct->semant_error(c->get_filename(), this) << "Attribute " << name << " is multiply defined in class.\n";
        return;
    }
    attrs[name] = type_decl;
}

// ====================================================================================
// Chequeo de tipos de clases y features (Fase 3)
// ====================================================================================
void class__class::type_check(ClassTable* ct) {
    SymbolTable<Symbol, Symbol> *env = new SymbolTable<Symbol, Symbol>();
    env->enterscope();
    env->addid(self, new Symbol(SELF_TYPE));

    // Atributos visibles: los de los ancestros (desde Object) y los propios
    std::vector<Symbol> anc = ct->ancestors(name);
    for (int i = (int)anc.size() - 1; i >= 0; i--) {
        std::map<Symbol, Symbol>& attrs = ct->attr_table[anc[i]];
        for (std::map<Symbol, Symbol>::iterator it = attrs.begin(); it != attrs.end(); ++it)
            env->addid(it->first, new Symbol(it->second));
    }

    for (int i = features->first(); features->more(i); i = features->next(i))
        features->nth(i)->type_check(ct, env, this);

    env->exitscope();
}

void method_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol filename = c->get_filename();

    // Verificar la redefinición respecto al método heredado (si existe)
    MethodSignature* orig = ct->lookup_method(c->get_parent(), name);
    if (orig != NULL) {
        int n = 0;
        for (int i = formals->first(); formals->more(i); i = formals->next(i)) n++;
        if (n != (int)orig->arg_types.size()) {
            ct->semant_error(filename, this) << "Incompatible number of formal parameters in redefined method " << name << ".\n";
        } else {
            int k = 0;
            for (int i = formals->first(); formals->more(i); i = formals->next(i), k++) {
                Symbol t = formals->nth(i)->get_type();
                if (t != orig->arg_types[k]) {
                    ct->semant_error(filename, this) << "In redefined method " << name << ", parameter type " << t
                        << " is different from original type " << orig->arg_types[k] << "\n";
                    break;
                }
            }
        }
        if (return_type != orig->return_type) {
            ct->semant_error(filename, this) << "In redefined method " << name << ", return type " << return_type
                << " is different from original return type " << orig->return_type << ".\n";
        }
    }

    env->enterscope();
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        Formal f = formals->nth(i);
        Symbol fname = f->get_name();
        Symbol ftype = f->get_type();
        bool ok = true;
        if (fname == self) {
            ct->semant_error(filename, f) << "'self' cannot be the name of a formal parameter.\n";
            ok = false;
        }
        if (ftype == SELF_TYPE) {
            ct->semant_error(filename, f) << "Formal parameter " << fname << " cannot have type SELF_TYPE.\n";
        } else if (!ct->class_exists(ftype)) {
            ct->semant_error(filename, f) << "Class " << ftype << " of formal parameter " << fname << " is undefined.\n";
        }
        if (ok) {
            if (env->probe(fname) != NULL) {
                ct->semant_error(filename, f) << "Formal parameter " << fname << " is multiply defined.\n";
            } else {
                env->addid(fname, new Symbol(ftype));
            }
        }
    }

    bool ret_ok = ct->type_defined(return_type);
    if (!ret_ok) {
        ct->semant_error(filename, this) << "Undefined return type " << return_type << " in method " << name << ".\n";
    }

    Symbol body_type = expr->type_check(ct, env, c);
    if (ret_ok && !ct->is_subtype(body_type, return_type, c)) {
        ct->semant_error(filename, this) << "Inferred return type " << body_type << " of method " << name
            << " does not conform to declared return type " << return_type << ".\n";
    }
    env->exitscope();
}

void attr_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol filename = c->get_filename();
    if (name == self) {
        // El error ya se reportó en la fase de recolección; solo chequear la inicialización
        init->type_check(ct, env, c);
        return;
    }

    if (ct->lookup_attr(c->get_parent(), name) != NULL) {
        ct->semant_error(filename, this) << "Attribute " << name << " is an attribute of an inherited class.\n";
    }

    bool type_ok = ct->type_defined(type_decl);
    if (!type_ok) {
        ct->semant_error(filename, this) << "Class " << type_decl << " of attribute " << name << " is undefined.\n";
    }

    Symbol init_type = init->type_check(ct, env, c);
    if (type_ok && init_type != No_type && !ct->is_subtype(init_type, type_decl, c)) {
        ct->semant_error(filename, this) << "Inferred type " << init_type << " of initialization of attribute " << name
            << " does not conform to declared type " << type_decl << ".\n";
    }
}

// ====================================================================================
// Chequeo de tipos de expresiones
// ====================================================================================

Symbol int_const_class::type_check(ClassTableP ct, SymbolTable<Symbol, Symbol> *env, class__class* curr_class) {
    type = Int;
    return type;
}

Symbol bool_const_class::type_check(ClassTableP ct, SymbolTable<Symbol, Symbol> *env, class__class* curr_class) {
    type = Bool;
    return type;
}

Symbol string_const_class::type_check(ClassTableP ct, SymbolTable<Symbol, Symbol> *env, class__class* curr_class) {
    type = Str;
    return type;
}

Symbol no_expr_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    type = No_type;
    return type;
}

Symbol object_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    if (name == self) {
        type = SELF_TYPE;
        return type;
    }
    Symbol* t = env->lookup(name);
    if (t == NULL) {
        ct->semant_error(c->get_filename(), this) << "Undeclared identifier " << name << ".\n";
        type = Object;
    } else {
        type = *t;
    }
    return type;
}

Symbol assign_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol expr_type = expr->type_check(ct, env, c);
    if (name == self) {
        ct->semant_error(c->get_filename(), this) << "Cannot assign to 'self'.\n";
        type = expr_type;
        return type;
    }
    Symbol* decl = env->lookup(name);
    if (decl == NULL) {
        ct->semant_error(c->get_filename(), this) << "Assignment to undeclared variable " << name << ".\n";
    } else if (!ct->is_subtype(expr_type, *decl, c)) {
        ct->semant_error(c->get_filename(), this) << "Type " << expr_type << " of assigned expression does not conform to declared type "
            << *decl << " of identifier " << name << ".\n";
    }
    type = expr_type;
    return type;
}

// Chequea los argumentos actuales contra la firma del método
static void check_actuals(ClassTable* ct, class__class* c, tree_node* node, Symbol meth_name,
                          MethodSignature* sig, std::vector<Symbol>& actual_types) {
    if (sig->arg_types.size() != actual_types.size()) {
        ct->semant_error(c->get_filename(), node) << "Method " << meth_name << " called with wrong number of arguments.\n";
        return;
    }
    for (size_t i = 0; i < actual_types.size(); i++) {
        if (!ct->is_subtype(actual_types[i], sig->arg_types[i], c)) {
            ct->semant_error(c->get_filename(), node) << "In call of method " << meth_name << ", type " << actual_types[i]
                << " of parameter " << sig->arg_names[i] << " does not conform to declared type " << sig->arg_types[i] << ".\n";
        }
    }
}

Symbol dispatch_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol t0 = expr->type_check(ct, env, c);
    std::vector<Symbol> actual_types;
    for (int i = actual->first(); actual->more(i); i = actual->next(i))
        actual_types.push_back(actual->nth(i)->type_check(ct, env, c));

    Symbol lookup_class = (t0 == SELF_TYPE) ? c->get_name() : t0;
    MethodSignature* sig = ct->lookup_method(lookup_class, name);
    if (sig == NULL) {
        ct->semant_error(c->get_filename(), this) << "Dispatch to undefined method " << name << ".\n";
        type = Object;
        return type;
    }
    check_actuals(ct, c, this, name, sig, actual_types);
    type = (sig->return_type == SELF_TYPE) ? t0 : sig->return_type;
    return type;
}

Symbol static_dispatch_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol t0 = expr->type_check(ct, env, c);
    std::vector<Symbol> actual_types;
    for (int i = actual->first(); actual->more(i); i = actual->next(i))
        actual_types.push_back(actual->nth(i)->type_check(ct, env, c));

    if (type_name == SELF_TYPE) {
        ct->semant_error(c->get_filename(), this) << "Static dispatch to SELF_TYPE.\n";
        type = Object;
        return type;
    }
    if (!ct->class_exists(type_name)) {
        ct->semant_error(c->get_filename(), this) << "Static dispatch to undefined class " << type_name << ".\n";
        type = Object;
        return type;
    }
    if (!ct->is_subtype(t0, type_name, c)) {
        ct->semant_error(c->get_filename(), this) << "Expression type " << t0
            << " does not conform to declared static dispatch type " << type_name << ".\n";
        type = Object;
        return type;
    }
    MethodSignature* sig = ct->lookup_method(type_name, name);
    if (sig == NULL) {
        ct->semant_error(c->get_filename(), this) << "Static dispatch to undefined method " << name << ".\n";
        type = Object;
        return type;
    }
    check_actuals(ct, c, this, name, sig, actual_types);
    type = (sig->return_type == SELF_TYPE) ? t0 : sig->return_type;
    return type;
}

Symbol cond_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    if (pred->type_check(ct, env, c) != Bool)
        ct->semant_error(c->get_filename(), this) << "Predicate of 'if' does not have type Bool.\n";
    Symbol t1 = then_exp->type_check(ct, env, c);
    Symbol t2 = else_exp->type_check(ct, env, c);
    type = ct->least_common_ancestor(t1, t2, c);
    return type;
}

Symbol loop_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    if (pred->type_check(ct, env, c) != Bool)
        ct->semant_error(c->get_filename(), this) << "Loop condition does not have type Bool.\n";
    body->type_check(ct, env, c);
    type = Object;
    return type;
}

Symbol branch_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    env->enterscope();
    if (name == self) {
        ct->semant_error(c->get_filename(), this) << "'self' bound in 'case'.\n";
    }
    if (type_decl == SELF_TYPE) {
        ct->semant_error(c->get_filename(), this) << "Identifier " << name << " declared with type SELF_TYPE in case branch.\n";
    } else if (!ct->class_exists(type_decl)) {
        ct->semant_error(c->get_filename(), this) << "Class " << type_decl << " of case branch is undefined.\n";
    }
    if (name != self)
        env->addid(name, new Symbol(type_decl));
    Symbol t = expr->type_check(ct, env, c);
    env->exitscope();
    return t;
}

Symbol typcase_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    expr->type_check(ct, env, c);
    std::set<Symbol> seen;
    Symbol result = NULL;
    for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
        Case br = cases->nth(i);
        Symbol decl = br->get_type_decl();
        if (seen.find(decl) != seen.end()) {
            ct->semant_error(c->get_filename(), br) << "Duplicate branch " << decl << " in case statement.\n";
        }
        seen.insert(decl);
        Symbol t = br->type_check(ct, env, c);
        result = (result == NULL) ? t : ct->least_common_ancestor(result, t, c);
    }
    type = (result == NULL) ? Object : result;
    return type;
}

Symbol block_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol t = Object;
    for (int i = body->first(); body->more(i); i = body->next(i))
        t = body->nth(i)->type_check(ct, env, c);
    type = t;
    return type;
}

Symbol let_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol filename = c->get_filename();
    if (identifier == self) {
        ct->semant_error(filename, this) << "'self' cannot be bound in a 'let' expression.\n";
    }
    bool type_ok = ct->type_defined(type_decl);
    if (!type_ok) {
        ct->semant_error(filename, this) << "Class " << type_decl << " of let-bound identifier " << identifier << " is undefined.\n";
    }

    // La inicialización se evalúa en el entorno exterior
    Symbol init_type = init->type_check(ct, env, c);
    if (type_ok && init_type != No_type && !ct->is_subtype(init_type, type_decl, c)) {
        ct->semant_error(filename, this) << "Inferred type " << init_type << " of initialization of " << identifier
            << " does not conform to identifier's declared type " << type_decl << ".\n";
    }

    env->enterscope();
    if (identifier != self)
        env->addid(identifier, new Symbol(type_decl));
    type = body->type_check(ct, env, c);
    env->exitscope();
    return type;
}

// Operaciones aritméticas binarias (+, -, *, /)
static Symbol check_arith(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c,
                          tree_node* node, Expression e1, Expression e2, const char* op) {
    Symbol t1 = e1->type_check(ct, env, c);
    Symbol t2 = e2->type_check(ct, env, c);
    if (t1 != Int || t2 != Int)
        ct->semant_error(c->get_filename(), node) << "non-Int arguments: " << t1 << " " << op << " " << t2 << "\n";
    return Int;
}

Symbol plus_class::type_check(ClassTableP ct, SymbolTable<Symbol, Symbol> *env, class__class* c) {
    return type = check_arith(ct, env, c, this, e1, e2, "+");
}
Symbol sub_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    return type = check_arith(ct, env, c, this, e1, e2, "-");
}
Symbol mul_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    return type = check_arith(ct, env, c, this, e1, e2, "*");
}
Symbol divide_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    return type = check_arith(ct, env, c, this, e1, e2, "/");
}

Symbol neg_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol t = e1->type_check(ct, env, c);
    if (t != Int)
        ct->semant_error(c->get_filename(), this) << "Argument of '~' has type " << t << " instead of Int.\n";
    type = Int;
    return type;
}

// Comparaciones (<, <=)
static Symbol check_compare(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c,
                            tree_node* node, Expression e1, Expression e2, const char* op) {
    Symbol t1 = e1->type_check(ct, env, c);
    Symbol t2 = e2->type_check(ct, env, c);
    if (t1 != Int || t2 != Int)
        ct->semant_error(c->get_filename(), node) << "non-Int arguments: " << t1 << " " << op << " " << t2 << "\n";
    return Bool;
}

Symbol lt_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    return type = check_compare(ct, env, c, this, e1, e2, "<");
}
Symbol leq_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    return type = check_compare(ct, env, c, this, e1, e2, "<=");
}

Symbol eq_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol t1 = e1->type_check(ct, env, c);
    Symbol t2 = e2->type_check(ct, env, c);
    bool basic1 = (t1 == Int || t1 == Str || t1 == Bool);
    bool basic2 = (t2 == Int || t2 == Str || t2 == Bool);
    if ((basic1 || basic2) && t1 != t2)
        ct->semant_error(c->get_filename(), this) << "Illegal comparison with a basic type.\n";
    type = Bool;
    return type;
}

Symbol comp_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    Symbol t = e1->type_check(ct, env, c);
    if (t != Bool)
        ct->semant_error(c->get_filename(), this) << "Argument of 'not' has type " << t << " instead of Bool.\n";
    type = Bool;
    return type;
}

Symbol new__class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    if (type_name != SELF_TYPE && !ct->class_exists(type_name)) {
        ct->semant_error(c->get_filename(), this) << "'new' used with undefined class " << type_name << ".\n";
        type = Object;
    } else {
        type = type_name;
    }
    return type;
}

Symbol isvoid_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) {
    e1->type_check(ct, env, c);
    type = Bool;
    return type;
}
