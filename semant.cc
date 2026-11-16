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

// Mapa global para guardar las clases y poder acceder a ellas fácilmente
std::map<Symbol, Class_> class_map;

ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {
    install_basic_classes();

    // 1. Recolectar clases definidas por el usuario
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
        }
    }

    // Si hay errores en las definiciones base, detenerse
    if (errors()) return;

    // 2. Verificar herencias inválidas (No se puede heredar de Int, Bool, String, SELF_TYPE)
    for (std::map<Symbol, Class_>::iterator it = class_map.begin(); it != class_map.end(); ++it) {
        Symbol parent = it->second->get_parent();
        if (parent == Int || parent == Bool || parent == Str || parent == SELF_TYPE) {
            semant_error(it->second) << "Class " << it->first << " cannot inherit class " << parent << ".\n";
        }
    }

    // 3. Verificar que las clases padre existan y detectar ciclos de herencia
    for (std::map<Symbol, Class_>::iterator it = class_map.begin(); it != class_map.end(); ++it) {
        Symbol curr_name = it->first;
        Symbol parent_name = it->second->get_parent();
        
        std::set<Symbol> visited;
        visited.insert(curr_name);
        
        while (parent_name != No_class && parent_name != Object) {
            if (class_map.find(parent_name) == class_map.end()) {
                semant_error(it->second) << "Class " << curr_name << " inherits from an undefined class " << parent_name << ".\n";
                break;
            }
            if (visited.find(parent_name) != visited.end()) {
                semant_error(it->second) << "Class " << curr_name << ", or an ancestor of " << curr_name << ", is involved in an inheritance cycle.\n";
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

// Punto de entrada del analizador semántico
void program_class::semant() {
    initialize_constants();
    ClassTable *classtable = new ClassTable(classes);

    if (classtable->errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
    
    // AQUI EMPEZARÁ TU FASE 2 Y 3 (Recolección de firmas y type checking)
    // Se recorren las clases para chequear los tipos.
}

// ====================================================================================
// EJEMPLO DE TYPE_CHECK (Completa los demás guiándote por este)
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

Symbol plus_class::type_check(ClassTableP ct, SymbolTable<Symbol, Symbol> *env, class__class* curr_class) {
    Symbol t1 = e1->type_check(ct, env, curr_class);
    Symbol t2 = e2->type_check(ct, env, curr_class);
    if (t1 != Int || t2 != Int) {
        ct->semant_error(curr_class->get_filename(), this) << "non-Int arguments: " << t1 << " + " << t2 << "\n";
        type = Object;
    } else {
        type = Int;
    }
    return type;
}
// ====================================================================================
// IMPLEMENTACIONES FALTANTES PARA QUE COMPILE EL LINKER (Stubs)
// Rellena la lógica de estos métodos más adelante.
// ====================================================================================

// --- Getters para clases y parámetros ---
Symbol class__class::get_name() { return name; }
Symbol class__class::get_parent() { return parent; }
Features class__class::get_features() { return features; }

Symbol formal_class::get_name() { return name; }
Symbol formal_class::get_type() { return type_decl; }

// --- Funciones de recorrido de clases (Fase 2 y 3) ---
void class__class::gather_features(ClassTable* ct) { }
void class__class::type_check(ClassTable* ct) { }

void method_class::gather_features(ClassTable* ct, class__class* c) { }
void method_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { }

void attr_class::gather_features(ClassTable* ct, class__class* c) { }
void attr_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { }

// --- Funciones Type Check de las Expresiones ---
Symbol object_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol no_expr_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol isvoid_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Bool; }
Symbol new__class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol comp_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Bool; }
Symbol leq_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Bool; }
Symbol eq_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Bool; }
Symbol lt_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Bool; }
Symbol neg_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Int; }
Symbol divide_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Int; }
Symbol mul_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Int; }
Symbol sub_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Int; }
Symbol let_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol block_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol typcase_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol loop_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol cond_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol dispatch_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol static_dispatch_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }
Symbol assign_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return type = Object; }

Symbol branch_class::type_check(ClassTable* ct, SymbolTable<Symbol, Symbol>* env, class__class* c) { return Object; }