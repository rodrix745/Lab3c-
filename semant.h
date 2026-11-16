#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include <map>
#include <vector>
#include <set>
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// Estructura para guardar la firma de los metodos
struct MethodSignature {
    Symbol return_type;
    std::vector<Symbol> arg_types;
    std::vector<Symbol> arg_names;
};

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;

public:
  // Grafo de herencia
  std::map<Symbol, Class_> class_map;

  // Clases definidas por el usuario, en el orden del programa
  std::vector<Class_> user_classes;
  
  // Tabla global de metodos: map<NombreClase, map<NombreMetodo, Firma>>
  std::map<Symbol, std::map<Symbol, MethodSignature> > method_table;

  // Tabla global de atributos: map<NombreClase, map<NombreAtributo, Tipo>>
  std::map<Symbol, std::map<Symbol, Symbol> > attr_table;

  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);

  // Metodos auxiliares
  bool class_exists(Symbol type);
  bool type_defined(Symbol type);   // como class_exists, pero acepta SELF_TYPE
  bool is_subtype(Symbol type1, Symbol type2, class__class* curr_class);
  Symbol least_common_ancestor(Symbol type1, Symbol type2, class__class* curr_class);
  MethodSignature* lookup_method(Symbol class_name, Symbol method_name);
  Symbol lookup_attr(Symbol class_name, Symbol attr_name);   // busca en ancestros
  std::vector<Symbol> ancestors(Symbol class_name);          // [clase, padre, ..., Object]

  // Fases 2 y 3
  void gather_all_features();
  void type_check_all();
};

#endif
