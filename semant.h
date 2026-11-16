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
};

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;

public:
  // Grafo de herencia
  std::map<Symbol, Class_> class_map;
  
  // Tabla global de metodos: map<NombreClase, map<NombreMetodo, Firma>>
  std::map<Symbol, std::map<Symbol, MethodSignature> > method_table;

  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);

  // Metodos auxiliares
  bool check_cycles();
  bool is_subtype(Symbol type1, Symbol type2, class__class* curr_class);
  Symbol least_common_ancestor(Symbol type1, Symbol type2, class__class* curr_class);
  MethodSignature* lookup_method(Symbol class_name, Symbol method_name);
};

#endif
