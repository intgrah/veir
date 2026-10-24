// RUN: not veir-opt %s 2>&1 | filecheck %s
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^entry:
    %zero = "pancake.op"() [^side] <{operator = "add"}> : () -> i8
    "func.return"() : () -> ()
  ^side:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
// CHECK: pancake.op: Expected 0 successors
