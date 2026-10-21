// RUN: not veir-interpret %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %poison = "llvm.mlir.poison"() : () -> i8
    %result = "pancake.op"(%poison) <{operator = "add"}> : (i8) -> i8
    "func.return"(%result) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: failed to interpret operation
// CHECK: "pancake.op"
