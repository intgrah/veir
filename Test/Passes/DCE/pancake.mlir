// RUN: veir-opt %s -p=dce | filecheck %s
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %one = "pancake.const"() <{value = 1 : i8}> : () -> i8
    %sum = "pancake.op"(%one, %one) <{operator = "add"}> : (i8, i8) -> i8
    %mul = "pancake.panop"(%one, %sum) <{operator = "mul"}> : (i8, i8) -> i8
    %cmp = "pancake.cmp"(%mul, %sum) <{operator = "equal"}> : (i8, i8) -> i8
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
// CHECK: func.func @main
// CHECK-NOT: pancake.
// CHECK: return
