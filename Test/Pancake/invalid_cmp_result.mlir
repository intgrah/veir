// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %one = "pancake.const"() <{value = 1 : i32}> : () -> i32
  %result = "pancake.cmp"(%one, %one) <{operator = "equal"}> : (i32, i32) -> i1
}) : () -> ()
// CHECK: pancake.cmp: operand types must match the result word type
