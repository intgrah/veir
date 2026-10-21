// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %one = "pancake.const"() <{value = 1 : i64}> : () -> i64
  %cmp = "pancake.cmp"(%one, %one) <{operator = "unsigned_lt"}> : (i64, i64) -> i64
}) : () -> ()

// CHECK: pancake.cmp:
// CHECK-SAME: expected one of
