// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %addr = "pancake.base_addr"() : () -> i64
  %value = "pancake.load"(%addr) <{shape = [1 : i64, 2 : i64]}> : (i64) -> i64
}) : () -> ()

// CHECK: pancake.load:
// CHECK-SAME: expected shape one
