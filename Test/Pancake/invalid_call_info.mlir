// RUN: not veir-opt %s 2>&1 | filecheck %s

"pancake.call"() <{name = "callee", info = {destination = unit}}> : () -> ()

// CHECK: pancake.call:
// CHECK-SAME: missing 'handler'
