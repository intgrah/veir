// RUN: not veir-opt %s 2>&1 | filecheck %s
"pancake.op"() <{operator = "add"}> : () -> ()
// CHECK: pancake.op: Expected 1 result(s)
