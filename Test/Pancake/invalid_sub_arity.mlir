// RUN: not veir-opt %s 2>&1 | filecheck %s

%result = "pancake.op"() <{operator = "sub"}> : () -> i8
// CHECK: pancake.op: Expected 2 operand(s)
