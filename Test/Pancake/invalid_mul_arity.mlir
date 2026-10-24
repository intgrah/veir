// RUN: not veir-opt %s 2>&1 | filecheck %s

%result = "pancake.panop"() <{operator = "mul"}> : () -> i8
// CHECK: pancake.panop: Expected 2 operand(s)
