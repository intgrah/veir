// RUN: not veir-opt %s 2>&1 | filecheck %s
%result = "pancake.op"() <{operator = "mul"}> : () -> i8
// CHECK: pancake.op: unknown operator
