// RUN: not veir-opt %s 2>&1 | filecheck %s

%result = "pancake.const"() <{value = 0 : i8}> ({}) : () -> i8
// CHECK: pancake.const: Expected 0 regions
