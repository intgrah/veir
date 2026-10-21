// RUN: not veir-opt %s 2>&1 | filecheck %s

%result = "pancake.const"() <{value = 1 : i32}> : () -> i64
// CHECK: pancake.const: constant property type must match the result word type
