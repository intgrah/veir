// RUN: not veir-opt %s 2>&1 | filecheck %s
%result = "pancake.op"() <{operator = "add"}> : () -> f32
// CHECK: pancake.op: expected a signless integer result
