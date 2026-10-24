// RUN: not veir-opt %s 2>&1 | filecheck %s
%result = "pancake.op"() <{operator = "add"}> : () -> si8
// CHECK: pancake.op: expected a nonzero-width signless integer result
