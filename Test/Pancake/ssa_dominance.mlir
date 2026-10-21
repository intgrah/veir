// RUN: not veir-opt %s 2>&1 | filecheck %s

"pancake.function"() <{name = "main", inline = false, exported = false, params = [], return_shape = 1 : i64}> ({
  "pancake.assign"(%value) <{name = "x", kind = "local"}> : (i64) -> ()
  %value = "pancake.const"() <{value = 0 : i64}> : () -> i64
}) : () -> ()

// CHECK: operand #0 does not dominate this use
