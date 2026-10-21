// RUN: not veir-opt %s 2>&1 | filecheck %s

"pancake.function"() <{name = "main", inline = false, exported = false, params = [], return_shape = 1 : i64}> ({
  %value = "pancake.const"() <{value = 0 : i64}> : () -> i64
  "pancake.return"(%value) : (i64) -> ()
  "pancake.tick"() : () -> ()
}) : () -> ()

// CHECK: Expected a terminator to be the last operation of its block
