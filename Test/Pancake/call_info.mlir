// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "pancake.function"() <{name = "calls", inline = false, exported = false, params = [], return_shape = 1 : i64}> ({
    "pancake.call"() <{name = "callee", info = {destination = unit, handler = unit}}> : () -> ()
    // CHECK: "pancake.call"() <{"info" = {destination, handler}, "name" = "callee"}>
    "pancake.call"() <{name = "callee", info = {destination = {kind = "local", name = "result"}, handler = {exception = "error", name = "caught"}}}> ({
      "pancake.annot"() <{tag = "handler", text = "caught"}> : () -> ()
    }) : () -> ()
    // CHECK: "pancake.call"() <{"info" = {"destination" = {"kind" = "local", "name" = "result"}, "handler" = {"exception" = "error", "name" = "caught"}}, "name" = "callee"}>
    "pancake.call"() <{name = "callee", info = unit}> : () -> ()
    // CHECK: "pancake.call"() <{info, "name" = "callee"}>
  }) : () -> ()
}) : () -> ()
