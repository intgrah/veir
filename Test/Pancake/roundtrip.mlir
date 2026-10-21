// RUN: VEIR_ROUNDTRIP
// RUN: veir-opt -p=dce --print-op-generic %s | filecheck %s

"builtin.module"() ({
  "pancake.function"() <{name = "main", inline = false, exported = true, params = [], return_shape = 1 : i64}> ({
    // CHECK: "pancake.function"() <{"exported" = true, "inline" = false, "name" = "main", "params" = [], "return_shape" = 1 : i64}>
    %addr = "pancake.base_addr"() : () -> i64
    // CHECK: %[[ADDR:.*]] = "pancake.base_addr"() : () -> i64
    %one = "pancake.const"() <{value = 1 : i64}> : () -> i64
    // CHECK: %[[ONE:.*]] = "pancake.const"() <{"value" = 1 : i64}> : () -> i64
    "pancake.assign"(%one) <{name = "counter", kind = "local"}> : (i64) -> ()
    // CHECK: "pancake.assign"(%[[ONE]]) <{"kind" = "local", "name" = "counter"}>
    %value = "pancake.load"(%addr) <{shape = 1 : i64}> : (i64) -> i64
    // CHECK: %[[VALUE:.*]] = "pancake.load"(%[[ADDR]]) <{"shape" = 1 : i64}>
    "pancake.ite"(%one) ({
      "pancake.store"(%addr, %value) : (i64, i64) -> ()
      // CHECK: "pancake.ite"(%[[ONE]]) ({
      // CHECK: "pancake.store"(%[[ADDR]], %[[VALUE]])
    }, {
      "pancake.annot"() <{tag = "source", text = "else branch"}> : () -> ()
      // CHECK: "pancake.annot"() <{"tag" = "source", "text" = "else branch"}>
    }) : (i64) -> ()
    "pancake.ext_call"(%addr, %one, %addr, %one) <{function = "write"}> : (i64, i64, i64, i64) -> ()
    // CHECK: "pancake.ext_call"(%[[ADDR]], %[[ONE]], %[[ADDR]], %[[ONE]]) <{"function" = "write"}>
    "pancake.return"(%one) : (i64) -> ()
    // CHECK: "pancake.return"(%[[ONE]]) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
