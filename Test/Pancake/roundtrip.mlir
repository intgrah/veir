// RUN: VEIR_ROUNDTRIP
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %one = "pancake.const"() <{value = 1 : i8}> : () -> i8
    // CHECK: "pancake.const"() <{"value" = 1 : i8}> : () -> i8
    %sum = "pancake.op"(%one, %one, %one) <{operator = "add"}> : (i8, i8, i8) -> i8
    // CHECK: "pancake.op"({{.*}}) <{"operator" = "add"}> : (i8, i8, i8) -> i8
    %mul = "pancake.panop"(%sum, %one) <{operator = "mul"}> : (i8, i8) -> i8
    // CHECK: "pancake.panop"({{.*}}) <{"operator" = "mul"}> : (i8, i8) -> i8
    %cmp = "pancake.cmp"(%sum, %mul) <{operator = "notTest"}> : (i8, i8) -> i8
    // CHECK: "pancake.cmp"({{.*}}) <{"operator" = "notTest"}> : (i8, i8) -> i8
    "func.return"(%cmp) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
