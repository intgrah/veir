// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8)}> ({
    %one = "pancake.const"() <{value = 1 : i8}> : () -> i8
    %two = "pancake.const"() <{value = 2 : i8}> : () -> i8
    %minus = "pancake.const"() <{value = -1 : i8}> : () -> i8
    %high = "pancake.const"() <{value = -128 : i8}> : () -> i8
    %zero = "pancake.op"() <{operator = "add"}> : () -> i8
    %all = "pancake.op"() <{operator = "and"}> : () -> i8
    %wrap = "pancake.op"(%minus, %one) <{operator = "add"}> : (i8, i8) -> i8
    %sub = "pancake.op"(%zero, %one) <{operator = "sub"}> : (i8, i8) -> i8
    %xor = "pancake.op"(%minus, %one, %high) <{operator = "xor"}> : (i8, i8, i8) -> i8
    %or = "pancake.op"(%one, %high) <{operator = "or"}> : (i8, i8) -> i8
    %mul = "pancake.panop"(%minus, %two) <{operator = "mul"}> : (i8, i8) -> i8
    %unsigned = "pancake.cmp"(%minus, %one) <{operator = "lower"}> : (i8, i8) -> i8
    %signed = "pancake.cmp"(%minus, %one) <{operator = "less"}> : (i8, i8) -> i8
    %eq = "pancake.cmp"(%minus, %minus) <{operator = "equal"}> : (i8, i8) -> i8
    %ne = "pancake.cmp"(%minus, %one) <{operator = "notEqual"}> : (i8, i8) -> i8
    %nu = "pancake.cmp"(%minus, %one) <{operator = "notLower"}> : (i8, i8) -> i8
    %ns = "pancake.cmp"(%minus, %one) <{operator = "notLess"}> : (i8, i8) -> i8
    %test = "pancake.cmp"(%high, %one) <{operator = "test"}> : (i8, i8) -> i8
    %ntest = "pancake.cmp"(%high, %high) <{operator = "notTest"}> : (i8, i8) -> i8
    "func.return"(%zero, %all, %wrap, %sub, %xor, %or, %mul, %unsigned, %signed, %eq, %ne, %nu, %ns, %test, %ntest) : (i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00#8, 0xff#8, 0x00#8, 0xff#8, 0x7e#8, 0x81#8, 0xfe#8, 0x00#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x00#8, 0x01#8, 0x01#8]
