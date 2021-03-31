def upper_bound(prec):
  prec = prec // 8
  return ("0x1" + (prec * "_00")).replace("_00_00", "_0000")

for precision in (8, 16, 32, 64):
  print("""
  /*
   * uint8 arithmetic and bit operations
   */

  function method bit_or_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) | (b as bv8)) as uint8
  }

  function method bit_and_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) & (b as bv8)) as uint8
  }

  function method bit_xor_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) ^ (b as bv8)) as uint8
  }

  function wrapped_add_uint8(a: uint8, b: uint8): uint8 {
    if a as int + b as int < 0x1_00 then
      a + b
    else
      (a as int + b as int - 0x1_00) as uint8
  }

  function wrapped_sub_uint8(a: uint8, b: uint8): uint8 {
    if a as int - b as int >= 0 then
      a - b
    else
      (a as int - b as int + 0x1_00) as uint8
  }""".replace('8', str(precision)).replace('0x1_00', upper_bound(precision)))

  for op in ("or", "and", "xor", "add", "sub"):
    a = """
  method {:extern} execute_atomic_fetch_OP_uint8<G>(
      a: Atomic<uint8, G>,
      operand: uint8) 
  returns (
      ret_value: uint8,
      ghost orig_value: uint8,
      ghost new_value: uint8,
      ghost linear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_OP_uint8(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)"""

    a = a.replace("OP", op).replace('8', str(precision))

    if op in ("add", "sub"):
      a = a.replace("bit", "wrapped")

    print(a)
