d = 0x11EDC6F41
#for i in range(0, 33):
  #print("true, " if (d >> i) & 1 != 0 else "false, ")
#print(", ".join("a"+str(i)+": bool" for i in range(0, 32)))
#print(" && ".join(("!" if i != 0 else "")+"a"+str(i)+"" for i in range(0, 32)))
#print(", ".join("a"+str(i)+"" for i in range(0, 31)))

def get(i):
  if i <= 30:
    return ("!" if (d>>(i+1))&1 else "")+"a"+str(i+1)
  else:
    return "true"
#print(", ".join(get(i) for i in range(0, 32)))

cache = {}
def mod_pow(k):
  assert k >= 0
  if k in cache:
    return cache[k]

  if k == 0:
    res = 1
  else:
    p = mod_pow(k-1)
    p = p << 1
    if p >> 32:
      p = p ^ d
    res = p

  cache[k] = res
  return res

def pow_str(k):
  p = mod_pow(k)
  return "pow("+str(k)+"," + ",".join("true" if (p>>i)&1 else "false" for i in range(0,32)) + ")"

def main():
  print("""include "CRC32LutLemma.i.dfy"

module CRC32_C_Lut_Powers {
  import opened Bits_s
  import opened F2_X_s
  import opened CRC32_C_Lut_Lemma

""")

  for i in range(1, 2*256+1): #(2*256*64-33) + 1 // 8 + 1):
    k = 64*i - 33
    print("  lemma pow_"+str(k)+"()")
    print("  ensures "+pow_str(k))
    print("  {")
    #prev = k - 64
    #if prev < 0:
    #  prev = -1

    #for j in range(prev+1, k):
    """
    for j in range(k-1, prev, -1):
      print("    assert " + pow_str(j) + " by {")
    if prev >= 0:
      print("    pow_"+str(prev)+"();")
    print("    " + ("}" * (k-1-prev)))
    """

    if i > 1:
      print("    assert " + pow_str(k-21) + " by { ")
      print("    assert " + pow_str(k-42) + " by { pow_" + str(k-64) + "(); } }")

    
    print("  }")

  print("}")

main()
