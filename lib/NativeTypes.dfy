module NativeTypes {
  newtype {:nativeType "byte"} byte = i:int | 0 <= i < 0x100
  newtype {:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
}
