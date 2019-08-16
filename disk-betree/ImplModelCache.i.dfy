include "ImplModel.i.dfy"
include "../lib/Sets.i.dfy"

module ImplModelCache { 
  import opened ImplModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  predicate RefAvailable(s: Variables, ref: Reference)
  {
    && s.Ready?
    && ref !in s.ephemeralIndirectionTable
    && ref !in s.cache 
  }

  function getFreeRefIterate(s: Variables, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if i !in s.ephemeralIndirectionTable && i !in s.cache then (
      Some(i)
    ) else if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRefIterate(s, i+1) 
    )
  }

  function {:opaque} getFreeRef(s: Variables)
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  {
    getFreeRefIterate(s, 0)
  }

  function {:opaque} write(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  : (s': Variables)
  requires s.Ready?
  {
    // TODO how do we deal with this?
    var eph := s.ephemeralIndirectionTable[ref := (None, if node.children.Some? then node.children.value else [])];
    s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node])
  }

  function {:opaque} alloc(k: Constants, s: Variables, node: Node)
  : (p: (Variables, Option<Reference>))
  requires s.Ready?
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (write(k, s, ref.value, node), ref)
    ) else (
      (s, None)
    )
  }
}
