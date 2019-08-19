include "ImplModel.i.dfy"
include "ImplModelIO.i.dfy"
include "../lib/Sets.i.dfy"

module ImplModelCache { 
  import opened ImplModel
  import opened ImplModelIO

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
    && ref != BT.G.Root()
  }

  function getFreeRefIterate(s: Variables, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires i >= 1
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
    getFreeRefIterate(s, 1)
  }

  function {:opaque} write(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  : (s': Variables)
  requires s.Ready?
  ensures s'.Ready?
  {
    // TODO how do we deal with this?
    var eph := s.ephemeralIndirectionTable[ref := (None, if node.children.Some? then node.children.value else [])];
    s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node])
  }

  function {:opaque} alloc(k: Constants, s: Variables, node: Node)
  : (p: (Variables, Option<Reference>))
  requires s.Ready?
  ensures var (s', id) := p;
    s'.Ready?
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (write(k, s, ref.value, node), ref)
    ) else (
      (s, None)
    )
  }
 
  lemma allocCorrect(k: Constants, s: Variables, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  ensures var (s', ref) := alloc(k, s, node);
    && WFVars(s')
    && (ref.Some? ==> BC.Alloc(Ik(k), IVars(s), IVars(s'), ref.value, INode(node)))
    && (ref.None? ==> s' == s)
  {
    reveal_alloc();
    reveal_write();
    var ref := getFreeRef(s);
  }
  
  lemma writeCorrect(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires ref == BT.G.Root() ==> s.rootBucket == map[]
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value ==> s.frozenIndirectionTable.value[ref].0.Some?
  ensures var s' := write(k, s, ref, node);
    && WFVars(s')
    && BC.Dirty(Ik(k), IVars(s), IVars(s'), ref, INode(node))
  {
    reveal_write();
    if (ref == BT.G.Root()) {
      INodeRootEqINodeForEmptyRootBucket(node);
    }
  }
}
