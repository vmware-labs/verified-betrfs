include "../lib/Base/Option.s.dfy"
include "../lib/Base/sequences.i.dfy"

/*
 * What I want in a module system:
 * The ability to refine multiple modules at once, specifying how imports from
 * one satisfy abstract obligations (eg unstated types) of others.
 *
 * These definitions give rise to a family of related types, and I want to drop
 * them in.
 *
 * Given that I'm stuck with Dafny's crappy one, I can rewrite this with templates,
 * maybe. Nope, because templates don't provide a sane way to leave a parameter
 * to be filled by a predicate body.
 */

abstract module UIfc {
  type UIOp(==)
}

module MapIfc refines UIfc {
  type K(==)
  type V(==)
  datatype UIOp = Put(k:K, v:V) | Get(k:K, v:V)
}

abstract module CrashableIfc refines UIfc {
  type SyncId = nat
  datatype CUIOp<UIOp> =
    App(a:UIOp) | Crash | SyncRequest(syncId:SyncId) | SyncComplete(syncId:SyncId)
}

module CrashableMapIfc refines CrashableIfc {
  
}

abstract module Spec {
  import Ifc : UIfc

  type Vars(==)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp)
}

module MapSpec refines Spec {
  import Ifc = MapIfc

  type V = Ifc.V
  type K = Ifc.K
  // type UIOp = Ifc.UIOp // That I can't use this synonym is a bug.

  datatype Vars = Vars(m:map<K,V>)
  predicate Init(s:Vars) {
    s.m == map[]
  }
  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp) {
    match uiop
      case Get(k,v) => s.m[k]==v && s'==s
      case Put(k,v) => s'.m == s.m[k := v]
  }
}

// Analog to Spec
abstract module Crashable refines CrashableIfc {
  type Vars(==)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, iop:UIOp)
}

abstract module CrashSafe refines Crashable {
  import opened Options
  import opened Sequences

  // The parameter machine
  type PUIOp(==)
  type PVars(==, !new)
  predicate PInit(s:PVars)
  predicate PNext(s:PVars, s':PVars, iop:PUIOp)

  type AppOp = PUIOp

  datatype View = View(p:PVars, syncId:Option<SyncId>)

  // The sequence of states that have been issued toward the disk.
  // The first one is persistent. The last one is the current ephemeral state.
  // The ephemeral state always has syncId.None?.
  datatype Vars = Vars(views:seq<View>)

  predicate Init(s:Vars) {
    && |s.views| == 1
    && PInit(s.views[0].p)
    && s.views[0].syncId.None?
  }

  predicate Next(s:Vars, s':Vars, uiop:UIOp) {
    // spontaneous write completion can happen whenever you like
    || s'.views == s.views[1..]
    || (
      && uiop.App?
      && var e := Last(s.views).p;
          exists e' ::
            && PNext(e, e', uiop.a)
            && s'.views == s.views + [View(e', None)]
       )

//    || (match uiop
//        App(a) => (
//          var e := Last(s.views).p;
//          exists e' ::
//            && PNext(e, e')
//            && s'.views == s.views + [View(e', None)]
//            )
//
//        Crash =>
//          s'.views == s.views[..1]
//          
//        SyncRequest(syncId) =>
//          var eview := Last(s.views);
//          s'.views == DropLast(s.views) + [View(eview.p, syncId), eview]
//
//        SyncComplete(syncId) =>
//          // If syncId is associated with the peristent state, you may report it complete.
//          && s.views[0].syncId == syncId
//          && s'.views == s.views[0 := s.views[0](.syncId == None)]
//      )
  }
}

module CrashSafeMap refines Crashable {
  import opened MapSpec
}

//--module DiskIfc {
//--  type Addr(!new, ==)
//--  type Block(!new)
//--  datatype IOp = Read(a:Addr, b:Block) | Write(a:Addr, b:Block)
//--}
//--
//--module Disk {
//--  import opened DiskIfc
//-- 
//--  datatype Vars = Vars(m:map<Addr, Block>)
//--
//--  predicate Next(s:Vars, s':Vars, iop:IOp) {
//--    match iop
//--      case Read(a, b) => a in s.m && s.m[a]==b && s'==s
//--      case Write(a, b) => s'.m == s.m[a := b]
//--  }
//--}
//--
//--abstract module CacheIfc {
//--  type Vars(!new)
//--}
//--
//--abstract module ClientSkeleton {
//--  import opened CrashableSpec
//--  import opened DiskIfc
//--  import Disk
//--  import CacheIfc
//--
//--  type ConcreteVars
//--  datatype Vars = Vars(cv:ConcreteVars, cache:CacheIfc.Vars)
//--
//--  predicate Init(s:Vars)
//--  predicate Mkfs(d:Disk.Vars)
//--  predicate Next(s:Vars, s':Vars, uiop:UIOp, iop:IOp)
//--}
//--
//--abstract module CrashFreeIOSystem {
//--  import opened CrashableSpec
//--  import ClientSkeleton
//--  import opened DiskIfc
//--  import Disk
//--
//--  datatype Vars = Vars(c:ClientSkeleton.Vars, d:Disk.Vars)
//--
//--  predicate Init(s:Vars)
//--  {
//--    && ClientSkeleton.Init(s.c)
//--    && ClientSkeleton.Mkfs(s.d)
//--  }
//--
//--  predicate Next(s:Vars, s':Vars, uiop:UIOp, iop:IOp)
//--  {
//--    && !uiop.Crash?
//--    && ClientSkeleton.Next(s.c, s'.c, uiop, iop)
//--    && Disk.Next(s.d, s'.d, iop)
//--  }
//--}
//--
//--abstract module CrashableIOSystem {
//--  import opened CrashableSpec
//--  import ClientSkeleton
//--  import opened DiskIfc
//--  import Disk
//--
//--  datatype Vars = Vars(c:ClientSkeleton.Vars, d:Disk.Vars)
//--
//--  predicate Init(s:Vars)
//--  {
//--    && ClientSkeleton.Init(s.c)
//--    && ClientSkeleton.Mkfs(s.d)
//--  }
//--
//--  predicate Next(s:Vars, s':Vars, uiop:UIOp, iop:IOp)
//--  {
//--    if uiop.Crash?
//--    then
//--      && uiop.Crash?
//--      && ClientSkeleton.Init(s'.c)
//--      && s'.d == s'.d
//--    else
//--      && ClientSkeleton.Next(s.c, s'.c, uiop, iop)
//--      && Disk.Next(s.d, s'.d, iop)
//--  }
//--}
//--
//--
//--abstract module CrashSafeSpec refines CrashSafe {
//-- 
//--}
//--
//--abstract module CrashFreeIOSystemRefinement refines CrashFreeIOSystem {
//--  import Spec
//--
//--  function I(s:Vars) : Spec.Vars
//--}
//--
//--abstract module CrashableIOSystemRefinement refines CrashableIOSystem {
//--  import Spec
//--
//--  function I(s:Vars) : Spec.Vars
//--}
//--
//--abstract module CrashSafeCacheConfersCrashSafety {
//--  import CrashFreeIOSystemRefinement
//--  import CrashableIOSystemRefinement
//--  import CrashableIOSystem
//--  import CrashSafeSpec
//--  import Spec
//--
//--  lemma CrashSafeCacheConfersCrashSafety()
//--    requires
//--      //var x : CrashFreeIOSystemRefinement.UIOp :| true;
//--      var x := CrashFreeIOSystemRefinement.foo();
//--      var y : Spec.UIOp :| true;
//--      y==x
//--    /*
//--    requires forall s,s',uiop:CrashFreeIOSystemRefinement.UIOp,iop::
//--      CrashFreeIOSystemRefinement.Next(s,s',uiop,iop)
//--        ==> Spec.Next(CrashFreeIOSystemRefinement.I(s), CrashFreeIOSystemRefinement.I(s'), uiop)
//--
//--    // Try to bind Client the same way in both?
//--    requires forall s,s',uiop,iop ::
//--      CrashFreeIOSystemRefinement.ClientSkeleton.Next(s,s',uiop,iop)
//--        <==> CrashableIOSystem.ClientSkeleton.Next(s,s',uiop,iop)
//--
//--    ensures forall s,s',uiop,iop ::
//--      CrashableIOSystem.Next(s,s',uiop,iop)
//--        ==> CrashSafeSpec.Next(CrashableIOSystemRefinement.I(s), CrashableIOSystemRefinement.I(s'), uiop)
//--    */
//--
//--}
