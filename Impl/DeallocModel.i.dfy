// include "BookkeepingModel.i.dfy"

// module DeallocModel { 
//   import IT = IndirectionTable
//   import opened StateSectorModel
//   import opened IOModel
//   import opened DiskOpModel
//   import opened BookkeepingModel
//   import opened Bounds
//   import opened ViewOp
//   import opened InterpretationDiskOps

//   import opened Options
//   import opened Maps
//   import opened Sequences
//   import opened Sets

//   import opened NativeTypes

//   import LruModel

//   predicate deallocable(s: BBC.Variables, ref: BT.G.Reference)
//   {
//     && s.Ready?
//     && var graph := s.ephemeralIndirectionTable.graph;
//     // TODO: dedup
//     && ref in graph
//     && ref != BT.G.Root()
//     && (forall r | r in graph :: ref !in graph[r])
//   }

//   // predicate deallocable(ref: BT.G.Reference)
//   // {
//   //   && ref in this.I().graph
//   //   && ref != BT.G.Root()
//   //   && (forall r | r in this.I().graph :: ref !in this.I().graph[r])
//   // }

//   function {:opaque} Dealloc(s: BBC.Variables, io: IO, ref: BT.G.Reference)
//   : (res : (BBC.Variables, IO))
//   requires BBC.Inv(s)
//   requires io.IOInit?
//   requires deallocable(s, ref)
//   {
//     if (
//       && s.frozenIndirectionTable.Some?
//       && s.frozenIndirectionTable.value.hasEmptyLoc(ref)
//     ) then (
//       (s, io)
//     ) else if BC.OutstandingRead(ref) in s.outstandingBlockReads.Values then (
//       (s, io)
//     ) else (
//       var eph := s.ephemeralIndirectionTable
//         .(graph := MapRemove1(s.ephemeralIndirectionTable.graph, ref))
//         .(locs := MapRemove1(s.ephemeralIndirectionTable.locs, ref));

//       // var blockAllocator' := if oldLoc.Some?
//       //   then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
//       //   else s.blockAllocator;

//       var s' := s
//         .(ephemeralIndirectionTable := eph)
//         .(cache := MapRemove(s.cache, {ref}));
//       //   .(lru := LruModel.Remove(s.lru, ref))
//       //   .(blockAllocator := blockAllocator');
//       (s', io)
//     )
//   }

//   lemma DeallocCorrect(s: BBC.Variables, io: IO, ref: BT.G.Reference)
//   requires BBC.Inv(s)
//   requires io.IOInit?
//   requires deallocable(s, ref)
//   ensures var (s', io') := Dealloc(s, io, ref);
//       && ValidDiskOp(diskOp(io'))
//       && IDiskOp(diskOp(io')).jdop.NoDiskOp?
//       && (
//         || BBC.Next(s, s', IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))
//         || BBC.Next(s, s', IDiskOp(diskOp(io')).bdop, StatesInternalOp)
//       )
//   {
//     reveal_Dealloc();
//     var (s', io') := Dealloc(s, io, ref);

//     // LruModel.LruRemove(s.lru, ref);

//     if (
//       && s.frozenIndirectionTable.Some?
//       && s.frozenIndirectionTable.value.hasEmptyLoc(ref)
//     ) {
//       assert noop(s, s');
//       return;
//     }

//     if BC.OutstandingRead(ref) in s.outstandingBlockReads.Values {
//       assert noop(s, s');
//       return;
//     }

//     assert BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref);

//     // lemmaIndirectionTableLocIndexValid(s, ref);

//       var eph := s.ephemeralIndirectionTable
//         .(graph := MapRemove1(s.ephemeralIndirectionTable.graph, ref))
//         .(locs := MapRemove1(s.ephemeralIndirectionTable.locs, ref));

//     // var (eph, oldLoc) := s.ephemeralIndirectionTable.removeRef(ref);

//     // var blockAllocator' := if oldLoc.Some?
//     //   then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
//     //   else s.blockAllocator;

//     // freeIndirectionTableLocCorrect(s, s', ref,
//     //   if oldLoc.Some?
//     //   then Some(oldLoc.value.addr as int / NodeBlockSize())
//     //   else None);
//     // reveal_ConsistentBitmap();

//     // assert WFBCVars(s');

//     var iDiskOp := IDiskOp(diskOp(io)).bdop;
//     assert BC.Unalloc(s, s', iDiskOp, AdvanceOp(UI.NoOp, true), ref);
//     assert BBC.BlockCacheMove(s, s', iDiskOp, AdvanceOp(UI.NoOp, true), BC.UnallocStep(ref));
//     //assert stepsBC(s, s', AdvanceOp(UI.NoOp, true), io, BC.UnallocStep(ref));
//     assert BBC.NextStep(s, s', iDiskOp, AdvanceOp(UI.NoOp, true), BBC.BlockCacheMoveStep(BC.UnallocStep(ref)));
//   }
// /*

//   function {:opaque} FindDeallocable(s: BBC.Variables)
//   : (ref: Option<Reference>)
//   requires WFBCVars(s)
//   requires s.Ready?
//   {
//     s.ephemeralIndirectionTable.findDeallocable()
//   }

//   lemma FindDeallocableCorrect(s: BBC.Variables)
//   requires WFBCVars(s)
//   requires s.Ready?
//   ensures var ref := FindDeallocable(s);
//       && (ref.Some? ==> ref.value in s.ephemeralIndirectionTable.I().graph)
//       && (ref.Some? ==> deallocable(s, ref.value))
//       && (ref.None? ==> forall r | r in s.ephemeralIndirectionTable.I().graph :: !deallocable(s, r))
//   {
//     reveal_FindDeallocable();
//   }
//   */
// }
