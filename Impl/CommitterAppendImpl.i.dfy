// include "CommitterAppendModel.i.dfy"
// include "CommitterImpl.i.dfy"
// include "DiskOpImpl.i.dfy"

// module CommitterAppendImpl {
//   import opened NativeTypes
//   import opened Options

//   import opened DiskLayout
//   import opened KeyType
//   import opened ValueType
//   import opened Journal

//   import opened DiskOpImpl
//   import opened CommitterModel
//   import opened StateModel
//   import opened IOModel
//   import CommitterAppendModel
//   import JournalistImpl

//     linear inout method JournalAppend(key: Key, value: Value)
//     requires old_self.Inv()
//     requires old_self.status == StatusReady
//     requires old_self.journalist.canAppend(JournalInsert(key, value))
//     ensures self.Inv()
//     // ensures var je := JournalInsert(key, value);
//     //   self.I() == old_self.I().(inMemoryJournal := old_self.I().inMemoryJournal + [je])
//     // ensures self.I() == CommitterAppendModel.JournalAppend(
//     //     old_self.I(), key, value)
//     ensures JournalCache.Next(
//         old_self.I(), self.I(), JournalDisk.NoDiskOp,
//         AdvanceOp(UI.PutOp(key, value), false));
//     {
//       var je := JournalInsert(key, value);
//       inout self.journalist.append(je);

//       assert JournalCache.Advance(
//           old_self.I(), self.I(), JournalDisk.NoDiskOp,
//           AdvanceOp(UI.PutOp(key, value), false));
//       assert JournalCache.NextStep(
//           old_self.I(), self.I(), JournalDisk.NoDiskOp,
//           AdvanceOp(UI.PutOp(key, value), false),
//           JournalCache.AdvanceStep);
//     }

// }
