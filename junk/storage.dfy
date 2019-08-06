include "Maps.s.dfy"

  // Problems with this model:
  // - non-atomic write-back not modeled (fix by improving model)
  // - does not prevent user from rolling back disk state (fix by rewriting as a class or trait)
  // - does not enforce that every step preserves consistency (???)
  // - Synchronous (ok with me for now)
abstract module Buffered_Storage {
  import Maps = Maps

  type LBA(==)
  type Datum

  type DurableStore = map<LBA, Datum>
  type WriteBuffer = map<LBA, Datum>
  datatype BufferedStore = BufferedStore(durable: DurableStore, buffer: WriteBuffer)

  function State(disk: BufferedStore) : map<LBA, Datum> {
    Maps.union_preferA(disk.buffer, disk.durable)
  }

  function Crash(disk: BufferedStore) : BufferedStore {
    BufferedStore(disk.durable, map[])
  }

  predicate NextBufferedStore(disk': BufferedStore, disk: BufferedStore) {
      forall lba :: lba in disk'.buffer ==> lba in disk.buffer && disk'.buffer[lba] == disk.buffer[lba]
    && disk'.durable.Keys >= disk.durable.Keys
    && disk'.durable.Keys <= disk.durable.Keys + disk.buffer.Keys
    && forall lba :: lba in disk'.durable.Keys - disk.buffer.Keys ==> disk'.durable[lba] == disk.durable[lba]
    && forall lba :: lba in disk'.durable.Keys - disk.durable.Keys ==> disk'.durable[lba] == disk.buffer[lba]
    && forall lba :: lba in disk.buffer.Keys * disk.durable.Keys ==>
      (disk'.durable[lba] == disk.durable[lba] || disk'.durable[lba] == disk.buffer[lba])
  }

  datatype ReadResult = Error | DNE | ReadResult(datum: Datum)
  method Read(disk: BufferedStore, lba: LBA)
    returns (result : (ReadResult, BufferedStore))
    ensures NextBufferedStore(result.1, disk);
    ensures result.0.DNE? ==> lba !in State(disk);
    ensures result.0.ReadResult? ==> (lba in State(disk) && result.0.datum == State(disk)[lba]);

  datatype WriteResult = Error | Success
  method Write(disk: BufferedStore, lba: LBA, datum: Datum)
    returns (result: (WriteResult, BufferedStore))
    ensures result.0.Success? ==>
            NextBufferedStore(result.1, BufferedStore(disk.durable, disk.buffer[lba := datum]));
    ensures result.0.Error? ==> NextBufferedStore(result.1, disk);

  datatype SyncResult = Error | Success
  method Sync(disk: BufferedStore)
    returns (result: (SyncResult, BufferedStore))
    ensures NextBufferedStore(result.1, disk);
    ensures result.0.Success? ==> result.1.durable == State(disk);
}
