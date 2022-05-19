// trusted SQLite module
include "../lib/Lang/NativeTypes.s.dfy"

module KVType {
  import NativeTypes

  type IndexKey = seq<NativeTypes.byte>
  type TableKey = NativeTypes.nat64
  type Value = seq<NativeTypes.byte>
}

// which layer should txns at


module SQLite {
  import opened KVType

  type ID = int

  datatype Entry = 
    | IndexEntry(ikey: IndexKey)
    | TableEntry(tkey: TableKey, v: Value)

  datatype Store = 
    | Index(keys: seq<IndexKey>, id: ID)
    | Table(kv: imap<TableKey, Value>, id: ID)

  datatype Database = Database(stores: seq<Store>)

  predicate WF(db: Database)
  {
    && true // TODO
  }

  predicate WFStore(s: Store)
  {
    && true // TODO
  }

  predicate ValidNewID(db: Database, id: ID)
  {
    && true
  }

  function EmptyKV() : (zmap : imap<TableKey,Value>)
  {
    imap k :: []
  }

  predicate ValidNewStore(db: Database, s: Store)
  {
    && WFStore(s)
    && ValidNewID(db, s.id)
    && (s.Index? ==> s.keys == [])
    && (s.Table? ==> s.kv == EmptyKV())
  }

  predicate Create(db: Database, db': Database, s: Store)
  {
    && WF(db)
    && WF(db')
    && ValidNewStore(db, s)
    && db'.stores == db.stores + [s]
  }

  predicate Delete(db: Database, db': Database, s: Store)
  {
    && WF(db)
    && WF(db')
    // TODO
  }

  predicate Insert(db: Database, db': Database, s: Store, e: Entry)
  {
    && WF(db)
    && WF(db')
    // TODO
  }

  predicate GroupOps(db: Database, db': Database)
  {
    && true
  }

  // datatype op for individual step
  predicate BeginTxn(db: Database, db': Database)
  {
    && WF(db)
    && WF(db')
    // TODO
  }

  predicate EndTxn(db: Database, db': Database)
  {
    && WF(db)
    && WF(db')
    // TODO
  }

  // in terms of sync there's normal and full
  // normal only sync at checkpoint vs full syncs after each txn   

  // kv store on top of a kv store

  // split into 3 pieces: top half of DB, bottom end of DB, storage layer

  // 1. getting some execution traces
  // 2. pair programs together (ping jon)
  // 3. can skip the actual pager impl for now 
}