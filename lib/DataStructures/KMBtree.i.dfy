include "MutableBtreeBulkOperations.i.dfy"
include "MutableBtree.i.dfy"
include "../Base/Message.i.dfy"
  
module KMBtreeModel refines BtreeModel {
  //import Keys = Lexicographic_Byte_Order
  import Messages = ValueMessage`Internal
  type Value = Messages.Message
}

module LKMBtree refines LMutableBtree {
  import Model = KMBtreeModel
    
  function method MaxKeysPerLeaf() : uint64 { 64 }
  function method MaxChildren() : uint64 { 64 }

  function method DefaultValue() : Value { Model.Messages.DefineDefault() }
  function method DefaultKey() : Key { [] }
}

module KMBtree refines MutableBtree {
  import L = LKMBtree`All
  import Model = KMBtreeModel
}

// TODO(robj): dead code; delete?
module KMBtreeBulkOperations refines MutableBtreeBulkOperations {
  import opened MB = KMBtree`All
}
