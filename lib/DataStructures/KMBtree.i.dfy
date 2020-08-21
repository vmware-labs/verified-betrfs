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
