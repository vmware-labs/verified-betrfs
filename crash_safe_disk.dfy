abstract module Synchronous_Disk {
  type LBA(==)
  type Datum

  // We model a disk as a mutable map from LBAs to Datums
  type State = map<LBA, Datum>
    
  trait Disk {
    function Interpret() : map<LBA, Datum>
      
    method Read(lba: LBA) returns (result: Datum)
      requires lba in Interpret();
      ensures result == Interpret()[lba];

    method Write(lba: LBA, datum: Datum)
      ensures Interpret() == old(Interpret())[lba := datum];
  }
}

// A crash-safe disk enforces that every write either
// - not change the post-crash state, or
// - ensure that the post-crash state is the current state
abstract module Crash_Safe_Disk refines Synchronous_Disk {
  import DS: On_Disk_Data_Structure

  trait Disk {
    var mem: DS.In_Memory_State
    ghost var post_crash_mem: DS.In_Memory_State
      
    method Write(lba: LBA, datum: Datum)
      ensures Interpret() == old(Interpret())[lba := datum];
      ensures DS.Interpret(post_crash_mem, Interpret()) == DS.Interpret(post_crash_mem, old(Interpret()));

    method CommittingWrite(lba: LBA, datum: Datum)
      ensures Interpret() == old(Interpret())[lba := datum];
      ensures DS.Interpret(post_crash_mem, Interpret()) == DS.Interpret(mem, old(Interpret()));

    constructor()
  }
}

abstract module On_Disk_Data_Structure {
  import Disk_Model: Synchronous_Disk
    
  type Interpretation(==)

  class In_Memory_State {
    constructor()
  }

  function Interpret(mem: In_Memory_State, disk: map<Disk_Model.LBA, Disk_Model.Datum>) : Interpretation
  
}

  
abstract module Crash_Safe_Data_Structure refines On_Disk_Data_Structure {
  import Disk_Model = Crash_Safe_Disk
    
}
  
