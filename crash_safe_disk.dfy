include "map_utils.dfy"
  
module Logging_int_int_Map /* refines Crash_Safe_Data_Structure */ {
  import Map_Utils

  type LBA = int
  type Datum = (int, int)
  type Disk = map<LBA, Datum>
    
  type StructureInterpretation = map<int, int>

  predicate Valid(disk: Disk)
  {
    0 in disk &&
      disk[0].0 >= 0 &&
      disk[0].1 == 0 &&
      (forall i :: 1 <= i <= disk[0].0 ==> i in disk)
  }

  function method LastEntry(disk: Disk) : int
    requires Valid(disk);
  {
    disk[0].0
  }
      
  function PostCrashInterpretation(disk: Disk) : StructureInterpretation
    requires Valid(disk);
    decreases LastEntry(disk);
  {
    if LastEntry(disk) <= 0 then map[]
    else
      var lastEntry := LastEntry(disk);
      var disk' := disk[0 := (lastEntry - 1, 0)];
      PostCrashInterpretation(disk')[disk[lastEntry].0 := disk[lastEntry].1]
  }

  function TrimLastLogEntry(disk: Disk) : Disk
    requires Valid(disk);
    requires LastEntry(disk) > 0;
    ensures Valid(TrimLastLogEntry(disk));
  {
    disk[0 := (LastEntry(disk)-1, 0)]
  }

  lemma DiskInterpretationIgnoresExtra(a: Disk, b: Disk)
    requires Valid(a);
    requires Valid(b);
    requires LastEntry(a) == LastEntry(b);
    requires forall i :: 0 <= i <= LastEntry(a) ==> a[i] == b[i];
    ensures PostCrashInterpretation(a) == PostCrashInterpretation(b);
    decreases LastEntry(a);
  {
    if LastEntry(a) > 0 {
      var a' := TrimLastLogEntry(a);
      var b' := TrimLastLogEntry(b);
      DiskInterpretationIgnoresExtra(a', b');
    }
  }
  
  type InMemoryState = seq<(int, int)>
    
  function TailSeqInterpretation(log: seq<(int, int)>) : StructureInterpretation
  {
    if |log| == 0 then map[]
    else TailSeqInterpretation(log[..|log|-1])[log[|log|-1].0 := log[|log|-1].1]
  }
  
  function OverallInterpretation(disk: Disk, mem: InMemoryState) : StructureInterpretation
    requires Valid(disk);
  {
    var diskmap: StructureInterpretation := PostCrashInterpretation(disk);
    var memmap: StructureInterpretation := TailSeqInterpretation(mem);
    Map_Utils.union_preferA(memmap, diskmap)
  }

  lemma CommittingUpdatesInterpretation(disk: Disk, mem: InMemoryState)
    requires Valid(disk);
    requires forall i :: 0 <= i <= disk[0].0 + |mem| ==> i in disk;
    requires forall i :: 0 <= i < |mem| ==> disk[disk[0].0 + i + 1] == mem[i];
    ensures Valid(disk[0 := (disk[0].0 + |mem|, 0)]);
    ensures OverallInterpretation(disk[0 := (LastEntry(disk) + |mem|, 0)], []) ==
      OverallInterpretation(disk, mem);
    decreases |mem|;
  {
    if |mem| == 0 {
      var disk' := disk[0 := (LastEntry(disk) + |mem|, 0)];
      assert disk' == disk; // Observe
    } else if |mem| == 1 {
      var k := mem[0].0;
      var v := mem[0].1;
      var disk' := disk[0 := (LastEntry(disk) + |mem|, 0)];
      assert disk'[0 := (disk'[0].0 - 1, 0)] == disk; // Observe
    } else {
      CommittingUpdatesInterpretation(disk, mem[0..|mem|-1]);
      var disk' := disk[0 := (LastEntry(disk) + |mem|-1, 0)];
      CommittingUpdatesInterpretation(disk', mem[|mem|-1..|mem|]);
      var disk'' := disk'[0 := (LastEntry(disk') + 1, 0)];
      assert disk'' == disk[0 := (LastEntry(disk) + |mem|, 0)]; // Observe
    }
  }
  
  class Logging_int_int_Map {
    var disk: Disk
    var mem: InMemoryState

    method Set(k: int, v: int)
      requires Valid(disk);
      ensures Valid(disk);
      ensures OverallInterpretation(disk, mem) == old(OverallInterpretation(disk, mem))[k := v];
      modifies this;
    {
      mem := mem + [(k, v)];
    }

    method MakeDurable()
      requires Valid(disk);
      ensures Valid(disk);
      ensures PostCrashInterpretation(disk) == OverallInterpretation(disk, mem);
      ensures OverallInterpretation(disk, mem) == old(OverallInterpretation(disk, mem));
      modifies this;
    {
      if |mem| > 0 {
        var i := 0;
        while i < |mem|
          invariant 0 <= i <= |mem|;
          invariant Valid(disk);
          invariant |mem| > 0;
          invariant forall j :: LastEntry(disk) + 1 <= j < LastEntry(disk) + 1 + i ==> j in disk;
          invariant forall j :: 0 <= j < i ==> disk[LastEntry(disk) + j + 1] == mem[j];
          invariant OverallInterpretation(disk, mem) == old(OverallInterpretation(disk, mem));
          invariant PostCrashInterpretation(disk) == old(PostCrashInterpretation(disk));
        {
          Write(LastEntry(disk) + i + 1, mem[i]);
          i := i + 1;
        }
        CommittingWrite(0, (LastEntry(disk) + |mem|, 0));
      }
    }
    
    method Read(lba: LBA) returns (result: Datum)
      requires Valid(disk);
      requires lba in disk;
      ensures result == disk[lba];
    {
      result := disk[lba];
    }

    method Write(lba: LBA, datum: Datum)
      requires Valid(disk);
      requires lba > LastEntry(disk);
      ensures Valid(disk);
      ensures disk == old(disk)[lba := datum];
      ensures PostCrashInterpretation(disk) == old(PostCrashInterpretation(disk));
      ensures mem == old(mem);
      modifies this;
    {
      DiskInterpretationIgnoresExtra(disk, disk[lba := datum]);
      disk := disk[lba := datum];
    }

    method CommittingWrite(lba: LBA, datum: Datum)
      requires Valid(disk);
      requires |mem| > 0;
      requires lba == 0;
      requires datum == (LastEntry(disk) + |mem|, 0);
      requires forall i :: 0 <= i <= datum.0 ==> i in disk;
      requires forall i :: 0 <= i < |mem| ==> disk[LastEntry(disk) + 1 + i] == mem[i];
      ensures Valid(disk);
      ensures disk == old(disk)[lba := datum];
      ensures PostCrashInterpretation(disk) == old(OverallInterpretation(disk, mem));
      ensures OverallInterpretation(disk, mem) == old(OverallInterpretation(disk, mem));
      modifies this;
    {
      CommittingUpdatesInterpretation(disk, mem);
      disk := disk[lba := datum];
      mem := [];
    }
  }
}
