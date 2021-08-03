// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
include "PathBasedFS.i.dfy"

module PathBasedFSInv {
  import opened Options
  import opened PathBasedFS
  import opened FSTypes
  import opened PathSpec

  predicate Inv(fs: FileSys)
  {
    && WF(fs)
    // path is connected
    && (forall path | PathExists(fs, path) && path != RootDir :: ParentDirIsDir(fs, path))
    // redirect meta points to a valid and hidden path meta
    && (forall path | fs.meta_map[path].RedirectMeta? :: 
        && fs.meta_map[fs.meta_map[path].source].PathMeta?
        && fs.meta_map[fs.meta_map[path].source].hidden
        && !fs.meta_map[fs.meta_map[path].source].m.ftype.Directory?)
  }

  lemma InitImpliesInv(fs: FileSys)
  requires Init(fs)
  ensures Inv(fs)
  {
  }

  lemma NextPreservesInv(fs: FileSys, fs': FileSys)
  requires Inv(fs)
  requires Next(fs, fs')
  ensures Inv(fs')
  {
    var step :| NextStep(fs, fs', step);
    NextStepPreservesInv(fs, fs', step);
  }

  lemma NextStepPreservesInv(fs: FileSys, fs': FileSys, step: Step)
  requires Inv(fs)
  requires NextStep(fs, fs', step)
  ensures Inv(fs')
  {
    match step {
      case DeleteStep(path, ctime) => DeletePreservesInv(fs, fs', path, ctime);
      case RenameStep(source, dest, ctime) => RenamePreservesInv(fs, fs', source, dest, ctime);
      case LinkStep(source, dest, ctime, hiddenName) => LinkPreservesInv(fs, fs', source, dest, ctime, hiddenName);
      case _ => {
        if step.CreateStep? || step.ChangeAttrStep? || step.TruncateStep? || step.WriteStep? || step.UpdateTimeStep? {
          SimpleStepPreservesInv(fs, fs', step);
        }
      }
    }
  }

  lemma DeletePreservesInv(fs: FileSys, fs': FileSys, path: Path, ctime: Time)
  requires Inv(fs)
  requires Delete(fs, fs', path, ctime)
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p) && p != RootDir
    ensures ParentDirIsDir(fs', p)
    {
      assert PathExists(fs, p); // observe
    }

    // forall p | fs'.meta_map[p].RedirectMeta? 
    // ensures fs'.meta_map[fs'.meta_map[p].source].PathMeta?
    // ensures fs'.meta_map[fs'.meta_map[p].source].hidden
    // ensures !fs'.meta_map[fs'.meta_map[p].source].m.ftype.Directory?
    // {
    //   var m := fs.meta_map[path];

    //   if m.RedirectMeta? && fs'.meta_map[p].source == m.source {
    //     assert fs.meta_map[p] == fs'.meta_map[p];
    //     assert fs'.meta_map[m.source] == MetaDataDelete(fs, path, ctime);

    //     if NoAlias(fs, path) {
    //       assert p != path;
    //       assert false;
    //     }
    //   }
    // }
    assert Inv(fs');
  }

  // lemma RenamedPathsRemainDifferent(src: Path, dst: Path, p1: Path, p2: Path)
  // requires p1 != p2
  // requires p1 == dst || BeneathDir(dst, p1)
  // requires p2 == dst || BeneathDir(dst, p2)
  // ensures src + p1[|dst|..] != src + p2[|dst|..]
  // {
  //   if BeneathDir(dst, p1) && BeneathDir(dst, p2) {
  //     assert p1[|dst|..] != p2[|dst|..];

  //     var p1' := src + p1[|dst|..];
  //     var p2' := src + p2[|dst|..];

  //     assert p1'[..|src|] == p2'[..|src|];
  //   }
  // }

  lemma {:timeLimitMultiplier 2} RenamePreservesInv(fs: FileSys, fs': FileSys, src: Path, dst: Path, ctime: Time)
  requires Inv(fs)
  requires Rename(fs, fs', src, dst, ctime)
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p) && p != RootDir
    ensures ParentDirIsDir(fs', p)
    {
      if p == dst {
        assert ParentDirIsDir(fs', p);
      } else if BeneathDir(dst, p) {
        var parent_dir := GetParentDir(p);
        var srcpath := src + p[|dst|..];
        var srcparent_dir := GetParentDir(srcpath);
        assert ParentDirIsDir(fs, srcpath); // observe
        assert parent_dir == dst || BeneathDir(dst, parent_dir); // observe

        if parent_dir == dst {
          assert fs'.meta_map[parent_dir] == UpdatePathCtime(fs, src, ctime);
        } else {
          assert src + parent_dir[|dst|..] == srcparent_dir; // observe
          assert fs'.meta_map[parent_dir] == fs.meta_map[srcparent_dir];
        }
      } else if fs.meta_map[dst].RedirectMeta? && fs.meta_map[dst].source == p {
        assert ParentDirIsDir(fs', p);
      } else if  p == GetParentDir(src) || p == GetParentDir(dst) {
        assert ParentDirIsDir(fs', p);
      } else {
        assert ParentDirIsDir(fs, p);
        assert ParentDirIsDir(fs', p);
      }
    }

    forall p | fs'.meta_map[p].RedirectMeta? 
    ensures fs'.meta_map[fs'.meta_map[p].source].PathMeta?
    ensures fs'.meta_map[fs'.meta_map[p].source].hidden
    ensures !fs'.meta_map[fs'.meta_map[p].source].m.ftype.Directory?
    {
      assume false;
      // if (p == dest || p == source) && fs.meta_map[source].PathMeta? {
      //   assert fs'.meta_map[hiddenName.value] == LinkMeta(fs, source, ctime);
      // }
    }
    assert Inv(fs');
  }

  lemma LinkPreservesInv(fs: FileSys, fs': FileSys, source: Path, dest: Path, ctime: Time, hiddenName: Option<Path>)
  requires Inv(fs)
  requires Link(fs, fs', source, dest, ctime, hiddenName)
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p) && p != RootDir
    ensures ParentDirIsDir(fs', p)
    {
      if p == dest {
        assert ParentDirIsDir(fs', p);
      } else {
        assert PathExists(fs, p); // observe
      }
    }

    forall p | fs'.meta_map[p].RedirectMeta? 
    ensures fs'.meta_map[fs'.meta_map[p].source].PathMeta?
    ensures fs'.meta_map[fs'.meta_map[p].source].hidden
    ensures !fs'.meta_map[fs'.meta_map[p].source].m.ftype.Directory?
    {
      if (p == dest || p == source) && fs.meta_map[source].PathMeta? {
        assert fs'.meta_map[hiddenName.value] == LinkMeta(fs, source, ctime);
      }
    }
    assert Inv(fs');
  }

  lemma SimpleStepPreservesInv(fs: FileSys, fs': FileSys, step: Step)
  requires Inv(fs)
  requires NextStep(fs, fs', step)
  requires step.CreateStep? || step.ChangeAttrStep? || step.TruncateStep? || step.WriteStep? || step.UpdateTimeStep?
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p) && p != RootDir 
    ensures ParentDirIsDir(fs', p)
    {
      if p != step.path {
        assert PathExists(fs, p); // observe
      }
    }
    assert Inv(fs');
  }
}
