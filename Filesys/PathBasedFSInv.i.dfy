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
    // Hidden view consistency: no redirect in the hidden map
    && (forall path :: !fs.hidden.meta_map[path].RedirectMeta?)
    // Hidden view consistency: no directory in hidden map
    && (forall path | fs.hidden.meta_map[path].MetaData? :: !fs.hidden.meta_map[path].ftype.Directory?)
    // Content view and hidden view consistency: a redirect meta has a valid entry in hidden view
    && (forall path | fs.content.meta_map[path].RedirectMeta? :: ValidHiddenEntry(fs, path))
    // Content view and hidden view consistency: no dangly hidden view entries
    && (forall hidden | fs.hidden.meta_map[hidden].MetaData? :: HasReference(fs, hidden))
    // Refinement inv: all valid paths have valid IDs
    && (forall path | PathExists(fs, path) :: GetMeta(fs, path).id.ID?)
    // Refinement inv: alias path and id relationship
    && (forall path | PathExists(fs, path) :: AliasConsistentWithID(fs, path))
    // Refinement inv: nonexistent paths have empty data
    && (forall path | !PathExists(fs, path) :: GetData(fs, path) == EmptyData())
  }

  predicate AliasConsistentWithID(fs: FileSys, path: Path)
  requires WF(fs)
  requires PathExists(fs, path)
  requires forall p | PathExists(fs, p) :: GetMeta(fs, p).MetaData?
  {
    var id := GetMeta(fs, path).id;
    var m := fs.content.meta_map[path];
    && (forall alias | PathExists(fs, alias) && GetMeta(fs, alias).id == id ::
      && (m.MetaData? ==> path == alias)
      && (m.RedirectMeta? ==> m == fs.content.meta_map[alias]))
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
    forall p | PathExists(fs', p)
    ensures GetMeta(fs', p).id.ID?
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    ensures AliasConsistentWithID(fs', p)
    {
      assert AliasConsistentWithID(fs, p); // observe
      if p != RootDir {
        assert PathExists(fs, p); // observe
      }
    }

    forall p | !PathExists(fs', p)
    ensures GetData(fs', p) == EmptyData()
    {
      if p != path {
        assert !PathExists(fs, p);
      } else {
        assert !PathExists(fs', p);
      }
    }

    forall hidden | fs'.hidden.meta_map[hidden].MetaData?
    ensures HasReference(fs', hidden)
    {
      var p :| fs.content.meta_map[p] == RedirectMeta(hidden) && p != path;
      assert fs'.content.meta_map[p] == fs.content.meta_map[p]; // observe
    }

    assert Inv(fs');
  }

  lemma NoValidBeneathDir(fs: FileSys, dir: Path, path: Path)
  requires Inv(fs)
  requires BeneathDir(dir, path)
  requires && fs.content.meta_map[dir].MetaData? 
           && fs.content.meta_map[dir].ftype.Directory? ==> IsEmptyDir(fs, dir)
  ensures !PathExists(fs, path)
  {
    var pdir := GetParentDir(path);
    if pdir != dir {
      NoValidBeneathDir(fs, dir, pdir);
    }
  }

  lemma {:timeLimitMultiplier 2} RenamePreservesReferences(fs: FileSys, fs': FileSys, src: Path, dst: Path, ctime: Time)
  requires Inv(fs)
  requires Rename(fs, fs', src, dst, ctime)
  ensures forall hidden | fs'.hidden.meta_map[hidden].MetaData? :: HasReference(fs', hidden)
  {
    forall hidden | fs'.hidden.meta_map[hidden].MetaData?
    ensures HasReference(fs', hidden)
    {
      var p :| fs.content.meta_map[p] == RedirectMeta(hidden);
      if p == src {
        assert fs'.content.meta_map[dst] == RedirectMeta(hidden); // observe
      } else if BeneathDir(src, p) {
        var p' := dst + p[|src|..];
        assert src + p'[|dst|..] == p; // observe
        assert fs'.content.meta_map[p'] == fs.content.meta_map[p]; // observe
      } else if p == dst {
        var alias :| fs.content.meta_map[alias] == RedirectMeta(hidden) && alias != dst;
        if BeneathDir(src, alias) {
          NoValidBeneathDir(fs, src, alias);
        }
        if BeneathDir(dst, alias) {
          NoValidBeneathDir(fs, dst, alias);
        }
        assert fs'.content.meta_map[alias] == fs.content.meta_map[alias];
      } else if BeneathDir(dst, p) {
        NoValidBeneathDir(fs, dst, p);
      } else if p == GetParentDir(src) || p == GetParentDir(dst) {
        assert HasReference(fs', hidden); 
      } else {
        assert fs'.content.meta_map[p] == fs.content.meta_map[p];
        assert HasReference(fs', hidden);
      }
    }
  }

  lemma {:timeLimitMultiplier 2} RenamePreservesAliases(fs: FileSys, fs': FileSys, src: Path, dst: Path, ctime: Time)
  requires Inv(fs)
  requires Rename(fs, fs', src, dst, ctime)
  requires forall p | PathExists(fs', p) :: GetMeta(fs', p).MetaData?
  ensures forall p | PathExists(fs', p) :: AliasConsistentWithID(fs', p)
  {
    forall p | PathExists(fs', p)
    ensures AliasConsistentWithID(fs', p)
    {
      var id := GetMeta(fs', p).id;
      var m := fs'.content.meta_map[p];

      forall alias | PathExists(fs', alias) && GetMeta(fs', alias).id == id
      ensures m.MetaData? ==> alias == p
      ensures m.RedirectMeta? ==> fs'.content.meta_map[alias] == m
      {
        if p == dst {
          assert AliasConsistentWithID(fs, src); // observe
        } else if BeneathDir(dst, p) {
          var srcpath := src + p[|dst|..];
          assert fs'.content.meta_map[p] == fs.content.meta_map[srcpath];
          assert AliasConsistentWithID(fs, srcpath); // observe

          assert srcpath != dst;
          if BeneathDir(dst, srcpath) {
            NoValidBeneathDir(fs, dst, srcpath);
          }
        } else {
          assert id == GetMeta(fs, p).id;
          assert AliasConsistentWithID(fs, p); // observe
        }
      }
    }
  }

  lemma RenamePreservesInv(fs: FileSys, fs': FileSys, src: Path, dst: Path, ctime: Time)
  requires Inv(fs)
  requires Rename(fs, fs', src, dst, ctime)
  ensures Inv(fs')
  {
    forall p | !PathExists(fs', p)
    ensures GetData(fs', p) == EmptyData()
    {
      if BeneathDir(dst, p) {
        NoValidBeneathDir(fs, dst, p);
        assert !PathExists(fs, p);
      } else if p == src || BeneathDir(src, p) {
        assert !PathExists(fs', p);
      } else {
        assert !PathExists(fs, p);
      }
    }

    forall p | fs'.content.meta_map[p].RedirectMeta?
    ensures ValidHiddenEntry(fs', p)
    {
      if fs.content.meta_map[dst].RedirectMeta? && BeneathDir(dst, p) {
        var srcpath := src + p[|dst|..];
        assert fs'.content.meta_map[p] == fs.content.meta_map[srcpath];
      }
    }

    forall p | PathExists(fs', p)
    ensures GetMeta(fs', p).id.ID?
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    {
      if p != RootDir {
        if p == dst {
          assert ParentDirIsDir(fs', dst);
        } else if BeneathDir(dst, p) {
          var parent_dir := GetParentDir(p);
          var srcpath := src + p[|dst|..];
          assert ParentDirIsDir(fs, srcpath); // observe
          assert src + parent_dir[|dst|..] == GetParentDir(srcpath); // observe
          assert ParentDirIsDir(fs', p);
        } else {
          assert PathExists(fs, p); // observe
        }
      }
    }

    RenamePreservesReferences(fs, fs', src, dst, ctime);
    RenamePreservesAliases(fs, fs', src, dst, ctime);

    assert Inv(fs');
  }

  lemma LinkPreservesInv(fs: FileSys, fs': FileSys, source: Path, dest: Path, ctime: Time, hiddenName: Option<Path>)
  requires Inv(fs)
  requires Link(fs, fs', source, dest, ctime, hiddenName)
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p)
    ensures GetMeta(fs', p).id.ID?
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    ensures AliasConsistentWithID(fs', p)
    {
      if p != dest {
        assert AliasConsistentWithID(fs, p); // observe
        assert PathExists(fs, p); // observe
      }
    }

    forall hidden | fs'.hidden.meta_map[hidden].MetaData?
    ensures HasReference(fs', hidden)
    {
      if hiddenName.Some? && hiddenName.value == hidden {
        assert fs'.content.meta_map[source] == RedirectMeta(hidden); // observe
      } else {
        var p :| fs.content.meta_map[p] == RedirectMeta(hidden);
        assert fs'.content.meta_map[p] == fs.content.meta_map[p]; // observe
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
    forall p | PathExists(fs', p)
    ensures GetMeta(fs', p).id.ID?
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    ensures AliasConsistentWithID(fs', p)
    {
      if p != step.path {
        assert AliasConsistentWithID(fs, p); // observe
        assert PathExists(fs, p); // observe
      }
    }

    forall hidden | fs'.hidden.meta_map[hidden].MetaData?
    ensures HasReference(fs', hidden)
    {
      var p :| fs.content.meta_map[p] == RedirectMeta(hidden);
      assert fs'.content.meta_map[p] == fs.content.meta_map[p]; // observe
    }

    assert Inv(fs');
  }
}
