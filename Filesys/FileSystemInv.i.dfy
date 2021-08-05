// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FileSystem.s.dfy"

module FileSystemInv {
  import opened FileSystem
  import opened FSTypes
  import opened PathSpec

  predicate Inv(fs: FileSys)
  {
    && WF(fs)
    // Nonexistent ids is never occupied
    && fs.meta_map[Nonexistent].EmptyMeta?
    && fs.data_map[Nonexistent] == EmptyData()
    // Directory has no hardlinks
    && (forall path | PathExists(fs, path) :: DirImpliesNoAlias(fs, path))
    // ID consistent
    && (forall path | PathExists(fs, path) :: fs.path_map[path] == fs.meta_map[fs.path_map[path]].id)
    // Path and meta map consistency: directory structure is connected
    && (forall path | PathExists(fs, path) && path != RootDir :: ParentDirIsDir(fs, path))
  }

  lemma InitImpliesInv(fs: FileSys)
  requires Init(fs)
  ensures Inv(fs)
  {
  }

  // TODO: add ui op
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
      case LinkStep(source, dest, ctime) => LinkPreservesInv(fs, fs', source, dest, ctime); 
      case _ => {
        if step.CreateStep? || step.ChangeAttrStep? || step.TruncateStep? 
        || step.WriteStep? || step.UpdateTimeStep? {
          SimpleStepPreservesInv(fs, fs', step);
        }
      }
    }
  }

  /// Invariant proofs

  lemma SameAliases(fs: FileSys, fs': FileSys, changedPaths: iset<Path>, changedIds: iset<ID>)
  requires Inv(fs)
  requires WF(fs')
  requires forall p | p in changedPaths :: fs.path_map[p] in changedIds || fs.path_map[p].Nonexistent?
  requires forall p | p in changedPaths :: fs'.path_map[p] in changedIds || fs'.path_map[p].Nonexistent?
  requires forall p | p !in changedPaths :: fs'.path_map[p] == fs.path_map[p]
  requires forall p | p !in changedPaths :: fs'.path_map[p] !in changedIds
  ensures forall p | PathExists(fs, p) && PathExists(fs', p) && p !in changedPaths ::
    AliasPaths(fs, fs.path_map[p]) == AliasPaths(fs', fs'.path_map[p])
  {
  }

  lemma DeletePreservesInv(fs: FileSys, fs': FileSys, path: Path, ctime: Time)
  requires Inv(fs)
  requires Delete(fs, fs', path, ctime)
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p)
    ensures DirImpliesNoAlias(fs', p)
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    {
      assert DirImpliesNoAlias(fs, p); // observe
      assert p != RootDir ==> ParentDirIsDir(fs, p); // observe
  
      var id := fs.path_map[path];
      if fs'.path_map[p] != id {
        SameAliases(fs, fs', AliasPaths(fs, id), iset{id});
      }
    }

    assert Inv(fs');
  }

  lemma RenamedPathsRemainDifferent(src: Path, dst: Path, p1: Path, p2: Path)
  requires p1 != p2
  requires p1 == dst || BeneathDir(dst, p1)
  requires p2 == dst || BeneathDir(dst, p2)
  ensures src + p1[|dst|..] != src + p2[|dst|..]
  {
    if BeneathDir(dst, p1) && BeneathDir(dst, p2) {
      assert p1[|dst|..] != p2[|dst|..];

      var p1' := src + p1[|dst|..];
      var p2' := src + p2[|dst|..];

      assert p1'[..|src|] == p2'[..|src|];
    }
  }

  lemma RenamePreservesDirImpliesNoAlias(fs: FileSys, fs': FileSys, src: Path, dst: Path, ctime: Time)
  requires Inv(fs)
  requires Rename(fs, fs', src, dst, ctime)
  ensures forall p | PathExists(fs', p) :: DirImpliesNoAlias(fs', p)
  {
    forall p | PathExists(fs', p)
    ensures DirImpliesNoAlias(fs', p)
    {
      var id := fs'.path_map[p];
      var m := fs'.meta_map[id];
      var aliases := AliasPaths(fs', id);

      if (exists path | path in aliases :: path == dst || BeneathDir(dst, path)) {
        // this covers cases for dst prefixes and old src's aliases
        if m.ftype.Directory? && !NoAlias(fs', p) {
          var path :| path in aliases && (path == dst || BeneathDir(dst, path));
          var aliaspath :| aliaspath in aliases && aliaspath != path;
          assert path != aliaspath;

          var srcpath := src + path[|dst|..];
          assert id == fs.path_map[srcpath];
          assert DirImpliesNoAlias(fs, srcpath); // observe

          if aliaspath == dst || BeneathDir(dst, aliaspath) {
            var srcalias := src + aliaspath[|dst|..];
            assert fs.path_map[srcalias] == fs'.path_map[aliaspath];
            RenamedPathsRemainDifferent(src, dst, path, aliaspath);
            assert srcalias != srcpath;
            assert false;
          } else {
            assert fs.path_map[aliaspath] == fs'.path_map[aliaspath]; 
            assert false;
          }
        }
      } else {
        assert DirImpliesNoAlias(fs, p); // observe
        assert DirImpliesNoAlias(fs', p);
      }
    }
  }

  lemma RenamePreservesInv(fs: FileSys, fs': FileSys, src: Path, dst: Path, ctime: Time)
  requires Inv(fs)
  requires Rename(fs, fs', src, dst, ctime)
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p) && p != RootDir
    ensures ParentDirIsDir(fs', p)
    {
      var parent_dir := GetParentDir(p);
      if p == dst {
        assert ParentDirIsDir(fs', p);
      } else if BeneathDir(dst, p) {
        var srcpath := src + p[|dst|..];
        assert PathExists(fs, srcpath); // observe
        assert parent_dir == dst || BeneathDir(dst, parent_dir); // observe
        assert src + parent_dir[|dst|..] == GetParentDir(srcpath); // observe
        assert ParentDirIsDir(fs', p);
      } else {
        assert PathExists(fs, p); // observe
      }
    }

    forall p | PathExists(fs', p)
    ensures fs'.path_map[p] == fs'.meta_map[fs'.path_map[p]].id
    {
      if p == dst {
        assert src + p[|dst|..] == src;
        assert fs'.path_map[p] == fs.path_map[src];
        assert fs'.path_map[p] == fs'.meta_map[fs'.path_map[p]].id;
      } else if BeneathDir(dst, p) {
        assert fs'.path_map[p] == fs'.meta_map[fs'.path_map[p]].id;
      }
    }

    RenamePreservesDirImpliesNoAlias(fs, fs', src, dst, ctime);
    assert Inv(fs');
  }

  lemma LinkPreservesInv(fs: FileSys, fs': FileSys, source: Path, dest: Path, ctime: Time)
  requires Inv(fs)
  requires Link(fs, fs', source, dest, ctime)
  ensures Inv(fs')
  {
    forall p | PathExists(fs', p)
    ensures DirImpliesNoAlias(fs', p)
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    {
      assert p != dest ==> DirImpliesNoAlias(fs, p); // observe
      assert p != RootDir ==> ParentDirIsDir(fs, p); // observe

      var id := fs.path_map[source];
      if fs'.path_map[p] != id {
        SameAliases(fs, fs', AliasPaths(fs', id), iset{id});
      }
    }

    assert Inv(fs');
  }

  lemma SimpleStepPreservesInv(fs: FileSys, fs': FileSys, step: Step)
  requires Inv(fs)
  requires NextStep(fs, fs', step)
  requires step.CreateStep? || step.ChangeAttrStep? || step.TruncateStep? 
    || step.WriteStep? || step.UpdateTimeStep?
  ensures Inv(fs')
  {
    var path := step.path;

    forall p | PathExists(fs', p)
    ensures DirImpliesNoAlias(fs', p)
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    {
      if p != path {
        assert PathExists(fs, p); // observe
        assert DirImpliesNoAlias(fs, p); // observe
        if step.CreateStep? {
          SameAliases(fs, fs', iset{path}, iset{fs'.path_map[path]});
        }
      }
    }

    assert Inv(fs');
  }
}
