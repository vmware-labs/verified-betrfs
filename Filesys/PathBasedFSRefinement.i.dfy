// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FileSystemInv.i.dfy"
include "PathBasedFSInv.i.dfy"
include "../lib/Base/Maps.i.dfy"

module PathBasedFSRefinement {
  import F = FileSystem
  import P = PathBasedFS
  import FInv = FileSystemInv
  import PInv = PathBasedFSInv
  
  import Maps
  import opened Options
  import opened FSTypes
  import opened PathSpec

  /// Interpretation Functions

  function {:opaque} IPathMap(fs: P.FileSys) : (path_map: F.PathMap)
  requires PInv.Inv(fs)
  ensures F.PathMapComplete(path_map)
  {
    imap path :: if P.PathExists(fs, path) then P.GetMeta(fs, path).id else Nonexistent
  }

  function {:opaque} IMetaMap(fs: P.FileSys) : (meta_map: F.MetaView)
  requires PInv.Inv(fs)
  ensures forall id :: id in meta_map
  {
    var path_map := IPathMap(fs);
    reveal_IPathMap();

    imap id : ID :: 
      if id in path_map.Values
      then var p :| p in path_map && path_map[p] == id; P.GetMeta(fs, p)
      else EmptyMeta
  }

  function {:opaque} IDataMap(fs: P.FileSys) : (data_map: F.DataView)
  requires PInv.Inv(fs)
  ensures forall id :: id in data_map
  {
    var path_map := IPathMap(fs);
    reveal_IPathMap();

    imap id : ID :: 
      if id in path_map.Values
      then var p :| p in path_map && path_map[p] == id; P.GetData(fs, p)
      else EmptyData()
  }

  function IStep(step: P.Step) : (i_step: F.Step)
  {
    match step {
      case GetAttrStep(path, attr) => F.GetAttrStep(path, attr)
      case ReadLinkStep(path, link_path) => F.ReadLinkStep(path, link_path)
      case CreateStep(path, m) => F.CreateStep(path, m)
      case DeleteStep(path, ctime) => F.DeleteStep(path, ctime)
      case RenameStep(source, dest, ctime) => F.RenameStep(source, dest, ctime)
      case LinkStep(source, dest, ctime, hiddenName) => F.LinkStep(source, dest, ctime)
      case ChangeAttrStep(path, perm, uid, gid, ctime) => F.ChangeAttrStep(path, perm, uid, gid, ctime)
      case TruncateStep(path, size, time) => F.TruncateStep(path, size, time)
      case ReadStep(path, offset, size, data) => F.ReadStep(path, offset, size, data)
      case WriteStep(path, offset, size, data, time) => F.WriteStep(path, offset, size, data, time)
      case UpdateTimeStep(path, atime, mtime, ctime) => F.UpdateTimeStep(path, atime, mtime, ctime)
      case ReadDirStep(dir, start, results, done) => F.ReadDirStep(dir, start, results, done)
      case _ => F.StutterStep
    }
  }

  function I(fs: P.FileSys) : (i_fs: F.FileSys)
  requires PInv.Inv(fs)
  ensures F.WF(i_fs)
  ensures FInv.Inv(i_fs)
  {
    var i_fs := F.FileSys(IPathMap(fs), IMetaMap(fs), IDataMap(fs));
    assert FInv.Inv(i_fs) by { reveal_IPathMap(); reveal_IMetaMap(); reveal_IDataMap(); }
    i_fs
  }

  /// Refinement Proofs

  lemma GetMetaEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  ensures P.GetMeta(fs, path) == I(fs).meta_map[I(fs).path_map[path]]
  {
    reveal_IPathMap();
    reveal_IMetaMap();
  }

  lemma GetDataEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  ensures P.GetData(fs, path) == I(fs).data_map[I(fs).path_map[path]]
  {
    reveal_IPathMap();
    reveal_IMetaMap();
    reveal_IDataMap();
  }

  lemma ValidNewPathEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  ensures P.ValidNewPath(fs, path) == F.ValidNewPath(I(fs), path)
  {
    reveal_IPathMap();
    reveal_IMetaMap();
  }

  lemma PathExistsEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  ensures P.PathExists(fs, path) == F.PathExists(I(fs), path)
  {
    reveal_IPathMap();
    reveal_IMetaMap();
  }

  lemma IsEmptyDirEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  ensures P.IsEmptyDir(fs, path) == F.IsEmptyDir(I(fs).path_map, path)
  {
    reveal_IPathMap();
    reveal_IMetaMap();
  }

  lemma NoAliasEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  requires P.PathExists(fs, path)
  ensures P.NoAlias(fs, path) == F.NoAlias(I(fs), path)
  {
    reveal_IPathMap();
  }

  lemma RefinesInit(fs: P.FileSys)
  requires P.Init(fs)
  requires PInv.Inv(fs)
  ensures F.Init(I(fs))
  {
    reveal_IPathMap();
    reveal_IMetaMap();
    reveal_IDataMap();

    assert I(fs).path_map[RootDir] == RootID; // observe
  }

  lemma RefinesNext(fs: P.FileSys, fs': P.FileSys)
  requires PInv.Inv(fs)
  requires P.Next(fs, fs')
  ensures PInv.Inv(fs')
  ensures F.Next(I(fs), I(fs'))
  {
    var step :| P.NextStep(fs, fs', step);
    PInv.NextStepPreservesInv(fs, fs', step);
    NextStepRefines(fs, fs', step);
  }

  lemma NextStepRefines(fs: P.FileSys, fs': P.FileSys, step: P.Step)
  requires PInv.Inv(fs)
  requires P.NextStep(fs, fs', step)
  requires PInv.Inv(fs')
  ensures F.NextStep(I(fs), I(fs'), IStep(step))
  {
    var i_step := IStep(step);
    match step {
      case GetAttrStep(path, ctime) => RefinesGetAttr(fs, fs', path, ctime);
      case ReadLinkStep(path, link_path) => RefinesReadLink(fs, fs', path, link_path);
      case CreateStep(path, m) => RefinesCreate(fs, fs', path, m);
      case DeleteStep(path, ctime) => RefinesDelete(fs, fs', path, ctime);
      case RenameStep(source, dest, ctime) => {
        assert i_step == F.RenameStep(source, dest, ctime); // observe
        RefinesRename(fs, fs', source, dest, ctime);
      } 
      case LinkStep(source, dest, ctime, hiddenName) => {
        assert i_step == F.LinkStep(source, dest, ctime); // observe
        RefinesLink(fs, fs', source, dest, ctime, hiddenName);
      }
      case ChangeAttrStep(path, perm, uid, gid, ctime) => RefinesChangeAttr(fs, fs', path, perm, uid, gid, ctime);
      case TruncateStep(path, size, time) => RefinesTruncate(fs, fs', path, size, time);
      case ReadStep(path, offset, size, data) => RefinesRead(fs, fs', path, offset, size, data);
      case WriteStep(path, offset, size, data, time) => RefinesWrite(fs, fs', path, offset, size, data, time);
      case UpdateTimeStep(path, atime, mtime, ctime) => RefinesUpdateTime(fs, fs', path, atime, mtime, ctime);
      case ReadDirStep(dir, start, results, done) => RefinesReadDir(fs, fs', dir, start, results, done);
      case _ => {}
    }
  }

  lemma RefinesGetAttr(fs: P.FileSys, fs': P.FileSys, path: Path, attr: MetaData)
  requires PInv.Inv(fs)
  requires P.GetAttr(fs, fs', path, attr)
  ensures F.GetAttr(I(fs), I(fs'), path, attr)
  {
    GetMetaEquiv(fs, path);
  }

  lemma RefinesReadLink(fs: P.FileSys, fs': P.FileSys, path: Path, link_path: Path)
  requires PInv.Inv(fs)
  requires P.ReadLink(fs, fs', path, link_path)
  ensures F.ReadLink(I(fs), I(fs'), path, link_path)
  {
    GetMetaEquiv(fs, path);
  }

  lemma GetPathFromID(fs: P.FileSys, id: ID) returns (path: Path)
  requires PInv.Inv(fs)
  requires id.ID? && id in I(fs).path_map.Values
  ensures P.PathExists(fs, path)
  ensures P.GetMeta(fs, path).id == id
  ensures I(fs).path_map[path] == id
  {
    reveal_IPathMap();
    path :| P.PathExists(fs, path) && P.GetMeta(fs, path).id == id;
    GetMetaEquiv(fs, path);
  }

  lemma RefinesCreate(fs: P.FileSys, fs': P.FileSys, path: Path, m: MetaData)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Create(fs, fs', path, m)
  ensures F.Create(I(fs), I(fs'), path, m)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');
    var parent_dir := GetParentDir(path);
    var parent_id := P.GetMeta(fs, parent_dir).id;
    var parent_m' := F.UpdateParentTime(i_fs, parent_id, m.mtime);

    assert !P.PathExists(fs, path);
    assert i_fs'.path_map == i_fs.path_map[path := m.id] by { reveal_IPathMap(); }
    assert m.id !in i_fs.path_map.Values by { reveal_IPathMap(); }
    assert parent_id == i_fs.path_map[parent_dir] by { reveal_IPathMap(); }

    assert i_fs.meta_map[m.id].EmptyMeta? by { reveal_IMetaMap(); }
    assert i_fs.data_map[m.id] == P.GetData(fs, path) == EmptyData() by { reveal_IDataMap(); }

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[m.id := m][parent_id := parent_m'][id]
    ensures i_fs'.data_map[id] == i_fs.data_map[id]
    {
      if id == Nonexistent {
      } else if id in i_fs.path_map.Values {
        var p := GetPathFromID(fs, id);
        GetMetaEquiv(fs, p);
        GetMetaEquiv(fs', p);
        GetDataEquiv(fs, p);
        GetDataEquiv(fs', p);
      } else {
        if id == m.id {
          GetMetaEquiv(fs', path);
        } else {
          assert i_fs'.meta_map[id] == i_fs.meta_map[id] by { reveal_IMetaMap(); }
        }
        assert i_fs.data_map[id] == EmptyData() by { reveal_IDataMap(); }
        assert i_fs'.data_map[id] == EmptyData() by { reveal_IDataMap(); }
      }
    }

    Maps.IMapEquivalent(i_fs'.meta_map, i_fs.meta_map[m.id := m][parent_id := parent_m']);
    Maps.IMapEquivalent(i_fs'.data_map, i_fs.data_map);

    ValidNewPathEquiv(fs, path);
    assert F.Create(i_fs, i_fs', path, m);
  }

  lemma RefinesDelete(fs: P.FileSys, fs': P.FileSys, path: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Delete(fs, fs', path, ctime)
  ensures F.Delete(I(fs), I(fs'), path, ctime)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');

    var path_id := P.GetMeta(fs, path).id;
    var m := fs.content.meta_map[path];
    var m' := F.MetaDataDelete(i_fs, path, ctime);

    var parent_dir := GetParentDir(path);
    var parent_id := P.GetMeta(fs, parent_dir).id;
    var parent_m' := F.UpdateParentTime(i_fs, parent_id, ctime);

    assert path_id == i_fs.path_map[path] by { reveal_IPathMap(); }
    assert parent_id == i_fs.path_map[parent_dir] by { reveal_IPathMap(); }

    PathExistsEquiv(fs, path);
    GetMetaEquiv(fs, path);
    IsEmptyDirEquiv(fs, path);

    forall p 
    ensures i_fs'.path_map[p] == i_fs.path_map[path := Nonexistent][p]
    {
      reveal_IPathMap();
      if p != path && p != parent_dir {
        assert fs'.content.meta_map[p] == fs.content.meta_map[p];
        if m.RedirectMeta? && fs.content.meta_map[p] == RedirectMeta(m.source) {
          assert fs.hidden.meta_map[m.source].id == fs'.hidden.meta_map[m.source].id;
        }
      }
    }
    Maps.IMapEquivalent(i_fs'.path_map, i_fs.path_map[path := Nonexistent]);

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[path_id := m'][parent_id := parent_m'][id]
    ensures i_fs'.data_map[id] == i_fs.data_map[path_id := F.DataDelete(i_fs, path)][id]
    {
      if id == Nonexistent {
      } else if id in i_fs.path_map.Values {
        NoAliasEquiv(fs, path);
        if id == path_id && P.NoAlias(fs, path) {
          assert id !in i_fs'.path_map.Values;
          assert i_fs'.meta_map[id] == EmptyMeta by { reveal_IMetaMap(); }
          assert i_fs'.data_map[id] == EmptyData() by { reveal_IDataMap(); }
        } else {
          assert exists p :: P.PathExists(fs, p) && P.GetMeta(fs, p).id == id && p != path by { reveal_IPathMap(); }
          var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == id && p != path;
          assert i_fs'.path_map[p] == id by { reveal_IPathMap(); }
          GetMetaEquiv(fs, p);
          GetMetaEquiv(fs', p);
          GetDataEquiv(fs, p);
          GetDataEquiv(fs', p);
        }
      } else {
        assert i_fs'.meta_map[id] == i_fs.meta_map[id] by { reveal_IMetaMap(); }
        assert i_fs'.data_map[id] == i_fs.data_map[id] by { reveal_IDataMap(); }
      }
    }

    Maps.IMapEquivalent(i_fs'.meta_map, i_fs.meta_map[path_id := m'][parent_id := parent_m']);
    Maps.IMapEquivalent(i_fs'.data_map, i_fs.data_map[path_id := F.DataDelete(i_fs, path)]);

    assert i_fs'.meta_map == i_fs.meta_map[path_id := m'][parent_id := parent_m'];
    assert i_fs'.data_map == i_fs.data_map[path_id := F.DataDelete(i_fs, path)];
    assert F.Delete(i_fs, i_fs', path, ctime);
  }

  lemma RefinesRenamePathMap(fs: P.FileSys, fs': P.FileSys, src: Path, dst: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Rename(fs, fs', src, dst, ctime)
  requires dst != RootDir
  ensures I(fs').path_map == F.PathMapRename(I(fs), src, dst)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');
    var src_id := P.GetMeta(fs, src).id;

    forall path
    ensures i_fs'.path_map[path] == F.PathMapRename(i_fs, src, dst)[path]
    {
      reveal_IPathMap();
      if path == dst {
        assert src + path[|dst|..] == src;
        assert i_fs.path_map[src] == src_id;
        assert i_fs'.path_map[path] == src_id;
        assert F.PathMapRename(i_fs, src, dst)[dst] == i_fs.path_map[src];
      } else if BeneathDir(dst, path) {
        var srcpath := src + path[|dst|..];
        assert fs'.content.meta_map[path] == fs.content.meta_map[srcpath];
      } else if path == src || BeneathDir(src, path) {
        assert P.GetMeta(fs', path) == EmptyMeta;
        assert i_fs'.path_map[path] == Nonexistent; 
      } else if path == GetParentDir(src) || path == GetParentDir(dst) {
        assert fs'.content.meta_map[path] == P.UpdatePathTime(fs.content, path, ctime);
        assert fs'.content.meta_map[path].id == fs.content.meta_map[path].id;
      }
    }
    Maps.IMapEquivalent(i_fs'.path_map, F.PathMapRename(i_fs, src, dst));
  }

  lemma RefinesRenameDstID(fs: P.FileSys, fs': P.FileSys, src: Path, dst: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Rename(fs, fs', src, dst, ctime)
  requires dst != RootDir
  requires P.PathExists(fs, dst)
  requires I(fs').path_map == F.PathMapRename(I(fs), src, dst)
  ensures I(fs').meta_map[P.GetMeta(fs, dst).id] == F.MetaMapRename(I(fs), src, dst, ctime)[P.GetMeta(fs, dst).id]
  ensures I(fs').data_map[P.GetMeta(fs, dst).id] == I(fs).data_map[P.GetMeta(fs, dst).id := F.DataDelete(I(fs), dst)][P.GetMeta(fs, dst).id]
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');

    var src_id := P.GetMeta(fs, src).id;
    var dst_id := P.GetMeta(fs, dst).id;
    var src_parent_id := P.GetMeta(fs, GetParentDir(src)).id;
    var dst_parent_id := P.GetMeta(fs, GetParentDir(dst)).id;

    assert src_id == i_fs.path_map[src] by { reveal_IPathMap(); }
    assert dst_id == i_fs.path_map[dst] by { reveal_IPathMap(); }
    assert src_parent_id == i_fs.path_map[GetParentDir(src)] by { reveal_IPathMap(); }    
    assert dst_parent_id == i_fs.path_map[GetParentDir(dst)] by { reveal_IPathMap(); }

    NoAliasEquiv(fs, dst);
    if P.NoAlias(fs, dst) {
      assert dst_id !in i_fs'.path_map.Values; // observe
      assert i_fs'.meta_map[dst_id] == EmptyMeta by { reveal_IMetaMap(); }
      assert i_fs'.data_map[dst_id] == EmptyData() by { reveal_IDataMap(); }
    } else {
      assert exists p :: P.PathExists(fs, p) && P.GetMeta(fs, p).id == dst_id by { reveal_IPathMap(); }
      var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == dst_id && p != dst;
      assert i_fs.path_map[p] == dst_id by { reveal_IPathMap(); }

      GetMetaEquiv(fs, dst);
      assert !BeneathDir(dst, p) by {
        if BeneathDir(dst, p) {
          PInv.NoValidBeneathDir(fs, dst, p);
        }
      }

      var newpath := p;
      if BeneathDir(src, p) {
        newpath := dst + p[|src|..];
        assert p == src + newpath[|dst|..];
      }
      GetMetaEquiv(fs', newpath);
      GetDataEquiv(fs', newpath);
      GetDataEquiv(fs, p);
    }
  }

  lemma {:timeLimitMultiplier 2} RefinesRenameMetaMap(fs: P.FileSys, fs': P.FileSys, src: Path, dst: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Rename(fs, fs', src, dst, ctime)
  requires dst != RootDir
  requires I(fs').path_map == F.PathMapRename(I(fs), src, dst)
  ensures I(fs').meta_map == F.MetaMapRename(I(fs), src, dst, ctime)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');

    var src_id := P.GetMeta(fs, src).id;
    var dst_id := if P.PathExists(fs, dst) then P.GetMeta(fs, dst).id else Nonexistent;
    var src_parent_id := P.GetMeta(fs, GetParentDir(src)).id;
    var dst_parent_id := P.GetMeta(fs, GetParentDir(dst)).id;

    assert src_id == i_fs.path_map[src] by { reveal_IPathMap(); } 
    assert src_id == i_fs'.path_map[dst] by { reveal_IPathMap(); }
    assert dst_id == i_fs.path_map[dst] by { reveal_IPathMap(); }
    assert src_parent_id == i_fs.path_map[GetParentDir(src)] by { reveal_IPathMap(); }
    assert dst_parent_id == i_fs.path_map[GetParentDir(dst)] by { reveal_IPathMap(); }

    assert !BeneathDir(dst, GetParentDir(src)) by {
       if BeneathDir(dst, GetParentDir(src)) {
        PInv.NoValidBeneathDir(fs, dst, GetParentDir(src));
      }
    }

    GetMetaEquiv(fs, src);
    GetMetaEquiv(fs, GetParentDir(src));
    GetMetaEquiv(fs, GetParentDir(dst));

    forall id
    ensures i_fs'.meta_map[id] == F.MetaMapRename(i_fs, src, dst, ctime)[id]
    {
      if id == Nonexistent {
        assert FInv.Inv(i_fs);
        assert FInv.Inv(i_fs');
      } else if id in i_fs.path_map.Values {
        if id == src_id {
          GetMetaEquiv(fs', dst);
        } else if id == dst_id {
          RefinesRenameDstID(fs, fs', src, dst, ctime);
        } else if id == src_parent_id || id == dst_parent_id {
          var p := if id == src_parent_id then GetParentDir(src) else GetParentDir(dst);
          assert i_fs.path_map[p] == i_fs'.path_map[p];
          GetMetaEquiv(fs', p);
        } else {
          var p := GetPathFromID(fs, id);
          if BeneathDir(dst, p) {
            PInv.NoValidBeneathDir(fs, dst, p);
            assert false;
          } else {
            var newpath := p;
            if BeneathDir(src, p) {
              newpath := dst + p[|src|..];
              assert BeneathDir(dst, newpath);
              assert p == src + newpath[|dst|..];
            }
            assert P.GetMeta(fs, p) == P.GetMeta(fs', newpath);
            GetMetaEquiv(fs, p);
            GetMetaEquiv(fs', newpath);
          }
        }
      } else {
        assert id !in i_fs'.path_map.Values; // observe
        reveal_IMetaMap();
      }
    }
    Maps.IMapEquivalent(i_fs'.meta_map, F.MetaMapRename(i_fs, src, dst, ctime));
  }

  lemma RefinesRenameDataMap(fs: P.FileSys, fs': P.FileSys, src: Path, dst: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Rename(fs, fs', src, dst, ctime)
  requires dst != RootDir
  requires I(fs').path_map == F.PathMapRename(I(fs), src, dst)
  requires I(fs').meta_map == F.MetaMapRename(I(fs), src, dst, ctime)
  ensures I(fs').data_map == I(fs).data_map[I(fs).path_map[dst] := F.DataDelete(I(fs), dst)]
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');

    var dst_id := if P.PathExists(fs, dst) then P.GetMeta(fs, dst).id else Nonexistent;
    assert dst_id == i_fs.path_map[dst] by { reveal_IPathMap(); }

    forall id
    ensures i_fs'.data_map[id] == i_fs.data_map[dst_id := F.DataDelete(i_fs, dst)][id]
    {
      if id == Nonexistent {
      }  else if id in i_fs.path_map.Values {
        if id == dst_id {
          RefinesRenameDstID(fs, fs', src, dst, ctime);
        } else {
          var p := GetPathFromID(fs, id);
          if BeneathDir(dst, p) {
            PInv.NoValidBeneathDir(fs, dst, p);
          } else if p == src || BeneathDir(src, p) {
            var newpath := dst + p[|src|..];
            assert p == src + newpath[|dst|..];
            assert i_fs'.path_map[newpath] == i_fs.path_map[p];
            GetDataEquiv(fs, p);
            GetDataEquiv(fs', newpath);
          } else {
            assert i_fs'.path_map[p] == i_fs.path_map[p]; // observe
            GetDataEquiv(fs, p);
            GetDataEquiv(fs', p);
          }
        }
      } else {
        assert id !in i_fs'.path_map.Values; // observe
        assert i_fs.data_map[id] == EmptyData() by { reveal_IDataMap(); }
        assert i_fs'.data_map[id] == EmptyData() by { reveal_IDataMap(); }
      }
    }
    Maps.IMapEquivalent(i_fs'.data_map, i_fs.data_map[dst_id := F.DataDelete(i_fs, dst)]);
  }

  lemma {:timeLimitMultiplier 2} RefinesRename(fs: P.FileSys, fs': P.FileSys, src: Path, dst: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Rename(fs, fs', src, dst, ctime)
  ensures F.Rename(I(fs), I(fs'), src, dst, ctime)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');

    var dst_id := if P.PathExists(fs, dst) then P.GetMeta(fs, dst).id else Nonexistent;
    assert dst_id == i_fs.path_map[dst] by { reveal_IPathMap(); }

    if dst == RootDir {
      PInv.NoValidBeneathDir(fs, dst, src);
      assert false;
    }

    RefinesRenamePathMap(fs, fs', src, dst, ctime);
    RefinesRenameMetaMap(fs, fs', src, dst, ctime);
    RefinesRenameDataMap(fs, fs', src, dst, ctime);

    PathExistsEquiv(fs, src);   
    PathExistsEquiv(fs, dst);
    ValidNewPathEquiv(fs, dst);

    GetMetaEquiv(fs, src);
    GetMetaEquiv(fs, dst);
    IsEmptyDirEquiv(fs, dst);

    assert F.Rename(i_fs, i_fs', src, dst, ctime);
  }

  lemma {:timeLimitMultiplier 3} RefinesLink(fs: P.FileSys, fs': P.FileSys, source: Path, dest: Path, ctime: Time, hiddenName: Option<Path>)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Link(fs, fs', source, dest, ctime, hiddenName)
  ensures F.Link(I(fs), I(fs'), source, dest, ctime)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');

    GetMetaEquiv(fs, source);
    PathExistsEquiv(fs, source);
    ValidNewPathEquiv(fs, dest);

    var src_id := P.GetMeta(fs, source).id;
    var m := fs.content.meta_map[source];
    var m' := F.MetaDataUpdateCTime(i_fs.meta_map[i_fs.path_map[source]], ctime);

    var dparent_dir := GetParentDir(dest);
    var dparent_id := P.GetMeta(fs, dparent_dir).id;
    var dparent_m' := F.UpdateParentTime(i_fs, dparent_id, ctime);

    assert src_id == i_fs.path_map[source] by { reveal_IPathMap(); }
    assert dparent_id == i_fs.path_map[dparent_dir] by { reveal_IPathMap(); }

    forall p
    ensures i_fs'.path_map[p] == i_fs.path_map[dest := src_id][p]
    {
      reveal_IPathMap();
      if p != dest && p != dparent_dir && p != source {
        assert fs'.content.meta_map[p] == fs.content.meta_map[p];
      }
    }
    Maps.IMapEquivalent(i_fs'.path_map, i_fs.path_map[dest := src_id]);
    assert i_fs'.path_map == i_fs.path_map[dest := src_id];

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[src_id := m'][dparent_id := dparent_m'][id]
    ensures i_fs'.data_map[id] == i_fs.data_map[id]
    {
      if id == Nonexistent {
      } else if id in i_fs.path_map.Values {
        var p := GetPathFromID(fs, id);
        GetMetaEquiv(fs, p);
        GetMetaEquiv(fs', p);
        GetDataEquiv(fs, p);
        GetDataEquiv(fs', p);
      } else {
        assert i_fs'.meta_map[id] == i_fs.meta_map[id] by { reveal_IMetaMap(); }
        assert i_fs'.data_map[id] == i_fs.data_map[id] by { reveal_IDataMap(); }
      }
    }
    Maps.IMapEquivalent(i_fs'.meta_map, i_fs.meta_map[src_id := m'][dparent_id := dparent_m']);
    Maps.IMapEquivalent(i_fs'.data_map, i_fs.data_map);
    assert i_fs'.data_map == i_fs.data_map;
    assert F.Link(i_fs, i_fs', source, dest, ctime);
  }

  lemma RefinesChangeAttr(fs: P.FileSys, fs': P.FileSys, path: Path, perm: int, uid: int, gid: int, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.ChangeAttr(fs, fs', path, perm, uid, gid, ctime)
  ensures F.ChangeAttr(I(fs), I(fs'), path, perm, uid, gid, ctime)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');
    var path_id := P.GetMeta(fs, path).id;

    PathExistsEquiv(fs, path);
    assert i_fs.path_map[path] == path_id by { reveal_IPathMap(); }
    assert i_fs'.path_map == i_fs.path_map by { reveal_IPathMap(); }
    assert i_fs'.data_map == i_fs.data_map by { reveal_IDataMap(); }

    var m' :=  F.MetaDataChangeAttr(i_fs.meta_map[path_id], perm, uid, gid, ctime);

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[path_id := m'][id]
    {
      if id == Nonexistent {
      } else if id in i_fs.path_map.Values {
        var p := GetPathFromID(fs, id);
        GetMetaEquiv(fs, p);
        GetMetaEquiv(fs', p);
      } else {
        assert i_fs'.meta_map[id] == i_fs.meta_map[id] by { reveal_IMetaMap(); }
      }
    }
  }

  lemma RefinesTruncate(fs: P.FileSys, fs': P.FileSys, path: Path, size: int, time: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Truncate(fs, fs', path, size, time)
  ensures F.Truncate(I(fs), I(fs'),  path, size, time)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');
    var path_id := P.GetMeta(fs, path).id;

    GetMetaEquiv(fs, path);
    PathExistsEquiv(fs, path);
    assert i_fs.path_map[path] == path_id by { reveal_IPathMap(); }
    assert i_fs'.path_map == i_fs.path_map by { reveal_IPathMap(); }

    var m := P.GetMeta(fs, path);
    var m' := F.MetaDataUpdateTime(m, m.atime, time, time);
    var d' := F.DataTruncate(i_fs.data_map[path_id], size);

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[path_id := m'][id]
    ensures i_fs'.data_map[id] == i_fs.data_map[path_id := d'][id]
    {
      if id == Nonexistent {
      } else if id in i_fs.path_map.Values {
        var p := GetPathFromID(fs, id);
        GetMetaEquiv(fs, p);
        GetMetaEquiv(fs', p);
        GetDataEquiv(fs, p);
        GetDataEquiv(fs', p);
      } else {
        assert i_fs'.meta_map[id] == i_fs.meta_map[id] by { reveal_IMetaMap(); }
        assert i_fs'.data_map[id] == i_fs.data_map[id] by { reveal_IDataMap(); }
      }
    }
  }

  lemma RefinesRead(fs: P.FileSys, fs': P.FileSys, path: Path, offset: int, size: int, data: Data)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Read(fs, fs', path, offset, size, data)
  ensures F.Read(I(fs), I(fs'), path, offset, size, data)
  {
    reveal_IPathMap();
    reveal_IMetaMap();
    reveal_IDataMap();
  }

  lemma RefinesWrite(fs: P.FileSys, fs': P.FileSys, path: Path, offset: int, size: int, data: Data, time: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Write(fs, fs', path, offset, size, data, time)
  ensures F.Write(I(fs), I(fs'), path, offset, size, data, time)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');
    var path_id := P.GetMeta(fs, path).id;

    GetMetaEquiv(fs, path);
    GetDataEquiv(fs, path);
    PathExistsEquiv(fs, path);
    assert i_fs.path_map[path] == path_id by { reveal_IPathMap(); }
    assert i_fs'.path_map == i_fs.path_map by { reveal_IPathMap(); }

    var m := P.GetMeta(fs, path);
    var m' := F.MetaDataUpdateTime(m, time, time, time);
    var d' := F.DataWrite(i_fs.data_map[path_id], data, offset, size);

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[path_id := m'][id]
    ensures i_fs'.data_map[id] == i_fs.data_map[path_id := d'][id]
    {
      if id == Nonexistent {
      } else if id in i_fs.path_map.Values {
        var p := GetPathFromID(fs, id);
        GetMetaEquiv(fs, p);
        GetMetaEquiv(fs', p);
        GetDataEquiv(fs, p);
        GetDataEquiv(fs', p);
      } else {
        assert i_fs'.meta_map[id] == i_fs.meta_map[id] by { reveal_IMetaMap(); }
        assert i_fs'.data_map[id] == i_fs.data_map[id] by { reveal_IDataMap(); }
      }
    }
  }

  lemma RefinesUpdateTime(fs: P.FileSys, fs': P.FileSys, path: Path, atime: Time, mtime: Time, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.UpdateTime(fs, fs', path, atime, mtime, ctime)
  ensures F.UpdateTime(I(fs), I(fs'), path, atime, mtime, ctime)
  {
    var i_fs := I(fs);
    var i_fs' := I(fs');
    var path_id := P.GetMeta(fs, path).id;

    GetMetaEquiv(fs, path);
    PathExistsEquiv(fs, path);
    assert i_fs.path_map[path] == path_id by { reveal_IPathMap(); }
    assert i_fs'.path_map == i_fs.path_map by { reveal_IPathMap(); }
    assert i_fs'.data_map == i_fs.data_map by { reveal_IDataMap(); }

    var m' := F.MetaDataUpdateTime(i_fs.meta_map[path_id], atime, mtime, ctime);

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[path_id := m'][id]
    {
      if id == Nonexistent {
      } else if id in i_fs.path_map.Values {
        var p := GetPathFromID(fs, id);
        GetMetaEquiv(fs, p);
        GetMetaEquiv(fs', p);
        GetDataEquiv(fs, p);
        GetDataEquiv(fs', p);
      } else {
        assert i_fs'.meta_map[id] == i_fs.meta_map[id] by { reveal_IMetaMap(); }
        assert i_fs'.data_map[id] == i_fs.data_map[id] by { reveal_IDataMap(); }
      }
    }
  }

  lemma RefinesReadDir(fs: P.FileSys, fs': P.FileSys, dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.ReadDir(fs, fs', dir, start, results, done)
  ensures F.ReadDir(I(fs), I(fs'), dir, start, results, done)
  {
    reveal_IPathMap();
    reveal_IMetaMap();
  }

}
