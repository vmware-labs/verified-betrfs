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
  // ensures forall p :: path_map[p] == if P.PathExists(fs, p) then P.GetMeta(fs, p).id else Nonexistent
  {
    imap path :: if P.PathExists(fs, path) then P.GetMeta(fs, path).id else Nonexistent
  }

  function {:opaque} IMetaMap(fs: P.FileSys) : (meta_map: F.MetaView)
  requires PInv.Inv(fs)
  ensures forall id :: id in meta_map
  // ensures forall id | id !in IPathMap(fs).Values :: meta_map[id] == EmptyMeta
  // ensures forall p :: meta_map[IPathMap(fs)[p]] == P.GetMeta(fs, p)
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
  // ensures forall id | id !in IPathMap(fs).Values :: data_map[id] == EmptyData()
  // ensures forall p :: data_map[IPathMap(fs)[p]] == P.GetData(fs, p)
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

  // TODO: comment out
  // lemma InvImpliesInv(fs: P.FileSys)
  // requires PInv.Inv(fs)
  // ensures FInv.Inv(I(fs))
  // {
  // }

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

  lemma NoAliasEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  requires P.PathExists(fs, path)
  ensures P.NoAlias(fs, path) == F.NoAlias(I(fs), path)
  {
    reveal_IPathMap();
  }

  // lemma PathExists

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

  // maybe before fixing all of these proof we should check if rename does work like this.
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
    var parent_m' := P.UpdatePathTime(fs.content, parent_dir, m.mtime);

    reveal_IPathMap();

    assert !P.PathExists(fs, path);
    assert i_fs'.path_map == i_fs.path_map[path := m.id];

    reveal_IMetaMap();
    reveal_IDataMap();

    assert i_fs.meta_map[m.id].EmptyMeta?;
    assert i_fs.data_map[m.id] == P.GetData(fs, path) == EmptyData();

    forall id 
    ensures i_fs'.meta_map[id] == i_fs.meta_map[m.id := m][parent_id := parent_m'][id]
    ensures i_fs'.data_map[id] == i_fs.data_map[id]
    {

      if id in i_fs.path_map.Values {
        if id == parent_id {
                  assume false;

          calc {
            i_fs.meta_map[m.id := m][parent_id := parent_m'][id];
            P.GetMeta(fs', parent_dir);
            i_fs'.meta_map[parent_id];
          }
          calc {
            i_fs'.data_map[parent_id];
            P.GetData(fs', parent_dir);
            P.GetData(fs, parent_dir);
            i_fs.data_map[parent_id];
          }
        } else {

          if exists p :: P.PathExists(fs, p) && P.GetMeta(fs, p).id == id {
                              assume false;

            var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == id;
            calc {
              i_fs.meta_map[id];
              P.GetMeta(fs, p);
              P.GetMeta(fs', p);
              i_fs.meta_map[id];
              i_fs.meta_map[m.id := m][parent_id := parent_m'][id];
            }
            calc {
              i_fs'.data_map[id];
              P.GetData(fs', p);
              P.GetData(fs, p);
              i_fs.data_map[id];
            }
          }
          
          // else {
          //   assert id.Nonexistent?;
          // }
        }
      } else {
        assume false;
        if id == m.id {
          calc {
            i_fs'.meta_map[id];
            P.GetMeta(fs', path);
            i_fs.meta_map[m.id := m][parent_id := parent_m'][id];
          }
        } else {
          calc {
            i_fs'.meta_map[id];
            i_fs.meta_map[id];
            i_fs.meta_map[m.id := m][parent_id := parent_m'][id];
          }
        }
        assert i_fs.data_map[id] == EmptyData();
        assert i_fs'.data_map[id] == EmptyData();
      }
    }

    Maps.IMapEquivalent(i_fs'.meta_map, i_fs.meta_map[m.id := m][parent_id := parent_m']);
    Maps.IMapEquivalent(i_fs'.data_map, i_fs.data_map);
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
    var parent_m' := P.UpdatePathTime(fs.content, parent_dir, ctime);

    forall p 
    ensures i_fs'.path_map[p] == i_fs.path_map[path := Nonexistent][p]
    {
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
        // InvImpliesInv(fs);
        // InvImpliesInv(fs');
      } else if id in i_fs.path_map.Values {
        if id == parent_id {
          assert i_fs.path_map[parent_dir] == i_fs'.path_map[parent_dir];
          calc {
            i_fs.meta_map[path_id := m'][parent_id := parent_m'][id];
            parent_m';
            P.GetMeta(fs', parent_dir);
            i_fs'.meta_map[parent_id];
          }
          calc {
            i_fs'.data_map[parent_id];
            P.GetData(fs', parent_dir);
            P.GetData(fs, parent_dir);
            i_fs.data_map[path_id := F.DataDelete(i_fs, path)][id];
          }
        } else if id == path_id {
          if P.NoAlias(fs, path) {
            assert m' == EmptyMeta;
          } else {
            var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == id && p != path;
            assert P.PathExists(fs', p); // observe
          }
        } else {
          var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == id;
          calc {
            i_fs'.data_map[id];
            P.GetData(fs', p);
            P.GetData(fs, p);
            i_fs.data_map[path_id := F.DataDelete(i_fs, path)][id];
          }
          calc {
            i_fs.meta_map[id];
            P.GetMeta(fs, p);
            P.GetMeta(fs', p);
            i_fs.meta_map[id];
            i_fs.meta_map[path_id := m'][parent_id := parent_m'][id];
          }
        }
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

    var src_m := P.GetMeta(fs, src);
    var src_id := P.GetMeta(fs, src).id;
    var dst_m := P.GetMeta(fs, dst);

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

  lemma meow(fs: P.FileSys, fs': P.FileSys, src: Path, dst: Path, ctime: Time)
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

    var dst_id := P.GetMeta(fs, dst).id;
    assert dst_id == i_fs.path_map[dst] by { reveal_IPathMap(); }

    var src_id := P.GetMeta(fs, src).id;
    assert src_id == i_fs.path_map[src] by { reveal_IPathMap(); }

    var src_parent_dir := GetParentDir(src);
    var src_parent_id := P.GetMeta(fs, src_parent_dir).id;
    assert src_parent_id == i_fs.path_map[src_parent_dir] by { reveal_IPathMap(); }

    var dst_parent_dir := GetParentDir(dst);
    var dst_parent_id := P.GetMeta(fs, dst_parent_dir).id;
    assert dst_parent_id == i_fs.path_map[dst_parent_dir] by { reveal_IPathMap(); }

    assert dst_id != src_id;
    assert dst_id != src_parent_id;
    assert dst_id != dst_parent_id;

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
      assert F.MetaMapRename(i_fs, src, dst, ctime)[dst_id] == F.MetaDataDelete(i_fs, dst, ctime);
      assert F.MetaMapRename(i_fs, src, dst, ctime)[dst_id] == F.MetaDataUpdateCTime(i_fs.meta_map[dst_id], ctime);

      var dst_m := fs.content.meta_map[dst];
      assert dst_m.RedirectMeta?;
      assert fs.content.meta_map[p] == dst_m;
      
      assert p != dst;
      assert p != src;
      assert !BeneathDir(dst, p) by {
        if BeneathDir(dst, p) {
          PInv.NoValidBeneathDir(fs, dst, p);
        }
      }

      if BeneathDir(src, p) {
        var dstpath := dst + p[|src|..];
        assert p == src + dstpath[|dst|..];
        assert i_fs'.path_map[dstpath] == i_fs.path_map[p];
        assert i_fs'.path_map[dstpath] == dst_id;
        GetMetaEquiv(fs, p);
        GetMetaEquiv(fs', dstpath);
        GetDataEquiv(fs, p);
        GetDataEquiv(fs', dstpath);
      } else {
        assert i_fs'.path_map[p] == dst_id;
        assert fs'.content.meta_map[p] == dst_m;
        GetMetaEquiv(fs', p);
        GetDataEquiv(fs, p);
        GetDataEquiv(fs', p);
      }
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
    var src_m := P.GetMeta(fs, src);
    var src_m' := P.MetaDataUpdateTime(src_m, src_m.atime, src_m.mtime, ctime);
    assert src_id == i_fs.path_map[src] by { reveal_IPathMap(); }
    GetMetaEquiv(fs, src);

    var dst_id := if P.PathExists(fs, dst) then P.GetMeta(fs, dst).id else Nonexistent;
    assert dst_id == i_fs.path_map[dst] by { reveal_IPathMap(); }
    assert src_id == i_fs'.path_map[dst] by { reveal_IPathMap(); }

    var src_parent_dir := GetParentDir(src);
    var src_parent_id := P.GetMeta(fs, src_parent_dir).id;
    assert src_parent_id == i_fs.path_map[src_parent_dir] by { reveal_IPathMap(); }
    assert !BeneathDir(dst, src_parent_dir) by {
       if BeneathDir(dst, src_parent_dir) {
        PInv.NoValidBeneathDir(fs, dst, src_parent_dir);
      }
    }
    GetMetaEquiv(fs, src_parent_dir);

    var dst_parent_dir := GetParentDir(dst);
    var dst_parent_id := P.GetMeta(fs, dst_parent_dir).id;
    assert dst_parent_id == i_fs.path_map[dst_parent_dir] by { reveal_IPathMap(); }
    GetMetaEquiv(fs, dst_parent_dir);

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
          meow(fs, fs', src, dst, ctime);
        } else if id == src_parent_id {
          assert i_fs.path_map[src_parent_dir] == i_fs'.path_map[src_parent_dir];
          GetMetaEquiv(fs', src_parent_dir);
        } else if id == dst_parent_id {
          assert i_fs.path_map[dst_parent_dir] == i_fs'.path_map[dst_parent_dir];
          GetMetaEquiv(fs', dst_parent_dir);
        } else {
          assert exists p :: P.PathExists(fs, p) && P.GetMeta(fs, p).id == id by { reveal_IPathMap(); }
          var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == id;
          if BeneathDir(dst, p) {
            PInv.NoValidBeneathDir(fs, dst, p);
            assert false;
          } else if BeneathDir(src, p) {
            var dstpath := dst + p[|src|..];
            assert BeneathDir(dst, dstpath);
            assert p == src + dstpath[|dst|..];
            assert i_fs.path_map[p] == id by { reveal_IPathMap(); }
            assert i_fs'.path_map[dstpath] == i_fs.path_map[p];
            assert i_fs'.path_map[dstpath] == id;
            GetMetaEquiv(fs, p);
            GetMetaEquiv(fs', dstpath);
          } else {
            assert i_fs.path_map[p] == i_fs'.path_map[p];
            assert i_fs.path_map[p] == id by { reveal_IPathMap(); }
            assert P.GetMeta(fs, p) == P.GetMeta(fs', p);
            GetMetaEquiv(fs, p);
            GetMetaEquiv(fs', p);
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
          meow(fs, fs', src, dst, ctime);
        } else {
          assert exists p :: P.PathExists(fs, p) && P.GetMeta(fs, p).id == id by { reveal_IPathMap(); }
          var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == id;
          assert i_fs.path_map[p] == id by { reveal_IPathMap(); }

          if p == src || BeneathDir(src, p) {
            var dstpath := dst + p[|src|..];
            assert p == src + dstpath[|dst|..];
            assert i_fs'.path_map[dstpath] == i_fs.path_map[p];
            assert i_fs'.path_map[dstpath] == id;
            GetDataEquiv(fs, p);
            GetDataEquiv(fs', dstpath);
          } else if BeneathDir(dst, p) {
            PInv.NoValidBeneathDir(fs, dst, p);
          } else {
            assert i_fs'.path_map[p] == i_fs.path_map[p];
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

    if dst == RootDir {
      PInv.NoValidBeneathDir(fs, dst, src);
      assert false;
    }

    RefinesRenamePathMap(fs, fs', src, dst, ctime);
    RefinesRenameMetaMap(fs, fs', src, dst, ctime);
    RefinesRenameDataMap(fs, fs', src, dst, ctime);

    reveal_IPathMap();
    reveal_IMetaMap();
    reveal_IDataMap();

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

    var src_id := P.GetMeta(fs, source).id;
    var m := fs.content.meta_map[source];
    var m' := P.LinkMeta(fs, source, ctime);

    var dparent_dir := GetParentDir(dest);
    var dparent_id := P.GetMeta(fs, dparent_dir).id;
    var dparent_m' := P.UpdatePathTime(fs.content, dparent_dir, ctime);

    forall p
    ensures i_fs'.path_map[p] == i_fs.path_map[dest := src_id][p]
    {
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
        // InvImpliesInv(fs);
        // InvImpliesInv(fs');
      } else if id in i_fs.path_map.Values {
        if id == src_id {
          if m.MetaData? {
            assert fs'.content.meta_map[source] == RedirectMeta(hiddenName.value);
            assert fs'.hidden.meta_map[hiddenName.value] == m';
          } else {
            assert fs'.content.meta_map[source] == fs.content.meta_map[source];
          }
          assert P.GetMeta(fs', source) == m';
          assert i_fs'.meta_map[id] == m';
          assert i_fs.meta_map[src_id := m'][dparent_id := dparent_m'][id] == m';
          assert P.GetData(fs', source) == P.GetData(fs, source);
          assert i_fs'.data_map[id] == i_fs.data_map[id];
        } else if id == dparent_id {
          calc {
            i_fs.meta_map[src_id := m'][dparent_id := dparent_m'][id];
            dparent_m';
            P.GetMeta(fs', dparent_dir);
            i_fs'.meta_map[id];
          }
          calc {
            i_fs'.data_map[id];
            P.GetData(fs', dparent_dir);
            P.GetData(fs, dparent_dir);
            i_fs.data_map[id];
          }
        } else {
          var p :| P.PathExists(fs, p) && P.GetMeta(fs, p).id == id;
          assert P.PathExists(fs', p);
          calc {
            i_fs'.meta_map[id];
            P.GetMeta(fs', p);
            P.GetMeta(fs, p);
            i_fs.meta_map[id];
            i_fs.meta_map[src_id := m'][dparent_id := dparent_m'][id];
          }
          calc {
            i_fs'.data_map[id];
            P.GetData(fs', p);
            P.GetData(fs, p);
            i_fs.data_map[id];
          }
        }
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
  }

  lemma RefinesTruncate(fs: P.FileSys, fs': P.FileSys, path: Path, size: int, time: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Truncate(fs, fs', path, size, time)
  ensures F.Truncate(I(fs), I(fs'),  path, size, time)
  {
  }

  lemma RefinesRead(fs: P.FileSys, fs': P.FileSys, path: Path, offset: int, size: int, data: Data)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Read(fs, fs', path, offset, size, data)
  ensures F.Read(I(fs), I(fs'), path, offset, size, data)
  {
  }

  lemma RefinesWrite(fs: P.FileSys, fs': P.FileSys, path: Path, offset: int, size: int, data: Data, time: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.Write(fs, fs', path, offset, size, data, time)
  ensures F.Write(I(fs), I(fs'), path, offset, size, data, time)
  {
  }

  lemma RefinesUpdateTime(fs: P.FileSys, fs': P.FileSys, path: Path, atime: Time, mtime: Time, ctime: Time)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.UpdateTime(fs, fs', path, atime, mtime, ctime)
  ensures F.UpdateTime(I(fs), I(fs'), path, atime, mtime, ctime)
  {
  }

  lemma RefinesReadDir(fs: P.FileSys, fs': P.FileSys, dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
  requires PInv.Inv(fs)
  requires PInv.Inv(fs')
  requires P.ReadDir(fs, fs', dir, start, results, done)
  ensures F.ReadDir(I(fs), I(fs'), dir, start, results, done)
  {
  }

}
