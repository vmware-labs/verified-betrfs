// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FSTypes.s.dfy"

/*
 * This file system doesn't specify any permission checking or path cleanup: relying on shim/vfs to do so.
 * It defines an in memory filesystem, has no knowledge of device and persistence.
*/

module FileSystem {
  import opened FSTypes
  import opened PathSpec
  import opened Options

  type MetaView = imap<ID, MetaData>
  type DataView = imap<ID, Data> 

  datatype FileSys = FileSys(path_map: PathMap, meta_map: MetaView, data_map: DataView)

  // jonh: This file would get 5.5% shorter if we replace WF with a subset type :)
  // jialin: we don't have an easy function method to initialize these imaps for the witness
  //   I saw splinter's interp.s example to bypass the compilation complaints but not sure if that's
  //   the standard/style we want to go with, so just going to leave this predicate here for now
  predicate WF(fs: FileSys)
  {
    && PathMapComplete(fs.path_map)
    && (forall id :: id in fs.meta_map && id in fs.data_map)
  }

  predicate PathExists(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && fs.path_map[path].ID?
    && fs.meta_map[fs.path_map[path]].MetaData?
  }

  predicate Init(fs: FileSys)
  {
    && fs.path_map == InitPathMap()
    && fs.meta_map == (imap id :: if id == RootID then InitRootMetaData() else EmptyMetaData)
    && fs.data_map == (imap id :: EmptyData())
  }

  /// Inv conditions

  function AliasPaths(fs: FileSys, id: ID) : (aliases: iset<Path>)
  requires WF(fs)
  ensures forall path :: path in aliases <==> fs.path_map[path] == id
  {
    iset path | fs.path_map[path] == id
  }

  predicate NoAlias(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && AliasPaths(fs, fs.path_map[path]) == iset{path}
  }

  predicate DirImpliesHasNoAlias(fs: FileSys, path: Path)
  requires WF(fs)
  requires PathExists(fs, path)
  {
    var id := fs.path_map[path];
    && (fs.meta_map[id].ftype.Directory? ==> NoAlias(fs, path))
  }

  predicate ParentDirIsDir(fs: FileSys, path: Path)
  requires WF(fs)
  {
    var parent_dir := GetParentDir(path);
    var parent_id := fs.path_map[parent_dir];
    && PathExists(fs, parent_dir)
    && fs.meta_map[parent_id].ftype.Directory?
  }

  predicate ValidNewPath(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && ParentDirIsDir(fs, path)
    && fs.path_map[path].Nonexistent?
  }

  predicate ValidNewId(fs: FileSys, id: ID)
  requires WF(fs)
  {
    && id.ID?
    && AliasPaths(fs, id) == iset{}
  }

  /// FileSys Ops

  predicate GetAttr(fs: FileSys, fs':FileSys, path: Path, attr: MetaData)
  {
    && WF(fs)
    && PathExists(fs, path)
    && fs' == fs
    && attr == fs.meta_map[fs.path_map[path]]
  }

  predicate ReadLink(fs: FileSys, fs':FileSys, path: Path, link_path: Path)
  {
    && WF(fs)
    && PathExists(fs, path)
    && fs' == fs
    && fs.meta_map[fs.path_map[path]].ftype.SymLink?
    && link_path == fs.meta_map[fs.path_map[path]].ftype.source
  }

  function UpdateParentTime(fs: FileSys, id: ID, time: Time) : MetaData
  requires WF(fs)
  {
    var m := fs.meta_map[id];
    if m.MetaData? then (
      MetaDataUpdateTime(m, m.atime, time, time)
    ) else (
      m
    )
  }

  predicate Create(fs: FileSys, fs':FileSys, path: Path, id: ID, m: MetaData)
  {
    && WF(fs)
    && WF(fs')
    && ValidNewPath(fs, path)
    && ValidNewMetaData(m, path)
    && ValidNewId(fs, id)
    // Entry Not Present
    && fs.meta_map[id].EmptyMetaData?
    && fs.data_map[id] == EmptyData()
    // Updated maps
    && var parent_id := fs.path_map[GetParentDir(path)];
    && fs'.path_map == fs.path_map[path := id]
    && fs'.meta_map == fs.meta_map[id := m][parent_id := UpdateParentTime(fs, parent_id, m.mtime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataUpdateCTime(m: MetaData, ctime: Time): MetaData
  requires m.MetaData?
  {
    MetaData(m.ftype, m.perm, m.uid, m.gid, m.atime, m.mtime, ctime)
  }

  function MetaDataDelete(fs: FileSys, path: Path, ctime: Time): MetaData
  requires WF(fs)
  {
    var id := fs.path_map[path];
    if id.Nonexistent? || fs.meta_map[id].EmptyMetaData? || NoAlias(fs, path)
    then EmptyMetaData
    else MetaDataUpdateCTime(fs.meta_map[id], ctime)
  }

  function DataDelete(fs: FileSys, path: Path): Data
  requires WF(fs)
  {
    var id := fs.path_map[path];
    if id.Nonexistent? || NoAlias(fs, path)
    then EmptyData()
    else fs.data_map[id]
  }

  predicate Delete(fs: FileSys, fs':FileSys, path: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && path != RootDir
    && PathExists(fs, path)
    && var id := fs.path_map[path];
    && (fs.meta_map[id].ftype.Directory? ==> IsEmptyDir(fs.path_map, path))
    // maps after delete
    && var parent_id := fs.path_map[GetParentDir(path)];
    && fs'.path_map == fs.path_map[path := Nonexistent]
    && fs'.meta_map == fs.meta_map[id := MetaDataDelete(fs, path, ctime)][parent_id := UpdateParentTime(fs, parent_id, ctime)]
    && fs'.data_map == fs.data_map[id := DataDelete(fs, path)]
  }

  function PathMapRename(fs: FileSys, src: Path, dst: Path): (path_map: PathMap)
  requires WF(fs)
  ensures PathMapComplete(path_map)
  ensures 
    forall p | p != src && !BeneathDir(src, p) && p != dst && !BeneathDir(dst, p)
      :: path_map[p] == fs.path_map[p]
  {
    imap path :: 
      if path == src || BeneathDir(src, path)
        // remove source paths
        then Nonexistent
      else if path == dst || BeneathDir(dst, path)
        // redirect renamed paths to point to the same ids as source
        then var suffix := path[|dst|..];
          fs.path_map[src + suffix]
      // everything else remains the same
      else fs.path_map[path]
  }

  predicate Rename(fs: FileSys, fs':FileSys, src: Path, dst: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, src)
    && !BeneathDir(dst, src)
    && (PathExists(fs, dst) || ValidNewPath(fs, dst))

    && var src_id := fs.path_map[src];
    && var dst_id := fs.path_map[dst];
    && var src_m := fs.meta_map[src_id];
    && (PathExists(fs, dst) ==> 
      && var dst_m := fs.meta_map[dst_id];
      && (src_m.ftype.Directory? <==> dst_m.ftype.Directory?)
      && (dst_m.ftype.Directory? ==> IsEmptyDir(fs.path_map, dst))
    )

    && var sparent_id := fs.path_map[GetParentDir(src)];
    && var dparent_id := fs.path_map[GetParentDir(dst)];
    && var src_m' := MetaDataUpdateCTime(src_m, ctime);
    && fs'.path_map == PathMapRename(fs, src, dst)
    // robj: are src and dst reversed here?
    // jialin: src changes to dst in fs', but dst still points to the src_id
    //  so we update src_id to src_m', and delete anything that might be pointed to dst
    //  to show any old content is overwritten   
    && fs'.meta_map == 
          fs.meta_map[src_id := src_m']
                    // jonh: if dst_id is no longer referenced, shouldn't we remove it from the meta_map?
                     [dst_id := MetaDataDelete(fs, dst, ctime)]
                     [sparent_id := UpdateParentTime(fs, sparent_id, ctime)]
                     [dparent_id := UpdateParentTime(fs, dparent_id, ctime)]
    && fs'.data_map == fs.data_map[dst_id := DataDelete(fs, dst)]
  }

  predicate Link(fs: FileSys, fs':FileSys, source: Path, dest: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    // NOTE: won't work for hardlink other filesystem files
    // robj: Hard-links can't cross file systems, so not a problem.
    && PathExists(fs, source)
    && ValidNewPath(fs, dest)
    && var id := fs.path_map[source];
    && var m := fs.meta_map[id];
    && !m.ftype.Directory?  // disallow directory hardlinks
    // updated maps
    && var dparent_id := fs.path_map[GetParentDir(dest)];
    && fs'.path_map == fs.path_map[dest := id]
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateCTime(m, ctime)][dparent_id := UpdateParentTime(fs, dparent_id, ctime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataChangeAttr(m: MetaData, perm: int, uid:int, gid: int, ctime: Time): MetaData
  requires m.MetaData?
  {
    MetaData(m.ftype, perm, uid, gid, m.atime, m.mtime, ctime)
  }

  // chown + chmod
  predicate ChangeAttr(fs: FileSys, fs':FileSys, path: Path, perm: int, uid: int, gid: int, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    && var id := fs.path_map[path];
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataChangeAttr(fs.meta_map[id], perm, uid, gid, ctime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataUpdateTime(m: MetaData, atime: Time, mtime: Time, ctime: Time): MetaData
  requires m.MetaData?
  {
    MetaData(m.ftype, m.perm, m.uid, m.gid, atime, mtime, ctime)
  }

  function ZeroData(size: nat) : (d: Data) { seq(size, i => 0) }

  function DataTruncate(d: Data, size: int): (d': Data)
  requires 0 <= size
  ensures |d'| == size
  {
    if |d| >= size then d[..size] else d + ZeroData(size-|d|)
  }

  predicate Truncate(fs: FileSys, fs':FileSys, path: Path, size: int, time: Time)
  {
    && WF(fs)
    && WF(fs')
    && 0 <= size
    && PathExists(fs, path)
    && var id := fs.path_map[path];
    && var m := fs.meta_map[id];
    && m.ftype.File?
    // updated maps
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateTime(m, m.atime, time, time)]
    && fs'.data_map == fs.data_map[id := DataTruncate(fs.data_map[id], size)]
  }

  predicate Read(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data)
  {
    && WF(fs)
    && fs' == fs
    && PathExists(fs, path)
    && var id := fs.path_map[path];
    && fs.meta_map[id].ftype.File?
    && 0 <= offset <= offset+size <= |fs.data_map[id]|
    && data == fs.data_map[id][offset..offset+size]
  }

  function DataWrite(d: Data, data: Data, offset: int, size: int): (d': Data)
  requires 0 <= offset <= |d|
  requires size == |data|
  ensures offset <= offset+size <= |d'|
  ensures d'[offset..offset+size] == data
  {
    if offset+size > |d| then d[..offset] + data else d[..offset] + data + d[offset+size..]
  }

  predicate Write(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data, time: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    && |data| == size
    && var id := fs.path_map[path];
    && var m := fs.meta_map[id];
    && m.ftype.File?
    && 0 <= offset <= |fs.data_map[id]|
    // updated maps
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateTime(m, time, time, time)]
    && fs'.data_map == fs.data_map[id := DataWrite(fs.data_map[id], data, offset, size)]
  }

  predicate UpdateTime(fs: FileSys, fs':FileSys, path: Path, atime: Time, mtime: Time, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    && var id := fs.path_map[path];
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateTime(fs.meta_map[id], atime, mtime, ctime)]
    && fs'.data_map == fs.data_map
  }

  predicate ValidDirEntry(fs: FileSys, de: DirEntry)
  requires WF(fs)
  {
    && PathExists(fs, de.path)
    && de.id == fs.path_map[de.path]
    && de.ftype == fs.meta_map[de.id].ftype
  }

  // robj: What about done?
  // robj: Should we requires that results are all >= start in sort order?
  // jialin: just updated line 404-406
  predicate ReadDir(fs: FileSys, fs':FileSys, dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
  {
    && WF(fs)
    && fs' == fs
    && PathExists(fs, dir)
    && fs.meta_map[fs.path_map[dir]].ftype.Directory?
    && (start.Some? ==> IsDirEntry(dir, start.value))
    // results actually belong to this directory
    && (forall i | 0 <= i < |results| :: IsDirEntry(dir, results[i].path))
    // results consistent with filesys content
    && (forall i | 0 <= i < |results| :: ValidDirEntry(fs, results[i]))
    // results are strictly sorted, >= start
    && (start.Some? && |results| > 0 ==> DirEntryLte(start.value, results[0].path))
    && (forall i, j | 0 <= i < j < |results| :: 
          && DirEntryLte(results[i].path, results[j].path)
          && results[i] != results[j])
    // results don't skip over any valid entry
    && (forall path |
        && IsDirEntry(dir, path)
        && PathExists(fs, path)
        && (start.Some? ==> DirEntryLte(start.value, path))
        && (done ==> (exists i :: 0 <= i < |results| && results[i].path == path))
        && (!done && |results| > 0 ==> DirEntryLte(path, results[|results|-1].path))
          :: (exists i :: 0 <= i < |results| && results[i].path == path))
  }

  predicate Stutter(fs: FileSys, fs': FileSys)
  {
    && WF(fs)
    && fs' == fs
  }

  datatype Step =
    | GetAttrStep(path: Path, attr: MetaData)
    | ReadLinkStep(path: Path, link_path: Path)
    | CreateStep(path: Path, id: ID, m: MetaData) // mknod, mkdir, symlink
    | DeleteStep(path: Path, ctime: Time) // unlink and rmdir
    | RenameStep(source: Path, dest: Path, ctime: Time)
    | LinkStep(source: Path, dest: Path, ctime: Time)
    | ChangeAttrStep(path: Path, perm: int, uid: int, gid: int, ctime: Time) // chmod + chown
    | TruncateStep(path: Path, size: int, time: Time)
    | ReadStep(path: Path, offset: int, size: int, data: Data)
    | WriteStep(path: Path, offset: int, size: int, data: Data, time: Time)
    | UpdateTimeStep(path: Path, atime: Time, mtime: Time, ctime: Time) 
    | ReadDirStep(dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
    | StutterStep

  predicate NextStep(fs: FileSys, fs': FileSys, step:Step)
  {
    match step {
      case GetAttrStep(path, attr) => GetAttr(fs, fs', path, attr)
      case ReadLinkStep(path, link_path) => ReadLink(fs, fs', path, link_path)
      case CreateStep(path, id, m) => Create(fs, fs', path, id, m)
      case DeleteStep(path, ctime) => Delete(fs, fs', path, ctime)
      case RenameStep(source, dest, ctime) => Rename(fs, fs', source, dest, ctime)
      case LinkStep(source, dest, ctime) => Link(fs, fs', source, dest, ctime)
      case ChangeAttrStep(path, perm, uid, gid, ctime) => ChangeAttr(fs, fs', path, perm, uid, gid, ctime)
      case TruncateStep(path, size, time) => Truncate(fs, fs', path, size, time)
      case ReadStep(path, offset, size, data) => Read(fs, fs', path, offset, size, data)
      case WriteStep(path, offset, size, data, time) => Write(fs, fs', path, offset, size, data, time)
      case UpdateTimeStep(path, atime, mtime, ctime) => UpdateTime(fs, fs', path, atime, mtime, ctime)
      case ReadDirStep(dir, start, results, done) => ReadDir(fs, fs', dir, start, results, done)
      case StutterStep() => Stutter(fs, fs')
    }
  }

  predicate Next(fs: FileSys, fs': FileSys)
  {
    exists step :: NextStep(fs, fs', step)
  }
}
