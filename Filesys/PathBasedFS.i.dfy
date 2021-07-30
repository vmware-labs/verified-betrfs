// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FSTypes.s.dfy"

module PathBasedFS {
  import opened FSTypes
  import opened PathSpec
  import opened Options

  type ValidMeta(==,!new) = m : MetaData | m.MetaData? witness InitRootMetaData()

  datatype PathMeta =
    | Empty
    | PathMeta(m: ValidMeta, hidden: bool) // hidden used by hardlink
    | RedirectMeta(source: Path) // used by hardlink

  type MetaView = imap<Path, PathMeta>
  type DataView = imap<Path, Data>

  datatype FileSys = FileSys(meta_map: MetaView, data_map: DataView)

  // TODO: needs a refinement file to prove equivalence

  predicate WF(fs: FileSys)
  {
    && (forall p :: p in fs.meta_map && p in fs.data_map)
  }

  predicate PathExists(fs: FileSys, path: Path)
  requires WF(fs)
  {
    var m := fs.meta_map[path];
    || (m.PathMeta? && !m.hidden)
    || m.RedirectMeta?
  }

  predicate Init(fs: FileSys)
  {
    var empty_meta := imap p :: Empty;
    && fs.meta_map == empty_meta[RootDir := PathMeta(InitRootMetaData(), false)]
    && fs.data_map == (imap id :: EmptyData())
  }

  /// Inv conditions

  function GetMeta(fs: FileSys, path: Path) : PathMeta
  requires WF(fs)
  {
    var m := fs.meta_map[path];
    if m.RedirectMeta? then fs.meta_map[m.source] else m
  }

  // basically if it's not 
  // the last entry is for 

  // I want to write this based on the source stuff
  function AliasPaths(fs: FileSys, path: Path) : (aliases: iset<Path>)
  requires WF(fs)
  requires fs.meta_map[path].RedirectMeta?
  {
    var src := fs.meta_map[path].source;
    iset path | fs.meta_map[path].RedirectMeta? && fs.meta_map[path].source == src
  }

  predicate NoAlias(fs: FileSys, path: Path)
  requires WF(fs)
  {
    || fs.meta_map[path].PathMeta?
    || (fs.meta_map[path].RedirectMeta? ==> AliasPaths(fs, path) == iset{path})
  }

  // predicate DirImpliesHasNoAlias(fs: FileSys, path: Path)
  // requires WF(fs)
  // requires PathExists(fs, path)
  // {
  //   && (fs.meta_map[id].ftype.Directory? ==> NoAlias(fs, path))
  // }

  predicate ParentDirIsDir(fs: FileSys, path: Path)
  requires WF(fs)
  {
    var parent_dir := GetParentDir(path);
    && PathExists(fs, parent_dir)
    && GetMeta(fs, parent_dir).PathMeta?
    && GetMeta(fs, parent_dir).m.ftype.Directory?
  }

  predicate ValidNewPath(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && ParentDirIsDir(fs, path)
  }

  predicate ValidNewId(fs: FileSys, id: ID)
  requires WF(fs)
  {
    && id.ID?
    && (forall p | fs.meta_map[p].PathMeta? :: fs.meta_map[p].m.id != id)
  }

  predicate IsEmptyDir(fs: FileSys, dir: Path)
  requires WF(fs)
  {
    && (forall k | BeneathDir(dir, k) :: fs.meta_map[k].Empty?)
  }

  /// FileSys Ops

  predicate GetAttr(fs: FileSys, fs':FileSys, path: Path, attr: ValidMeta)
  {
    && WF(fs)
    && PathExists(fs, path)
    && fs' == fs
    && GetMeta(fs, path).PathMeta?
    && attr == GetMeta(fs, path).m
  }

  predicate ReadLink(fs: FileSys, fs':FileSys, path: Path, link_path: Path)
  {
    && WF(fs)
    && PathExists(fs, path)
    && fs' == fs
    && GetMeta(fs, path).PathMeta?
    && GetMeta(fs, path).m.ftype.SymLink?
    && link_path == GetMeta(fs, path).m.ftype.source
  }

  function UpdatePathTime(fs: FileSys, path: Path, time: Time) : PathMeta
  requires WF(fs)
  {
    var m := GetMeta(fs, path);
    if m.PathMeta? 
    then PathMeta(MetaDataUpdateTime(m.m, m.m.atime, time, time), m.hidden)
    else m
  }

  predicate Create(fs: FileSys, fs':FileSys, path: Path, m: MetaData)
  {
    && WF(fs)
    && WF(fs')
    && ValidNewPath(fs, path)
    && ValidNewMetaData(m, path)
    && ValidNewId(fs, m.id)
    // Entry Not Present
    && fs.meta_map[path].Empty?
    && fs.data_map[path] == EmptyData()
    // Updated maps
    && var parent_dir := GetParentDir(path);
    && var parent_m' := UpdatePathTime(fs, parent_dir, m.mtime);
    && fs'.meta_map == fs.meta_map[parent_dir := parent_m'][path := PathMeta(m, false)]
    && fs'.data_map == fs.data_map
  }

  function UpdatePathCtime(fs: FileSys, path: Path, time: Time) : PathMeta
  requires WF(fs)
  {
    var m := GetMeta(fs, path);
    if m.PathMeta? 
    then PathMeta(MetaDataUpdateTime(m.m, m.m.atime, m.m.mtime, time), m.hidden)
    else m
  }

  function MetaDataDelete(fs: FileSys, path: Path, ctime: Time): PathMeta
  requires WF(fs)
  {
    if NoAlias(fs, path) then Empty else UpdatePathCtime(fs, path, ctime)
  }

  function DataDelete(fs: FileSys, path: Path): Data
  requires WF(fs)
  {
    if NoAlias(fs, path) then EmptyData() else fs.data_map[path]
  }

  predicate Delete(fs: FileSys, fs':FileSys, path: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && path != RootDir
    && PathExists(fs, path)
    && var m := fs.meta_map[path];
    && (m.PathMeta? && m.m.ftype.Directory? ==> IsEmptyDir(fs, path))
    // maps after delete
    && var parent_dir := GetParentDir(path);
    && var parent_m' := UpdatePathCtime(fs, parent_dir, ctime);
    && var m' := MetaDataDelete(fs, path, ctime);
    && (m.PathMeta? ==> fs'.meta_map == fs.meta_map[path := m'][parent_dir := parent_m'])
    && (m.RedirectMeta? ==> fs'.meta_map == fs.meta_map[path := Empty][m.source := m'][parent_dir := parent_m'])
    && fs'.data_map == fs.data_map[path := DataDelete(fs, path)]
  }

  function MetaMapRename(fs: FileSys, src: Path, dst: Path, ctime: Time): (meta_map: MetaView)
  requires WF(fs)
  {
    imap path ::
      if path == src || BeneathDir(src, path) then Empty
      else if path == dst then UpdatePathCtime(fs, path, ctime)
      else if BeneathDir(dst, path) then (
        var suffix := path[|dst|..];
        fs.meta_map[src + suffix]
      ) else if fs.meta_map[dst].RedirectMeta? && fs.meta_map[dst].source == path then (
        UpdatePathCtime(fs, dst, ctime)
      ) else if path == GetParentDir(src) || path == GetParentDir(dst) then (
        UpdatePathTime(fs, path, ctime)
      ) else (
        fs.meta_map[path]
      )
  }

  function DataMapRename(fs: FileSys, src: Path, dst: Path, ctime: Time): (data_map: DataView)
  requires WF(fs)
  {
    imap path ::
      if path == src || BeneathDir(src, path) then EmptyData()
      else if path == dst || BeneathDir(dst, path) then (
        var suffix := path[|dst|..];
        fs.data_map[src + suffix]
      ) else if fs.meta_map[dst].RedirectMeta? && fs.meta_map[dst].source == path then (
        DataDelete(fs, dst)
      ) else (
        fs.data_map[path]
      )
  }

  predicate Rename(fs: FileSys, fs':FileSys, src: Path, dst: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, src)
    && !BeneathDir(dst, src)
    && (PathExists(fs, dst) || ValidNewPath(fs, dst))

    && var src_m := GetMeta(fs, src);
    && (PathExists(fs, dst) ==>
      && var dst_m := GetMeta(fs, dst);
      && (src_m.PathMeta? && src_m.m.ftype.Directory?
          <==> dst_m.PathMeta? && dst_m.m.ftype.Directory?)
      && (dst_m.PathMeta? && dst_m.m.ftype.Directory?
          ==> IsEmptyDir(fs, dst)))

    && fs'.meta_map == MetaMapRename(fs, src, dst, ctime)
    && fs'.data_map == DataMapRename(fs, src, dst, ctime)
  }

  predicate Link(fs: FileSys, fs':FileSys, source: Path, dest: Path, ctime: Time, hiddenName: Option<Path>)
  {
    && WF(fs)
    && WF(fs')
    // NOTE: won't work for hardlink other filesystem files
    // robj: Hard-links can't cross file systems, so not a problem.
    && PathExists(fs, source)
    && ValidNewPath(fs, dest)
    && var m := fs.meta_map[source];
    && (m.PathMeta? ==> !m.m.ftype.Directory?)
    && (m.PathMeta? <==> hiddenName.Some?) // generating an alias for the first time
    && (hiddenName.Some? ==> fs.meta_map[hiddenName.value].Empty?) // just have to be a newpath doesn't need to be connected
    // updated maps
    && var parent_dir := GetParentDir(dest);
    && var parent_m' := UpdatePathTime(fs, parent_dir, ctime);
    && var m' := UpdatePathCtime(fs, source, ctime);
    && (m.RedirectMeta? ==>
      && fs'.meta_map == fs.meta_map[parent_dir := parent_m'][m.source := m']
      && fs'.data_map == fs.data_map)
    && (m.PathMeta? ==>
      && fs'.meta_map == fs.meta_map[parent_dir := parent_m'][source := RedirectMeta(hiddenName.value)][hiddenName.value := m']
      && fs'.data_map == fs.data_map)
  }

  function MetaDataChangeAttr(fs: FileSys, path: Path, perm: int, uid:int, gid: int, ctime: Time): PathMeta
  requires WF(fs)
  requires PathExists(fs, path)
  {
    var m := GetMeta(fs, path);
    if m.PathMeta? 
    then PathMeta(MetaData(m.m.id, m.m.ftype, perm, uid, gid, m.m.atime, m.m.mtime, ctime), m.hidden)
    else m
  }

  // chown + chmod
  predicate ChangeAttr(fs: FileSys, fs':FileSys, path: Path, perm: int, uid: int, gid: int, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    // updated maps
    && var p := if fs.meta_map[path].PathMeta? then path else fs.meta_map[path].source;
    && fs'.meta_map == fs.meta_map[p := MetaDataChangeAttr(fs, path, perm, uid, gid, ctime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataUpdateTime(m: ValidMeta, atime: Time, mtime: Time, ctime: Time): ValidMeta
  {
    MetaData(m.id, m.ftype, m.perm, m.uid, m.gid, atime, mtime, ctime)
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
    && var m := GetMeta(fs, path);
    && m.PathMeta? && m.m.ftype.File?
    // updated maps
    && var p := if fs.meta_map[path].PathMeta? then path else fs.meta_map[path].source;
    && fs'.meta_map == fs.meta_map[p := UpdatePathTime(fs, path, time)]
    && fs'.data_map == fs.data_map[p := DataTruncate(fs.data_map[p], size)]
  }

  predicate Read(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data)
  {
    && WF(fs)
    && fs' == fs
    && PathExists(fs, path)
    && var m := GetMeta(fs, path);
    && (m.PathMeta? ==> m.m.ftype.File?)
    && var p := if fs.meta_map[path].PathMeta? then path else fs.meta_map[path].source;
    && 0 <= offset <= offset+size <= |fs.data_map[p]|
    && data == fs.data_map[p][offset..offset+size]
  }

  function DataWrite(d: Data, data: Data, offset: int, size: int): (d': Data)
  requires 0 <= offset <= |d|
  requires size == |data|
  ensures offset <= offset+size <= |d'|
  ensures d'[offset..offset+size] == data
  {
    if offset+size > |d| then d[..offset] + data else d[..offset] + data + d[offset+size..]
  }

  function UpdatePathWriteTime(fs: FileSys, path: Path, time: Time) : PathMeta
  requires WF(fs)
  {
    var m := GetMeta(fs, path);
    if m.PathMeta? 
    then PathMeta(MetaDataUpdateTime(m.m, time, time, time), m.hidden)
    else m
  }

  predicate Write(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data, time: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    && |data| == size
    && var m := GetMeta(fs, path);
    && (m.PathMeta? ==> m.m.ftype.File?)
    && var p := if fs.meta_map[path].PathMeta? then path else fs.meta_map[path].source;
    && 0 <= offset <= |fs.data_map[p]|
    // updated maps
    && fs'.meta_map == fs.meta_map[p := UpdatePathWriteTime(fs, path, time)]
    && fs'.data_map == fs.data_map[p := DataWrite(fs.data_map[p], data, offset, size)]
  }

  function UpdatePathUpdateTime(fs: FileSys, path: Path, atime: Time, mtime: Time, ctime: Time) : PathMeta
  requires WF(fs)
  {
    var m := GetMeta(fs, path);
    if m.PathMeta? 
    then PathMeta(MetaDataUpdateTime(m.m, atime, mtime, ctime), m.hidden)
    else m
  }

  predicate UpdateTime(fs: FileSys, fs':FileSys, path: Path, atime: Time, mtime: Time, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    && var p := if fs.meta_map[path].PathMeta? then path else fs.meta_map[path].source;
    && fs'.meta_map == fs.meta_map[p := UpdatePathUpdateTime(fs, path, atime, mtime, ctime)]
    && fs'.data_map == fs.data_map
  }

  predicate ValidDirEntry(fs: FileSys, de: DirEntry)
  requires WF(fs)
  {
    && PathExists(fs, de.path)
    && var m := GetMeta(fs, de.path);
    && (m.PathMeta? ==> 
      && de.id == m.m.id
      && de.ftype == m.m.ftype)
  }

  predicate ReadDir(fs: FileSys, fs':FileSys, dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
  {
    && WF(fs)
    && fs' == fs
    && PathExists(fs, dir)
    && fs.meta_map[dir].PathMeta?
    && fs.meta_map[dir].m.ftype.Directory?
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
    | GetAttrStep(path: Path, attr: ValidMeta)
    | ReadLinkStep(path: Path, link_path: Path)
    | CreateStep(path: Path, m: MetaData) // mknod, mkdir, symlink
    | DeleteStep(path: Path, ctime: Time) // unlink and rmdir
    | RenameStep(source: Path, dest: Path, ctime: Time)
    | LinkStep(source: Path, dest: Path, ctime: Time, hiddenName: Option<Path>)
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
      case CreateStep(path, m) => Create(fs, fs', path, m)
      case DeleteStep(path, ctime) => Delete(fs, fs', path, ctime)
      case RenameStep(source, dest, ctime) => Rename(fs, fs', source, dest, ctime)
      case LinkStep(source, dest, ctime, hiddenName) => Link(fs, fs', source, dest, ctime, hiddenName)
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
