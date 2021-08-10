// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FSTypes.s.dfy"

module PathBasedFS {
  import opened FSTypes
  import opened PathSpec
  import opened Options

  type MetaView = imap<Path, MetaData>
  type DataView = imap<Path, Data>

  datatype View = View(meta_map: MetaView, data_map: DataView)
  datatype FileSys = FileSys(content: View, hidden: View)

  predicate ViewComplete(v: View)
  {
    && (forall p :: p in v.meta_map && p in v.data_map)
  }

  predicate WF(fs: FileSys)
  {
    && ViewComplete(fs.content)
    && ViewComplete(fs.hidden)
  }

  predicate PathExists(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && !fs.content.meta_map[path].EmptyMeta?
  }

  predicate Init(fs: FileSys)
  {
    var empty_meta := imap p :: EmptyMeta;
    var empty_data := imap p :: EmptyData();

    && fs.content.meta_map == empty_meta[RootDir := InitRootMetaData()]
    && fs.content.data_map == empty_data
    && fs.hidden.meta_map == empty_meta
    && fs.hidden.data_map == empty_data
  }

  /// helper functions and predicates

  function GetMeta(fs: FileSys, path: Path) : MetaData
  requires WF(fs)
  {
    var m := fs.content.meta_map[path];
    if m.RedirectMeta? then fs.hidden.meta_map[m.source] else m
  }

  function AliasPaths(fs: FileSys, path: Path) : (aliases: iset<Path>)
  requires WF(fs)
  requires fs.content.meta_map[path].RedirectMeta?
  ensures forall p :: p in aliases <==> (
    && fs.content.meta_map[p].RedirectMeta? 
    && fs.content.meta_map[p].source == fs.content.meta_map[path].source)
  {
    var src := fs.content.meta_map[path].source;
    iset p | fs.content.meta_map[p].RedirectMeta? && fs.content.meta_map[p].source == src
  }

  predicate NoAlias(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && (fs.content.meta_map[path].RedirectMeta? ==> AliasPaths(fs, path) == iset{path})
  }

  predicate HasReference(fs: FileSys, hidden: Path)
  requires WF(fs)
  {
    && (exists path :: fs.content.meta_map[path] == RedirectMeta(hidden))
  }

  predicate ValidHiddenEntry(fs: FileSys, path: Path)
  requires WF(fs)
  requires fs.content.meta_map[path].RedirectMeta?
  {
    && fs.hidden.meta_map[fs.content.meta_map[path].source].MetaData?
  }

  predicate ParentDirIsDir(fs: FileSys, path: Path)
  requires WF(fs)
  {
    var parent_dir := GetParentDir(path);
    && PathExists(fs, parent_dir)
    && GetMeta(fs, parent_dir).MetaData?
    && GetMeta(fs, parent_dir).ftype.Directory?
  }

  predicate ValidNewPath(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && ParentDirIsDir(fs, path)
    && fs.content.meta_map[path].EmptyMeta?
  }

  predicate ValidNewHiddenName(fs: FileSys, path: Option<Path>)
  requires WF(fs)
  {
    && (path.Some? ==> fs.hidden.meta_map[path.value].EmptyMeta?)
  }

  predicate ValidNewId(fs: FileSys, id: ID)
  requires WF(fs)
  {
    && id.ID?
    && (forall p | fs.content.meta_map[p].MetaData? :: fs.content.meta_map[p].id != id)
    && (forall p | fs.hidden.meta_map[p].MetaData? :: fs.hidden.meta_map[p].id != id)
  }

  predicate IsEmptyDir(fs: FileSys, dir: Path)
  requires WF(fs)
  {
    && (forall k | IsDirEntry(dir, k) :: fs.content.meta_map[k].EmptyMeta?)
  }

  /// FileSys Ops

  predicate GetAttr(fs: FileSys, fs':FileSys, path: Path, attr: MetaData)
  {
    && WF(fs)
    && PathExists(fs, path)
    && fs' == fs
    && attr == GetMeta(fs, path)
  }

  predicate ReadLink(fs: FileSys, fs':FileSys, path: Path, link_path: Path)
  {
    && WF(fs)
    && PathExists(fs, path)
    && fs' == fs
    && GetMeta(fs, path).MetaData?
    && GetMeta(fs, path).ftype.SymLink?
    && link_path == GetMeta(fs, path).ftype.source
  }

  function MetaDataUpdateTime(m: MetaData, atime: Time, mtime: Time, ctime: Time): MetaData
  requires m.MetaData?
  {
    MetaData(m.id, m.ftype, m.perm, m.uid, m.gid, atime, mtime, ctime)
  }

  function UpdatePathTime(v: View, path: Path, time: Time) : MetaData
  requires ViewComplete(v)
  {
    var m := v.meta_map[path];
    if m.MetaData? 
    then MetaDataUpdateTime(m, m.atime, time, time)
    else m
  }

  predicate Create(fs: FileSys, fs':FileSys, path: Path, m: MetaData)
  {
    && WF(fs)
    && WF(fs')
    && ValidNewPath(fs, path)
    && ValidNewMetaData(m, path)
    && ValidNewId(fs, m.id)
    // Updated maps
    && var parent_dir := GetParentDir(path);
    && var parent_m' := UpdatePathTime(fs.content, parent_dir, m.mtime);
    && fs'.content.meta_map == fs.content.meta_map[parent_dir := parent_m'][path := m]
    && fs'.content.data_map == fs.content.data_map
    && fs'.hidden == fs.hidden
  }

  function UpdatePathCtime(v: View, path: Path, time: Time) : MetaData
  requires ViewComplete(v)
  {
    var m := v.meta_map[path];
    if m.MetaData? 
    then MetaDataUpdateTime(m, m.atime, m.mtime, time)
    else m
  }

  function HiddenMetaDataDelete(fs: FileSys, path: Path, ctime: Time): MetaData
  requires WF(fs)
  requires fs.content.meta_map[path].RedirectMeta?
  {
    var m := fs.content.meta_map[path];
    if NoAlias(fs, path) then EmptyMeta else UpdatePathCtime(fs.hidden, m.source, ctime)
  }

  function HiddenDataDelete(fs: FileSys, path: Path): Data
  requires WF(fs)
  requires fs.content.meta_map[path].RedirectMeta?
  {
    var m := fs.content.meta_map[path];
    if NoAlias(fs, path) then EmptyData() else fs.hidden.data_map[m.source]
  }

  predicate Delete(fs: FileSys, fs':FileSys, path: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && path != RootDir
    && PathExists(fs, path)
    && var m := fs.content.meta_map[path];
    && (m.MetaData? && m.ftype.Directory? ==> IsEmptyDir(fs, path))
    // maps after delete
    && var parent_dir := GetParentDir(path);
    && var parent_m' := UpdatePathCtime(fs.content, parent_dir, ctime);
    && fs'.content.meta_map == fs.content.meta_map[path := EmptyMeta][parent_dir := parent_m']
    && fs'.content.data_map == fs.content.data_map[path := EmptyData()]
    && (m.MetaData? ==> fs'.hidden == fs.hidden)
    && (m.RedirectMeta? ==>
      // need to clean up hidden file if no more  
      && fs'.hidden.meta_map == fs.hidden.meta_map[m.source := HiddenMetaDataDelete(fs, path, ctime)]
      && fs'.hidden.data_map == fs.hidden.data_map[m.source := HiddenDataDelete(fs, path)])
  }

  function MetaMapRename(v: View, src: Path, dst: Path, ctime: Time): (meta_map: MetaView)
  requires ViewComplete(v)
  {
    // NOTE(Jialin): ordering matters here, we need to guarantee dst is defined before overwriting
    // all src entries. it is possible for dst entries to cover src entries
    imap path ::
      if path == dst then UpdatePathCtime(v, src, ctime) // update src ctime if not hidden
      else if BeneathDir(dst, path) then v.meta_map[src + path[|dst|..]] // redirect dst to src prefix
      else if path == src || BeneathDir(src, path) then EmptyMeta // clear all valid source entries
      else if path == GetParentDir(src) || path == GetParentDir(dst) then UpdatePathTime(v, path, ctime) // update parentdir
      else v.meta_map[path]
  }

  function DataMapRename(v: View, src: Path, dst: Path, ctime: Time): (data_map: DataView)
  requires ViewComplete(v)
  {
    imap path ::
      if path == dst || BeneathDir(dst, path) then v.data_map[src + path[|dst|..]]
      else if path == src || BeneathDir(src, path) then EmptyData()
      else v.data_map[path]
  }

  predicate Rename(fs: FileSys, fs':FileSys, src: Path, dst: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && src != RootDir
    && src != dst
    && PathExists(fs, src)
    && !BeneathDir(src, dst)
    && (PathExists(fs, dst) || ValidNewPath(fs, dst))
    && (PathExists(fs, dst) ==> fs.content.meta_map[dst] != fs.content.meta_map[src])
    // if dst exists and is a directory 
    // dst needs to be empty and src has to be a directory too
    && var src_m := fs.content.meta_map[src];
    && var dst_m := fs.content.meta_map[dst];
    && (PathExists(fs, dst) ==>
      && (src_m.MetaData? && src_m.ftype.Directory? <==> dst_m.MetaData? && dst_m.ftype.Directory?)
      && (dst_m.MetaData? && dst_m.ftype.Directory? ==> IsEmptyDir(fs, dst)))
    // updated maps
    && fs'.content.meta_map == MetaMapRename(fs.content, src, dst, ctime)
    && fs'.content.data_map == DataMapRename(fs.content, src, dst, ctime)
    && (!dst_m.RedirectMeta? ==> fs'.hidden == fs.hidden)
    && (dst_m.RedirectMeta? ==>
      && fs'.hidden.meta_map == fs.hidden.meta_map[dst_m.source := HiddenMetaDataDelete(fs, dst, ctime)]
      && fs'.hidden.data_map == fs.hidden.data_map[dst_m.source := HiddenDataDelete(fs, dst)])
  }

  function LinkMeta(v: View, path: Path, time: Time) : MetaData
  requires ViewComplete(v)
  {
    var m := v.meta_map[path];
    if m.MetaData? then MetaDataUpdateTime(m, m.atime, m.mtime, time)
    else m
  }

  predicate Link(fs: FileSys, fs':FileSys, source: Path, dest: Path, ctime: Time, hiddenName: Option<Path>)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, source)
    && ValidNewPath(fs, dest)
    && ValidNewHiddenName(fs, hiddenName)
    && var m := fs.content.meta_map[source];
    && (m.MetaData? ==> !m.ftype.Directory? && hiddenName.Some?)
    // updated maps
    && var parent_dir := GetParentDir(dest);
    && var parent_m' := UpdatePathTime(fs.content, parent_dir, ctime);
    && var p := if m.MetaData? then hiddenName.value else m.source;
    && fs'.content.meta_map == fs.content.meta_map[parent_dir := parent_m'][source := RedirectMeta(p)][dest := RedirectMeta(p)]
    && fs'.content.data_map == fs.content.data_map[p := EmptyData()]
    && (m.MetaData? ==> 
      && fs'.hidden.meta_map == fs.hidden.meta_map[hiddenName.value := LinkMeta(fs.content, source, ctime)]
      && fs'.hidden.data_map == fs.hidden.data_map[hiddenName.value := fs.content.data_map[source]])
    && (m.RedirectMeta? ==> fs'.hidden == fs.hidden)
  }

  function MetaDataChangeAttr(v: View, path: Path, perm: int, uid:int, gid: int, ctime: Time): MetaData
  requires ViewComplete(v)
  {
    var m := v.meta_map[path];
    if m.MetaData? then MetaData(m.id, m.ftype, perm, uid, gid, m.atime, m.mtime, ctime)
    else m
  }

  // chown + chmod
  predicate ChangeAttr(fs: FileSys, fs':FileSys, path: Path, perm: int, uid: int, gid: int, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    // updated maps
    && var m := fs.content.meta_map[path];
    && var p := if m.MetaData? then path else m.source;
    && var v := if m.MetaData? then fs.content else fs.hidden;
    && var m' := MetaDataChangeAttr(v, p, perm, uid, gid, ctime);
    && (m.MetaData? ==> 
      && fs'.content.meta_map == fs.content.meta_map[p := m']
      && fs'.content.data_map == fs.content.data_map
      && fs'.hidden == fs.hidden)
    && (m.RedirectMeta? ==> 
      && fs'.content == fs.content
      && fs'.hidden.meta_map == fs.hidden.meta_map[p := m']
      && fs'.hidden.data_map == fs.hidden.data_map)
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
    && GetMeta(fs, path).MetaData?
    && GetMeta(fs, path).ftype.File?
    // updated maps
    && var m := fs.content.meta_map[path];
    && var p := if m.MetaData? then path else m.source;
    && var v := if m.MetaData? then fs.content else fs.hidden;
    && var d := if m.MetaData? then fs.content.data_map[p] else fs.hidden.data_map[p];
    && var m' := UpdatePathTime(v, p, time);

    && (m.MetaData? ==>
      && fs'.content.meta_map == fs.content.meta_map[p := m']
      && fs'.content.data_map == fs.content.data_map[p := DataTruncate(d, size)]
      && fs'.hidden == fs.hidden)
    && (m.RedirectMeta? ==>
      && fs'.content == fs.content
      && fs'.hidden.meta_map == fs.hidden.meta_map[p := m']
      && fs'.hidden.data_map == fs.hidden.data_map[p := DataTruncate(d, size)])
  }

  predicate Read(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data)
  {
    && WF(fs)
    && fs' == fs
    && PathExists(fs, path)
    && (GetMeta(fs, path).MetaData? ==> GetMeta(fs, path).ftype.File?)
    && var m := fs.content.meta_map[path];
    && var d := if m.MetaData? then fs.content.data_map[path] else fs.hidden.data_map[m.source];
    && 0 <= offset <= offset+size <= |d|
    && data == d[offset..offset+size]
  }

  function DataWrite(d: Data, data: Data, offset: int, size: int): (d': Data)
  requires 0 <= offset <= |d|
  requires size == |data|
  ensures offset <= offset+size <= |d'|
  ensures d'[offset..offset+size] == data
  {
    if offset+size > |d| then d[..offset] + data else d[..offset] + data + d[offset+size..]
  }

  function UpdatePathWriteTime(v: View, path: Path, time: Time) : MetaData
  requires ViewComplete(v)
  {
    var m := v.meta_map[path];
    if m.MetaData? then MetaDataUpdateTime(m, time, time, time)
    else m
  }

  predicate Write(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data, time: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    && |data| == size
    && (GetMeta(fs, path).MetaData? ==> GetMeta(fs, path).ftype.File?)
    && var m := fs.content.meta_map[path];
    && var v := if m.MetaData? then fs.content else fs.hidden;
    && var p := if m.MetaData? then path else m.source;
    && var d := if m.MetaData? then fs.content.data_map[p] else fs.hidden.data_map[p];
    && 0 <= offset <= |d|
    && var m' := UpdatePathWriteTime(v, p, time);
    && var d' := DataWrite(d, data, offset, size);
    && (m.MetaData? ==> 
      && fs'.content.meta_map == fs.content.meta_map[p := m']
      && fs'.content.data_map == fs.content.data_map[p := d']
      && fs'.hidden == fs.hidden)
    && (m.RedirectMeta? ==>
      && fs'.content == fs.content
      && fs'.hidden.meta_map == fs.hidden.meta_map[p := m']
      && fs'.hidden.data_map == fs.hidden.data_map[p := d'])
  }

  function UpdatePathUpdateTime(v: View, path: Path, atime: Time, mtime: Time, ctime: Time) : MetaData
  requires ViewComplete(v)
  {
    var m := v.meta_map[path];
    if m.MetaData? then MetaDataUpdateTime(m, atime, mtime, ctime)
    else m
  }

  predicate UpdateTime(fs: FileSys, fs':FileSys, path: Path, atime: Time, mtime: Time, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && PathExists(fs, path)
    && var m := fs.content.meta_map[path];
    && var v := if m.MetaData? then fs.content else fs.hidden;
    && var p := if m.MetaData? then path else m.source;
    && var m' := UpdatePathUpdateTime(v, p, atime, mtime, ctime);
    // updated maps
    && (m.MetaData? ==> 
      && fs'.content.meta_map == fs.content.meta_map[p := m']
      && fs'.content.data_map == fs.content.data_map
      && fs'.hidden == fs.hidden)
    && (m.RedirectMeta? ==> 
      && fs'.content == fs.content
      && fs'.hidden.meta_map == fs.hidden.meta_map[p := m']
      && fs'.hidden.data_map == fs.hidden.data_map)
  }

  predicate ValidDirEntry(fs: FileSys, de: DirEntry)
  requires WF(fs)
  {
    && PathExists(fs, de.path)
    && var m := GetMeta(fs, de.path);
    && (m.MetaData? ==>
      && de.id == m.id
      && de.ftype == m.ftype)
  }

  predicate ReadDir(fs: FileSys, fs':FileSys, dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
  {
    && WF(fs)
    && fs' == fs
    && fs.content.meta_map[dir].MetaData?
    && fs.content.meta_map[dir].ftype.Directory?
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
