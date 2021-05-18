include "fstypes.s.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Sequences.i.dfy"

/*
 * This file system doesn't specify any permission checking or path cleanup: relying on shim/vfs to do so.
 * It is a completely in memory filesystem, no knowledge of device and persistence.
*/

module FileSys {
  import opened FileSysTypes
  import opened Sequences

  const DefaultId := -1;

  type PathMap = imap<Path, int>
  type MetaView = imap<int, MetaData>
  type DataView = imap<int, Data> 

  datatype FileSys = FileSys(path_map: PathMap, meta_map: MetaView, data_map: DataView)

  predicate WF(fs: FileSys)
  {
    && (forall path :: path in fs.path_map)
    && (forall id :: id in fs.meta_map && id in fs.data_map)
  }

  function EmptyFS() : (fs : FileSys)
  {
    var path_map := imap path :: DefaultId;
    var meta_map := imap id :: EmptyMetaData();
    var data_map := imap id :: EmptyData();
    FileSys(path_map, meta_map, data_map)
  }

  // predicate IsAbsolutePath(path: Path)
  // {
  //   && |path| > 0
  //   && path[0] as int == '/' as int
  // }

  predicate ValidPath(fs: FileSys, path: Path)
  requires WF(fs)
  {
    // && IsAbsolutePath(path)
    && fs.path_map[path] != DefaultId
  }

  function GetParentDir(path: Path): Path
  {
    if |path| == 0 || Last(path) as int == '/' as int 
    then path else GetParentDir(DropLast(path))
  }

  predicate ValidNewPath(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && var parentdir := GetParentDir(path);
    && ValidPath(fs, parentdir)
    && fs.meta_map[fs.path_map[parentdir]].ftype.Directory?
    && fs.path_map[path] == DefaultId
  }

  predicate IsEmptyDir(fs: FileSys, dir: Path)
  requires WF(fs)
  {
    reveal_IsPrefix();
    && (forall k | k != dir && IsPrefix(dir, k) && k[|dir|] as int == '/' as int :: fs.path_map[k] == DefaultId)
  }

  predicate ValidNewMetaData(m: MetaData)
  {
    && m.atime == m.ctime == m.mtime
    && m.size == 0
    && m.nlink == 1
  }

  // FileSys Ops

  predicate GetAttr(fs: FileSys, fs':FileSys, path: Path, attr: MetaData)
  {
    && WF(fs)
    && ValidPath(fs, path)
    && fs' == fs
    && attr == fs.meta_map[fs.path_map[path]]
  }

  predicate ReadLink(fs: FileSys, fs':FileSys, path: Path, link_path: Path)
  {
    && WF(fs)
    && ValidPath(fs, path)
    && fs' == fs
    && fs.meta_map[fs.path_map[path]].ftype.SymLink?
    && link_path == fs.meta_map[fs.path_map[path]].ftype.source
  }

  predicate Create(fs: FileSys, fs':FileSys, path: Path, id: int, m: MetaData)
  {
    && WF(fs)
    && WF(fs')
    && ValidNewPath(fs, path)
    && ValidNewMetaData(m)
    && id != DefaultId
    // Entry Not Present
    && fs.meta_map[id] == EmptyMetaData() // implies id hasn't shown up
    && fs.data_map[id] == EmptyData()
    // Updated maps
    && fs'.path_map[path] == id
    && fs'.meta_map == fs.meta_map[id := m]
    && fs'.data_map == fs.data_map
  }

  function MetaDataUpdateLink(m: MetaData, delta: int, ctime: Time): MetaData
  {
    MetaData(m.nlink+delta, m.size, m.ftype, m.perm, m.uid, m.gid, m.atime, m.mtime, ctime)
  }

  predicate Delete(fs: FileSys, fs':FileSys, path: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && (fs.meta_map[id].ftype.Directory? ==> IsEmptyDir(fs, path))
    // maps after delete
    && fs'.path_map == fs.path_map[path := DefaultId]
    && (fs.meta_map[id].nlink == 1 ==> 
        && fs'.meta_map == fs.meta_map[id := EmptyMetaData()]
        && fs'.data_map == fs.data_map[id := EmptyData()])
    && (fs.meta_map[id].nlink > 1 ==> 
        && fs'.meta_map == fs.meta_map[id := MetaDataUpdateLink(fs.meta_map[id], -1, ctime)]
        && fs'.data_map == fs.data_map)
  }

  predicate SymLink(fs: FileSys, fs':FileSys, source: Path, dest: Path, id: int, m: MetaData)
  {
    && WF(fs)
    && WF(fs')
    && ValidNewPath(fs, dest) // source doesn't need to be valid
    && ValidNewMetaData(m)
    && m.ftype == FileType.SymLink(source)
    && id != DefaultId
    && fs.meta_map[id] == EmptyMetaData()
    && fs.data_map[id] == EmptyData()
    // updated maps
    && fs'.path_map == fs.path_map[dest := id]
    && fs'.meta_map == fs.meta_map[id := m]
    && fs'.data_map == fs.data_map
  }

  // rename is a map because we allow directory
  predicate Rename(fs: FileSys, fs':FileSys, rename_map: imap<Path, Path>, flags: int)
  {
    && WF(fs)
    && WF(fs')
    // TODO
  }

  predicate Link(fs: FileSys, fs':FileSys, source: Path, dest: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, source)  // NOTE: won't work for hardlink other filesystem files
    && ValidNewPath(fs, dest)
    && var id := fs.path_map[source];
    && !fs.meta_map[id].ftype.Directory?  // disallow directory hardlinks
    // updated maps
    && fs'.path_map == fs.path_map[dest := id]
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateLink(fs.meta_map[id], 1, ctime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataChangeAttr(m: MetaData, perm: int, uid:int, gid: int, ctime: Time): MetaData
  {
    MetaData(m.nlink, m.size, m.ftype, perm, uid, gid, m.atime, m.mtime, ctime)
  }

  // chown + chmod
  predicate ChangeAttr(fs: FileSys, fs':FileSys, path: Path, perm: int, uid: int, gid: int, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataChangeAttr(fs.meta_map[id], perm, uid, gid, ctime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataTruncate(m: MetaData, size: int, time: Time): MetaData
  {
    MetaData(m.nlink, size, m.ftype, m.perm, m.uid, m.gid, m.atime, time, time)
  }

  function ZeroData(size: int) : (d: Data)
  requires size >= 0
  ensures size == |d|
  ensures forall i | 0 <= i < |d| :: d[i] == 0
  {
    if size == 0 then [] else ZeroData(size-1) + [0]
  }

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
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs.meta_map[id].ftype.File?
    && size != fs.meta_map[id].size
    // updated maps
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataTruncate(fs.meta_map[id], size, time)]
    && fs'.data_map == fs.data_map[id := DataTruncate(fs.data_map[id], size)]
  }

  predicate Read(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data)
  {
    && WF(fs)
    && fs' == fs
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs.meta_map[id].ftype.File?
    && 0 <= offset <= offset+size <= fs.meta_map[id].size
    && fs.meta_map[id].size == |fs.data_map[id]| // consistency
    && data == fs.data_map[id][offset..offset+size]
  }

  function MetaDataWrite(m: MetaData, newsize: int, time: Time): MetaData
  {
    var size := if m.size > newsize then m.size else newsize;
    MetaData(m.nlink, size, m.ftype, m.perm, m.uid, m.gid, time, time, time)
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
    && ValidPath(fs, path)
    && |data| == size
    && var id := fs.path_map[path];
    && fs.meta_map[id].ftype.File?
    && fs.meta_map[id].size == |fs.data_map[id]|
    && 0 <= offset <= fs.meta_map[id].size
    // updated maps
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataWrite(fs.meta_map[id], offset+size, time)]
    && fs'.data_map == fs.data_map[id := DataWrite(fs.data_map[id], data, offset, size)]
  }

  function MetaDataUpdateTime(m: MetaData, atime: Time, mtime: Time, ctime: Time): MetaData
  {
    MetaData(m.nlink, m.size, m.ftype, m.perm, m.uid, m.gid, atime, mtime, ctime)
  } 

  predicate UpdateTime(fs: FileSys, fs':FileSys, path: Path, atime: Time, mtime: Time, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateTime(fs.meta_map[id], atime, mtime, ctime)]
    && fs'.data_map == fs.data_map
  }

  predicate ReadDir(fs: FileSys, fs':FileSys, path: Path)
  {
    && WF(fs)
    && fs' == fs
    // TODO
  }

  predicate Stutter(fs: FileSys, fs': FileSys)
  {
    && WF(fs)
    && fs' == fs
  }

  datatype Step =
    | GetAttrStep(path: Path, attr: MetaData)
    | ReadLinkStep(path: Path, link_path: Path)
    | CreateStep(path: Path, id: int, m: MetaData) // mknod and mkdir
    | DeleteStep(path: Path, ctime: Time) // unlink and rmdir
    | SymLinkStep(source: Path, dest: Path, id: int, m: MetaData) // how to? path vs map? path: Path, link_path: Path
    | RenameStep(rename_map: imap<Path, Path>, flags: int) // a map of path to renames?
    | LinkStep(source: Path, dest: Path, ctime: Time)
    | ChangeAttrStep(path: Path, perm: int, uid: int, gid: int, ctime: Time) // chmod + chown
    | TruncateStep(path: Path, size: int, time: Time)
    | ReadStep(path: Path, offset: int, size: int, data: Data)
    | WriteStep(path: Path, offset: int, size: int, data: Data, time: Time)
    | UpdateTimeStep(path: Path, atime: Time, mtime: Time, ctime: Time) 
    | ReadDirStep(path: Path) // TODO: fill in rest of params: starting entry, end as we stop seeing one with prefix
    | StutterStep

  predicate NextStep(fs: FileSys, fs': FileSys, step:Step)
  {
    match step {
      case GetAttrStep(path, attr) => GetAttr(fs, fs', path, attr)
      case ReadLinkStep(path, link_path) => ReadLink(fs, fs', path, link_path)
      case CreateStep(path, id, m) => Create(fs, fs', path, id, m)
      case DeleteStep(path, ctime) => Delete(fs, fs', path, ctime)
      case SymLinkStep(source, dest, id, m) => SymLink(fs, fs', source, dest, id, m)
      case RenameStep(rename_map, flags) => Rename(fs, fs', rename_map, flags)
      case LinkStep(source, dest, ctime) => Link(fs, fs', source, dest, ctime)
      case ChangeAttrStep(path, perm, uid, gid, ctime) => ChangeAttr(fs, fs', path, perm, uid, gid, ctime)
      // case ChmodStep(path, mode, ctime) => Chmod(fs, fs', path, mode, ctime)
      // case ChownStep(path, uid, gid) => Chown(fs, fs', path, uid, gid)
      case TruncateStep(path, size, time) => Truncate(fs, fs', path, size, time)
      case ReadStep(path, offset, size, data) => Read(fs, fs', path, offset, size, data)
      case WriteStep(path, offset, size, data, time) => Write(fs, fs', path, offset, size, data, time)
      case UpdateTimeStep(path, atime, mtime, ctime) => UpdateTime(fs, fs', path, atime, mtime, ctime)
      case ReadDirStep(path) => ReadDir(fs, fs', path)
      case StutterStep() => Stutter(fs, fs')
    }
  }

  predicate Next(fs: FileSys, fs': FileSys)
  {
    exists step :: NextStep(fs, fs', step)
  }

  // connectedness of metadata tree
  predicate Inv(fs: FileSys)
  {
    && WF(fs)

    // for any given path? 
    // I guess 

    // In inv, nlink allowed if it's a file

    // how do we represent connectedness? 
    // for any path name

    // metadata tree
    //
    // path has to be a tree (at least for metadata), connectedness properties ( file path's dependency?), leafs are leafs (/a/b, no /a/b/c)
    // data map just leaf entries,
    // relationship between two maps: file: consistency check for meta map size and data_map?
    //           what about data map with non empty entry but no corresponding metadata

    // TODOs
  }

  lemma InitImpliesInv(fs: FileSys)
  {
  }

  lemma NextPreservesInv(fs: FileSys, fs': FileSys) // add ui op
  {
  }

   
    /*
      | MknodStep(path: Path, mode: Mode, rdev_id: int) // will have entry in data map
      | MkdirStep(path: Path, mode: Mode) // only entry in metadata
      | UnlinkStep(path: Path) // remove a file
      | RmdirStep(path: Path)
      | OpenStep(path: Path) 
      | FlushStep(path: Path) skipped as it doesn't change the filesys?
      | ReleaseStep(path: Path)
      | FSyncStep(path: Path) // skipped here
      | OpenDirStep(path: Path)
      | ReleaseDirStep(path: Path)
      | FSyncDir()
      | DestroyFS // should this exist?
      | SetXattrStep()
      | GetXattrStep()
      | ListXattrStep()
      | RemoveXattrStep()

      ignored fuse_ops:
        access (relying on kernel vfs), create (create + open), destroy (clean up a filesys), lock (flock), 
        bmap (map inode # to blk #), fallocate and so on
    */


}