include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"

module FileSysTypes {
  import opened NativeTypes
  import opened Options

  type Path = seq<byte>
  type Data = seq<byte>

  datatype FileType = 
    | File
    | Directory
    | SymLink(source: Path)
    | CharFile(major: int, minor: int) // device identifier
    | BlockFile(major: int, minor: int) // device identifier
    | FIFOFile 
    | SocketFile

  datatype Time = Time(seconds: int, nanoseconds: int)

  // metadata tracked by filesys
  datatype MetaData = MetaData(
    nlink: int,       // number of hard links
    size: int,        // size of file
    ftype: FileType,  // type of file
    perm: int,        // permission
    uid: int,         // user ID
    gid: int,         // group ID
    atime: Time,      // last accessed time
    mtime: Time,      // last modified tme 
    ctime: Time       // last status change time
  )

  function EmptyMetaData(): MetaData
  {
    MetaData(0, 0, File, 0, 0, 0, Time(0,0), Time(0,0), Time(0,0))
  }

  function EmptyData(): Data
  {
    []
  }

  //  datatype Stat = Stat(
  //   nlink: int,       // number of hard links
  //   size: int,        // size of file
  //   ftype: FileType,  // type of file
  //   perm: int,        // permission
  //   uid: int,         // user ID
  //   gid: int,         // group ID
  //   atime: Time,      // last accessed time
  //   mtime: Time,      // last modified tme 
  //   ctime: Time       // last status change time
  // )
  
  // function EmptyStat(): Stat
  // {
  //   Stat(0, 0, File, 0, 0, 0, Time(0,0), Time(0,0), Time(0,0))
  // }
  // xattr? // file within file 
  // Questions: ACL? softlink effects on map?

  //   datatype Stat = Stat(
  //   dev_id: int,    // device id containing the file  
  //   id: int,        // identifier for this file 
  //   nlink: int,     // number of hard links
  //   uid: int,       // user ID of owner
  //   gid: int,       // Group ID of owner
  //   size: int,      // size of file
  //   rdev_id: int,   // Device ID *if special file*
  //   blksize: int,   // Block size for filesystem I/O
  //   numblk: int,    // Number of 512B blocks allocated
  //   mode: Mode,     // file type and mode
  //   atime: Time,    // last accessed time
  //   mtime: Time,    // last modified tme 
  //   ctime: Time     // last status change time
  // )

  // might be part of super block data
  // when do we exose this if we spec this at a higher level are we 
  /*datatype StatFS = StatFS(
    fstype: int,      // Type of filesystem (see below)
    blksize: int,     // Optimal transfer block size? does that matter at this layer?
    freeblk: int,     // Free blocks in filesystem 
    availblk: int,    // Free blocks available to unprivileged user
    allocated: int,   // Total inodes in filesystem = # of metadata entry
    freespace: int,   // Free inodes in filesystem = # of space left
    id: int,          // Filesystem ID
    max_len: int,     // Maximum length of filenames
    fragsize: int,    // Fragment size (since Linux 2.6)
    flags: int,       // Mount flags of filesys
  )*/

}