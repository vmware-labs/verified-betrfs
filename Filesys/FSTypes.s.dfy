// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PathSpec.s.dfy"
include "../lib/Base/Option.s.dfy"

module FSTypes {
  import opened NativeTypes
  import opened Options
  import opened PathSpec

  // equivalent to inode number
  datatype ID = Nonexistent | ID(id: nat)
  const RootID := ID(0);
  type Data = seq<byte>

  datatype FileType = 
    | File
    | Directory
    | SymLink(source: Path)
    | CharFile(major: int, minor: int) // device identifier
    | BlockFile(major: int, minor: int) // device identifier
    | FIFOFile
    | SocketFile

  datatype Time = Time(nanoseconds: int)

  // metadata tracked by filesys
  datatype MetaData = 
    | EmptyMetaData
    | MetaData(
        id: ID,           // file identifier
        ftype: FileType,  // type of file
        perm: int,        // permission
        uid: int,         // user ID
        gid: int,         // group ID
        atime: Time,      // last accessed time
        mtime: Time,      // last modified tme 
        ctime: Time       // last status change time
      )

  predicate ValidNewMetaData(m: MetaData, path: Path)
  {
    && m.MetaData?
    && m.atime == m.ctime == m.mtime
  }

  function method InitRootMetaData(): MetaData
  {
    MetaData(RootID, Directory, 755, 0, 0, Time(0), Time(0), Time(0))
  }

  function EmptyData(): Data
  {
    []
  }

  // robj asks: is path too general here?  What if path includes slashes?
  // jialin: changed path to be seq<seq<byte>>, the path allowed to return
  //   to users have to be valid, which should eliminate formatting problem
  datatype DirEntry = DirEntry(id: ID, path: Path, ftype: FileType)
}
