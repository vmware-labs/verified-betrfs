// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/System/SeqComparison.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"

/*
  A PathElement is a sequence of byte.
  A Path is a sequence of PathElements.
  [] is the root directory.
  [[a]] = /a
  [[a],[f,o,o]] = /a/foo
*/

module PathSpec {
  import opened NativeTypes
  import SeqComparison
  import opened SequencesLite

  // equivalent to inode number
  datatype ID = Nonexistent | ID(id: nat)

  type PathElement = seq<byte>
  type Path = seq<PathElement>
  type PathMap = imap<Path, ID>

  const RootDir : Path := [];
  const RootID := ID(0);

  // robj says: aren't paths all of length >= 1?  Maybe use a subset type or defin a ValidPath predicate?
  // jialin: we can represent rootdir as empty path

  // jonh: or make Path a datatype and make this a datatype predicate .Complete! (But then you have the extra
  // syntax that comes with a datatype. :v/ )
  // jialin: there isn't many pathmap level operations, wrapping in a datatype might make accessing it 
  //  in the filesystem longer/messier
  predicate PathMapComplete(path_map: PathMap)
  {
    && (forall path :: path in path_map)
  }

  // robj: Can this be a const?
  // jonh: what's a const? Isn't this a const?
  // jialin: imap comprehensions can't be used to define a const
  //   const is considered as a non-ghost contexts and must be compilable
  function InitPathMap(): (path_map: PathMap)
  {
    imap path :: if path == RootDir then RootID else Nonexistent
  }

  predicate BeneathDir(dir: Path, path: Path)
  {
    && |dir| < |path|
    && path[..|dir|] == dir
  }

  predicate IsEmptyDir(path_map: PathMap, dir: Path)
  requires PathMapComplete(path_map)
  {
    && (forall k | BeneathDir(dir, k) :: path_map[k].Nonexistent?)
  }

  predicate IsDirEntry(dir: Path, path: Path)
  {
    && BeneathDir(dir, path)
    && |dir| + 1 == |path|
  }

  function GetParentDir(path: Path): (dir: Path)
  {
    if path == RootDir then RootDir else DropLast(path)
  }

  lemma GetParentDirImpliesIsDirEntry(path: Path, dir: Path)
  requires |path| > 0
  requires GetParentDir(path) == dir
  ensures IsDirEntry(dir, path)
  {
  }

  // to compare two dir entries, just compare their last element
  predicate DirEntryLte(a: Path, b: Path)
  requires |a| > 0
  requires |a| == |b|
  requires GetParentDir(a) == GetParentDir(b)
  {
    SeqComparison.lte(Last(a), Last(b))
  }
}
