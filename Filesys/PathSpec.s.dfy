// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/System/SeqComparison.s.dfy"

/*
  Path is represented by a sequence of sequence of byte.
  [] represents rootdir
  [[a]] = /a
  [[a],[bc]] = /a/bc
*/

module PathSpec {
  import opened NativeTypes
  import SeqComparison

  // equivalent to inode number
  datatype ID = Nonexistent | ID(id: nat)

  type Path = seq<seq<byte>>
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
    if |path| == 0 then [] else path[..|path|-1]
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
  requires a[..|a|-1] == b[..|b|-1]
  {
    SeqComparison.lte(a[|a|-1], b[|b|-1])
  }
}
