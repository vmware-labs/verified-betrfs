// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"

module PathSpec {
  import opened NativeTypes

  const RootDir :=  ['/' as byte];
  const RootId := 0;
  const DefaultId := -1; // robj: How about NonexistentId or something more concrete about its meaning?
    // jonh: better yet, make the type: datatype Inode = NoInode | Inode(inode: nat)

  // robj asks: what about jonh's suggestion to make Path seq<seq<byte>>?
  // jonh: yeah, I really like robj's suggestion to consider jonh's suggestion. Better to represent
  // the intended structure than to escape away the /'s.
  // robj says: aren't paths all of length >= 1?  Maybe use a subset type or defin a ValidPath predicate?
  type Path = seq<byte>
  // jonh: Is the int an inode? Suggest you name it. Either:
  //    type Inode = nat
  // or perhaps better yet:
  //    datatype Inode = Inode(inode: nat)
  // ... the latter creates extra syntax, but prevents automatic casting from other ints, which I think is a win.
  type PathMap = imap<Path, int>

  // robj: How about PathMapComplete?
  // jonh: or make Path a datatype and make this a datatype predicate .Complete! (But then you have the extra
  // syntax that comes with a datatype. :v/ )
  predicate PathComplete(path_map: PathMap)
  {
    && (forall path :: path in path_map)
  }

  // robj: Can this be a const?
  // jonh: what's a const? Isn't this a const?
  function InitPathMap(): (path_map: PathMap)
  {
    imap path :: if path == RootDir then RootId else DefaultId
  }

  // robj: How about "BeneathDir" or something to make it clear that
  // this doesn't mean "is an entry in dir"?
  // jonh: yeah this thing would be much easier to read if paths were sequences of components,
  // rather than trying to parse out slashes.
  predicate InDir(dir: Path, path: Path)
  {
    && path != dir
    && |path| > |dir|
    && path[..|dir|] == dir
    && (|dir| > 1 ==> path[|dir|] as int == '/' as int)
  }

  predicate IsEmptyDir(path_map: PathMap, dir: Path)
  requires PathComplete(path_map)
  {
    && (forall k | InDir(dir, k) :: path_map[k] == DefaultId)
  }

  predicate IsDirEntry(dir: Path, path: Path)
  {
    && InDir(dir, path)
    && !(exists p :: InDir(dir, p) && InDir(p, path))
    // && (forall i | |dir| < i < |path| :: path[i] as int != '/' as int) // equivalent
  }

  function GetParentDirIter(path: Path, i: int): (dir: Path)
  requires 0 <= i < |path|
  requires forall j | i < j < |path| :: path[j] as int != '/' as int
  ensures |dir| < |path|
  ensures path[..|dir|] == dir
  ensures |dir| > 1 ==> path[|dir|] as int == '/' as int 
  ensures forall j | |dir| < j < |path| :: path[j] as int != '/' as int
  {
    if path[i] as int == '/' as int then (
      if i == 0 && |path| > 1 then path[..i+1] else path[..i]
    ) else (
      if i == 0 then [] else GetParentDirIter(path, i-1)
    )
  }

  function GetParentDir(path: Path): (dir: Path)
  {
    if |path| == 0 then path
    else GetParentDirIter(path, |path|-1)
  }

  // robj: Can this be strengthened to IsDirEntry?
  lemma GetParentDirImpliesInDir(path: Path, dir: Path)
  requires |dir| > 0
  requires GetParentDir(path) == dir
  ensures InDir(dir, path)
  {
  }
}
