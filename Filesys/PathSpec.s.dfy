// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"

module PathSpec {
  import opened NativeTypes

  const RootDir :=  ['/' as byte];
  const RootId := 0;
  const DefaultId := -1;
  
  type Path = seq<byte>
  type PathMap = imap<Path, int>

  predicate PathComplete(path_map: PathMap)
  {
    && (forall path :: path in path_map)
  }

  function InitPathMap(): (path_map: PathMap)
  {
    imap path :: if path == RootDir then RootId else DefaultId
  }

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

  lemma GetParentDirImpliesInDir(path: Path, dir: Path)
  requires |dir| > 0
  requires GetParentDir(path) == dir
  ensures InDir(dir, path)
  {
  }
}