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

  type PathElement = seq<byte>
  type Path = seq<PathElement>

  const RootDir : Path := [];

  predicate BeneathDir(dir: Path, path: Path)
  {
    && |dir| < |path|
    && path[..|dir|] == dir
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
