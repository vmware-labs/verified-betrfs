// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Disk/GenericDisk.i.dfy"

module LikesAUMod
{
  import opened Maps
  import GenericDisk
  
  type LikesAU = multiset<GenericDisk.AU>

  function NoLikes() : LikesAU
  {
    multiset{}
  }

  function mapsum<T>(s: map<T, LikesAU>) : LikesAU
  {
    if s.Keys == {} then NoLikes()
    else (
      var k :| k in s.Keys;
      s[k] + mapsum(MapRemove1(s, k))
    )
  }
}
