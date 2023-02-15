// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Disk/GenericDisk.i.dfy"

module LikesMod
{
  import opened Maps
  import GenericDisk
  
  type Likes = multiset<GenericDisk.Address>

  function NoLikes() : Likes
  {
    multiset{}
  }

  function mapsum<T>(s: map<T, Likes>) : Likes
  {
    if s.Keys == {} then NoLikes()
    else (
      var k :| k in s.Keys;
      s[k] + mapsum(MapRemove1(s, k))
    )
  }
}
