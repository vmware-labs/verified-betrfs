// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"

module HilbertChoose {
  import opened Options

  // Dafny's idiocy around choose really blows.
//  function HilbertChoose<T(!new)>(p: (T)-->(bool)) : (t:T)
//    requires exists t :: p(t)
//    ensures p(t)
//  {
//    var t :| p(t); t
//  }

  function ChooseIf<T(!new)>(p: (T)-->(bool)) : (out:Option<T>)
    ensures out.Some? <==> exists t :: p.requires(t) && p(t)
    ensures out.Some? ==> p.requires(out.value) && p(out.value)
  {
    if exists out :: p.requires(out) && p(out)
    then Some(var t :| p.requires(t) && p(t); t)
    else None
  }
}

