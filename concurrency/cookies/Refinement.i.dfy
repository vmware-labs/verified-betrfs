// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module Refinement refines StateMachinesRefine(
    ResourceSM(CookieResource),
    AsyncSpec(CookieSpec))
{

  // Implementation must supply an interpretation function.
  function I(s:L.Vars) : H.Vars {
    var pantry_butter := sum pantry.butter over all pantries in s;
    var pantry_sugar := sum pantry.guar over all pantries in s;
    var reqs := map o | o in s && o.ButterAndSugar? :: o.rid := Input(o.butter, o.sugar);
    var resps := map o | o in s && o.Cookies? :: o.rid := Output(o.cookies);
    Variables(CookieSpec.Variables(pantry_butter, pantry_sugar), reqs, resps);
  }

  // Implementation provides an invariant to support induction.
  predicate Inv(s:L.Vars)

  lemma InterpPreservesInit(s:L.Vars)
      requires L.Init(s)
      ensures H.Init(I(s))

  lemma InvInit(s:L.Vars)
      requires L.Init(s)
      ensures Inv(s)

  lemma InvNext(s:L.Vars, s':L.Vars, transition:L.Ifc.TransitionLabel)
      requires Inv(s)
      requires L.Next(s, s', transition)
      ensures Inv(s')
      ensures H.Next(I(s), I(s'), transition)
}

