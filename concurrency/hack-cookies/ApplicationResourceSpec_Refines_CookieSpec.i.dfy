include "ApplicationResourceSpec.i.dfy"
include "CookieSpec.s.dfy"

module ApplicationResourceSpec_Refines_CookieSpec {
  import A = ApplicationResourceSpec
  import B = CookieSpec
  import Ifc = AsyncIfc

  function I(s: A.Variables) : B.Variables
    requires A.Inv(s)

  lemma RefinesNext(s: A.Variables, s':A.Variables, uiop: Ifc.Op)
    requires Inv(s)
    requires A.Next(s, s', uiop)
    ensures Inv(s')
    ensures MS.Next(I(s), I(s'), uiop)

  lemma RefinesInit(s: A.Variables)
    requires A.Init(s)
    ensures Inv(s)
    ensures MS.Init(I(s))

}
