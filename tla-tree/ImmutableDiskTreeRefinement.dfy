include "CrashableMap.dfy"
include "ImmutableDiskTreeInterpretation.dfy"

module ImmutableDiskTreeRefinement {
import opened TreeTypes
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened ImmutableDiskTreeInterpretation
import CrashableMap

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s)
    requires TreeInv(k, s)
    ensures CrashableMap.Init(Ik(k), I(k, s))
{
} 

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires TreeInv(k, s)
    requires TreeInv(k, s')
    ensures CrashableMap.WF(I(k, s))
    ensures CrashableMap.WF(I(k, s'))
    ensures CrashableMap.Next(Ik(k), I(k, s), I(k, s'))
{
}

} // module ImmutableDiskTreeRefinement
