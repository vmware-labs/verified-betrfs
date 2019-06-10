include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"
include "../tla-tree/MissingLibrary.dfy"
include "BtreeSpec.dfy"
include "BtreeInv.dfy"

abstract module BtreeRefinement {
  import opened BtreeInv
  import opened Sequences
  import opened MissingLibrary

  function Ik(k: Spec.Constants) : Spec.CSMap.Constants
  {
    Spec.CSMap.Constants()
  }

  function INode<Value(!new)>(tree: Spec.Node) : imap<Spec.Key, Option<Value>>
  {
    imap k:Spec.Key ::
        if (exists lookup: Spec.Lookup, v: Value :: Spec.IsSatisfyingLookup(tree, k, v, lookup)) then
        (var lookup: Spec.Lookup, v: Value :| Spec.IsSatisfyingLookup(tree, k, v, lookup);
         Some(v))
        else
         None
  }


  function I<Value(!new)>(k: Spec.Constants, s: Spec.Variables) : Spec.CSMap.Variables
  {
    Spec.CSMap.Variables([ INode(s.root) ])
  }

  lemma InvImpliesRefinementInv(k:Spec.Constants, s:Spec.Variables)
  requires Invariant(k, s);
  ensures Spec.CSMap.WF(I(k, s));
  {
    
  }

  lemma InterpretationsAreIdentical(k: Spec.Constants, s:Spec.Variables, s':Spec.Variables)
    requires PreservesLookups(s.root, s'.root);
    requires CantEquivocate(s.root)
    requires PreservesLookups(s'.root, s.root);
    requires CantEquivocate(s'.root)
    ensures I(k, s) == I(k, s')
  {
    assert INode(s.root) == INode(s'.root);
  }

  lemma InvImpliesRefinementNext(k:Spec.Constants, s:Spec.Variables, s':Spec.Variables)
  requires Spec.Next(k, s, s');
  requires Invariant(k, s);
  requires Invariant(k, s');
  ensures Spec.CSMap.WF(I(k, s));
  ensures Spec.CSMap.WF(I(k, s));
  ensures Spec.CSMap.Reachable(Ik(k), I(k, s), I(k, s'));
  {
    assert Invariant(k, s);
    assert Spec.WFTree(s.root); // assertion violation wtf?
    var step:Spec.Step :| Spec.NextStep(k, s, s', step);
    match step {
      case GetStep(key, value, lookup) => {
        assert Spec.CSMap.WF(I(k, s));

        assert Spec.CSMap.NextStep(Ik(k), I(k,s), I(k,s'), Spec.CSMap.QueryStep(key, Some(value)));

        assert Spec.CSMap.IsPath(Ik(k), I(k, s), I(k, s'), [I(k,s), I(k,s')]);
        assert Spec.CSMap.Reachable(Ik(k), I(k, s), I(k, s'));
      }
      case PutStep(key, value) => {
        assert Spec.CSMap.WF(I(k, s));

        var intermediate := Spec.CSMap.Variables([I(k,s').views[0], I(k,s).views[0]]);

        PutIsCorrect(s.root, s'.root, key, value);

        assert Spec.CSMap.NextStep(Ik(k), I(k,s), intermediate, Spec.CSMap.WriteStep(key, Some(value)));
        assert Spec.CSMap.NextStep(Ik(k), intermediate, I(k,s'), Spec.CSMap.PersistWritesStep(1));

        assert Spec.CSMap.IsPath(Ik(k), I(k, s), I(k, s'), [ I(k,s), intermediate, I(k,s') ]);

        assert Spec.CSMap.Reachable(Ik(k), I(k, s), I(k, s'));
      }
      case SplitStep(l, u, childrenToLeft) => {
        assert Spec.CSMap.WF(I(k, s));
        SplitIsCorrect(s.root, s'.root, l, u, childrenToLeft);
        InterpretationsAreIdentical(k, s, s');
        assert Spec.CSMap.IsPath(Ik(k), I(k, s), I(k, s'), [I(k,s)]);
        assert Spec.CSMap.Reachable(Ik(k), I(k, s), I(k, s'));
      }
      case GrowStep(childrenToLeft) => {
        assert Spec.CSMap.WF(I(k, s));

        if (s.root.Leaf?) {
          GrowLeafIsCorrect(s.root, s'.root, childrenToLeft);
          InterpretationsAreIdentical(k, s, s');
          assert I(k, s') == I(k, s);
        } else {
          GrowIndexIsCorrect(s.root, s'.root, childrenToLeft);
          InterpretationsAreIdentical(k, s, s');
          assert I(k, s') == I(k, s);
        }

        assert Spec.CSMap.IsPath(Ik(k), I(k, s), I(k, s'), [I(k,s)]);
        assert Spec.CSMap.Reachable(Ik(k), I(k, s), I(k, s'));
      }
    }
  }
}
