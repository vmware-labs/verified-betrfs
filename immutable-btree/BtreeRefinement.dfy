include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"
include "CrashableMap.dfy"
include "../tla-tree/MissingLibrary.dfy"
include "BtreeSpec.dfy"
include "BtreeInv.dfy"

module BtreeRefinement {
  import opened Spec = BtreeSpec
  import opened Inv = BtreeInv
  //import Keyspace = Bounded_Total_Order
  import opened Sequences
  import CrashableMap
  import opened MissingLibrary

  function Ik(k: Constants) : CrashableMap.Constants
  {
    CrashableMap.Constants()
  }

  function INode<Value(!new)>(tree: Node) : imap<Key, Option<Value>>
  {
    imap k:Key ::
        if (exists lookup: Lookup, v: Value :: IsSatisfyingLookup(tree, k, v, lookup)) then
        (var lookup: Lookup, v: Value :| IsSatisfyingLookup(tree, k, v, lookup);
         Some(v))
        else
         None
  }


  function I<Value(!new)>(k: Constants, s: Variables) : CrashableMap.Variables
  {
    CrashableMap.Variables([ INode(s.root) ])
  }

  lemma InvImpliesRefinementInv(k:Constants, s:Variables)
  requires Invariant(k, s);
  ensures CrashableMap.WF(I(k, s));
  {
    
  }

  lemma InterpretationsAreIdentical(k: Constants, s:Variables, s':Variables)
    requires PreservesLookups(s.root, s'.root);
    requires CantEquivocate(s.root)
    requires PreservesLookups(s'.root, s.root);
    requires CantEquivocate(s'.root)
    ensures I(k, s) == I(k, s')
  {
    assert INode(s.root) == INode(s'.root);
  }

  lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
  requires Next(k, s, s');
  requires Invariant(k, s);
  requires Invariant(k, s');
  ensures CrashableMap.WF(I(k, s));
  ensures CrashableMap.WF(I(k, s));
  ensures CrashableMap.Reachable(Ik(k), I(k, s), I(k, s'));
  {
    var step:Step :| NextStep(k, s, s', step);
    match step {
      case GetStep(key, value, lookup) => {
        assert CrashableMap.WF(I(k, s));
        assert CrashableMap.WF(I(k, s));

        assert CrashableMap.NextStep(Ik(k), I(k,s), I(k,s'), CrashableMap.QueryStep(key, Some(value)));

        assert CrashableMap.IsPath(Ik(k), I(k, s), I(k, s'), [I(k,s), I(k,s')]);
        assert CrashableMap.Reachable(Ik(k), I(k, s), I(k, s'));
      }
      case PutStep(key, value) => {
        assert CrashableMap.WF(I(k, s));
        assert CrashableMap.WF(I(k, s));

        var intermediate := CrashableMap.Variables([I(k,s').views[0], I(k,s).views[0]]);

        PutIsCorrect(s.root, s'.root, key, value);

        assert CrashableMap.NextStep(Ik(k), I(k,s), intermediate, CrashableMap.WriteStep(key, Some(value)));
        assert CrashableMap.NextStep(Ik(k), intermediate, I(k,s'), CrashableMap.PersistWritesStep(1));

        assert CrashableMap.IsPath(Ik(k), I(k, s), I(k, s'), [ I(k,s), intermediate, I(k,s') ]);

        assert CrashableMap.Reachable(Ik(k), I(k, s), I(k, s'));
      }
      case GrowStep(childrenToLeft) => {
        assert CrashableMap.WF(I(k, s));
        assert CrashableMap.WF(I(k, s));

        if (s.root.Leaf?) {
          GrowLeafIsCorrect(s.root, s'.root, childrenToLeft);
          InterpretationsAreIdentical(k, s, s');
          assert I(k, s') == I(k, s);
        } else {
          GrowIndexIsCorrect(s.root, s'.root, childrenToLeft);
          InterpretationsAreIdentical(k, s, s');
          assert I(k, s') == I(k, s);
        }

        assert CrashableMap.IsPath(Ik(k), I(k, s), I(k, s'), [I(k,s)]);
        assert CrashableMap.Reachable(Ik(k), I(k, s), I(k, s'));
      }
    }
  }
}
