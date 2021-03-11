// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Inc.dfy"

module StateMachine {
  import opened StateObjects

  type Variables = multiset<StateObject>

  // Allowed transforms:
  //
  // Ticket -> IncTicket, IncTicket, CurValue(0)
  // IncTicket, CurValue(n) -> IncStub, CurValue(n+1)
  // IncStub, IncStub, CurValue(n) -> Stub(n)

  // NOTE: we need to systematize the connection between these
  // and the transform methods

  predicate transform(a: multiset<StateObject>, b: multiset<StateObject>)
  {
    || (a == multiset{Ticket} && b == multiset{IncTicket, IncTicket, CurValue(0)})
    || (exists n :: a == multiset{IncTicket, CurValue(n)}
                 && b == multiset{IncStub, CurValue(n+1)})
    || (exists n :: a == multiset{IncStub, IncStub, CurValue(n)}
                 && b == multiset{Stub(n)})
  }

  predicate Init(s: Variables)
  {
    s == multiset{Ticket}
  }

  predicate Next(s: Variables, s': Variables)
  {
		exists a, b, c ::
			s == a + c && s' == b + c     // BP: Why the extra c?
			&& transform(a, b)
	}

	// We wanna prove this Inv (from which it clearly implies any Stub will be 2)
	// We can debate the exact way to formula this guarantee (which might be easier
	// for a more complex system with a more interesting guarantee) but in any case,
	// proving this Inv is the meat of the proof

  predicate Inv(s: Variables)
  {
    || s == multiset{Ticket}
    || s == multiset{IncTicket, IncTicket, CurValue(0)}
    || s == multiset{IncTicket, IncStub, CurValue(1)}
    || s == multiset{IncStub, IncStub, CurValue(2)}
    || s == multiset{Stub(2)}
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
  }

  lemma NextPreservesInv(s: Variables, s': Variables)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
  {
    
  }
}
