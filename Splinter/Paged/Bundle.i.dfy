include "AbstractJournal.i.dfy"
include "AbstractMap.i.dfy"
include "PagedJournal.i.dfy"
include "../../Spec/RefinementObligation.s.dfy"

// Hey look, this abstract journal satisfies the refinement.
module AbstractJournalRefinement refines CoordinationSystemRefinement(AbstractJournal, AbstractMap) { }

// can't get functors to do their thing. See branch splinter-jonh-modulefight
//module ConcreteRefinementProof refines ImplementationObligation(AbstractJournalRefinement, AbstractMap) { }

//module ImplementationObligation(implementation: StateMachineIfc) refines RefinesIfc(implementation, CrashTolerantMapSpecMod) { }

// Ooh, and so does this Paged journal
module PagedJournalRefinement refines CoordinationSystemRefinement(PagedJournal, AbstractMap) { }
