include "AbstractJournal.i.dfy"
include "PagedJournal.i.dfy"
include "../../Spec/RefinementObligation.s.dfy"

// Hey look, this abstract journal satisfies the refinement.
module AbstractJournalRefinement refines CoordinationSystemRefinement(AbstractJournal) { }

module ImplementationObligation(implementation: StateMachineIfc) refines RefinesIfc(implementation, CrashTolerantMapSpecMod) { }

module ConcreteRefinementProof refines ImplementationObligation(AbstractJournalRefinement) { }

// Ooh, and so does this Paged journal
module PagedJournalRefinement refines CoordinationSystemRefinement(PagedJournal) {
}
