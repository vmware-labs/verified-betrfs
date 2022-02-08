include "AbstractJournal.i.dfy"

// Hey look, this abstract journal satisfies the refinement.
module AbstractJournalRefinement refines PagedSystemRefinement(AbstractJournal) {
}
