include "AbstractJournal.i.dfy"
include "AbstractMap.i.dfy"
include "PagedJournal.i.dfy"

// Hey look, this abstract journal satisfies the refinement.
module AbstractJournalRefinement refines CoordinationSystemRefinement(AbstractJournal, AbstractMap) {
}

// Ooh, and so does this Paged journal
module PagedJournalRefinement refines CoordinationSystemRefinement(PagedJournal, AbstractMap) {
}
