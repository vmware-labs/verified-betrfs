include "AbstractJournal.i.dfy"
include "PagedJournal.i.dfy"

// Hey look, this abstract journal satisfies the refinement.
module AbstractJournalRefinement refines CoordinationSystemRefinement(AbstractJournal) {
}

// Ooh, and so does this Paged journal
module PagedJournalRefinement refines CoordinationSystemRefinement(PagedJournal) {
}
