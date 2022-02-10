include "AbstractJournal.i.dfy"
include "PagedJournal.i.dfy"

// Hey look, this abstract journal satisfies the refinement.
module AbstractJournalRefinement refines PagedSystemRefinement(AbstractJournal) {
}

// Ooh, and so does this Paged journal
module PagedJournalRefinement refines PagedSystemRefinement(PagedJournal) {
}
