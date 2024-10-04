pub mod spec;

// trusted outer thingy.
// This is the one file that breaks the "trusted things can't mention verified stuff" rule,
// because it's here that we're identifying a specific implementation that satisfies all
// the auditor's obligations.
pub fn main()
{
}
