pub mod spec;
pub mod trusted;
pub mod implementation;

// This file is where the generic theorem that the auditor reads
// (in _t files) meets the implementation that the implementor supplies
// (in _v files). Thus it can't follow the _t rule (because it mentions
// the _v stuff), but the auditor has to read it. Therefore, we want
// to keep it trivially simple. Its ONLY job is to mention the
// name of the implementation, to indicate that's what the compiler should
// put into the executable.

fn main() {
    //VerifiedEntry_t::entry::<SimpleBank_v::SimpleBank>();
}
