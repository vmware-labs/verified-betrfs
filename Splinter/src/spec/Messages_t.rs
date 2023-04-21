#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;


verus! {

// TODO: These are placeholders
// TODO: (tenzinhl) convert placeholder types to enum so that
// typchecker doesn't allow them to be interchangeably assigned
pub struct Value(pub int);
pub struct Delta(pub int);

// TODO(jonh): Need to genericize the types of Key, Value; and then we'll need to axiomitify /
// leave-unspecified a default value
pub open spec fn default_value() -> Value {
    Value(0)
}

// TODO: placeholder
pub open spec fn nop_delta() -> Delta {
    Delta(0)
}


#[is_variant]
pub enum Message {
    Define{ value: Value },
    Update{ delta: Delta },
}

impl Message {
    pub open spec fn merge(self, new: Message) -> Message {
        self  // TODO: This is a placeholder
    }

    pub open spec fn empty() -> Message {
        Message::Define{ value: default_value() }  // TODO: This is a placeholder
    }
}

}