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
    // place holder since we don't use deltas yet
    pub open spec fn combine_deltas(new: Delta, old: Delta) -> Delta
    {
        if new == nop_delta() {
            old
        } else if old == nop_delta() {
            new
        } else {
            nop_delta()
        }
    }

    pub open spec fn apply_delta(delta: Delta, value: Value) -> Value
    {
        value
    }

    pub open spec fn merge(self, new: Message) -> Message {
        if new.is_Define() {
            new
        } else if self.is_Define() {
            let new_value = Message::apply_delta(new.get_Update_delta(), self.get_Define_value());
            Message::Define{value: new_value}
        } else {
            let new_delta = Message::combine_deltas(new.get_Update_delta(), self.get_Update_delta());
            Message::Update{delta: new_delta}
        }
    }

    pub open spec fn empty() -> Message {
        Message::Define{ value: default_value() }  // TODO: This is a placeholder
    }
}

}