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
pub open spec(checked) fn default_value() -> Value {
    Value(0)
}

// TODO: placeholder
pub open spec(checked) fn nop_delta() -> Delta {
    Delta(0)
}


#[is_variant]
pub enum Message {
    Define{ value: Value },
    Update{ delta: Delta },
}

impl Message {
    // place holder since we don't use deltas yet
    pub open spec(checked) fn combine_deltas(new: Delta, old: Delta) -> Delta
    {
        if new == nop_delta() {
            old
        } else if old == nop_delta() {
            new
        } else {
            // nop_delta()
            new
        }
    }

    pub open spec(checked) fn apply_delta(delta: Delta, value: Value) -> Value
    {
        value
    }

    pub open spec(checked) fn merge(self, new: Message) -> Message {
        match (self, new)  {
            (_, Message::Define{value: new_value}) => { 
                Message::Define{value: new_value} 
            }
            (Message::Update{delta: old_delta}, Message::Update{delta: new_delta}) => {
                Message::Update{delta: Self::combine_deltas(new_delta, old_delta)} 
            }
            (Message::Define{value}, Message::Update{delta}) => { 
                Message::Define{value: Self::apply_delta(delta, value)}
            }
        }
    }

    pub open spec(checked) fn empty() -> Message {
        Message::Define{ value: default_value() }  // TODO: This is a placeholder
    }

    // pub proof fn merge_associativity(a: Message, b: Message, c: Message)
    //     ensures a.merge(b.merge(c)) == a.merge(b).merge(c)
    // {
    // }
}

}