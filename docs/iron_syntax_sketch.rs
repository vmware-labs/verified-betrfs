// --> various kinds of functions
#[pure] // deterministic (maybe implied when ghost?)
#[transparent]
ghost fn divides(v: nat, u: nat) -> bool { // 'ghost' == no implementation
    // --> quantifier syntax
    exists(|k: nat| k * u == v)
}

#[pure]
fn gcd(a: u64, b: u64) -> u64
    // --> spec syntax
    ensures exists(|k: nat| k * return == a),
            exists(|k: nat| k * return == b),
            forall(|d: nat| (divides(a, d) && divides(b, d)) ==> d <= return)
    // (this is consistent with the 'where' clause in vanilla rust)
{
    // --> ghost variables and blocks
    let max = ghost { math::max(a, b) }; // inspired by unsafe { ... } blocks

    for c in std::math::max(a, b)..0
        decreases c
        invariant forall(|cc: nat| cc > c ==> !divides(a, c) || !divides(b, c))
    {
        if a % c == 0 && b % c == 0 {
            // --> vc assertions
            assert divides(a, c) && divides(b, c); // assert isn't a function, like 'return'
            return c;
        }
    }
}

ghost struct Map<K, V>;

/// Linear probing Hashtable
struct Hashtable<T> {
    storage: Vec<Option<(u64, T)>>,
    pub ghost contents: Map<nat, T>,
}

impl<T> Hashtable<T> {
    #[pure]
    #[transparent]
    pub ghost fn contents_from_storage(storage: Vec<T>) -> Map<nat, T> { // return is implicitly ghost
        // --> map comprehension
        storage[..].filter_map(|x| x).collect()
    }
}

#[pure]
#[transparent]
pub ghost fn slice_of_doubles(length: nat) -> [nat] { // return is a 'slice' (dafny seq) of nats
    // --> list comprehension
    (0..length).map(|i| i * 2).collect()
}

ghost struct TwoThings {
    a: nat,
    b: nat,
}

pub ghost fn some_op(ghost two_things: TwoThings) -> ghost TwoThings
    ensures return.a == two_things.a + 1,
            return.b == two_things.b
{
    // --> (no) field update syntax? just use the constructor with some fancier (de)construction syntax?
    TwoThings { a: two_things.a + 1, ..two_things } // '..two_things' represents "the other fields of two_things"
}

// for the next example
#[pure]
// not transparent!
pub ghost fn something(a: TwoThings, b: TwoThings) {
    // ...
}

// --> lemmas
#[proof]
pub ghost fn something_transitive(a: TwoThings, b: TwoThings, c: TwoThings)
    requires something(a, b) && something(b, c)
    ensures something(a, c)
{
    // --> calc, reveal
    calc {
        a == by { reveal something; }
        b == by { reveal something; }
        c
    }

    // --> limit proof scope (proof goes before the assertion, contrary to dafny's assert .. by)
    using { reveal something; }
    assert something(a, c),
           potentially_something_else(a, c);
}
