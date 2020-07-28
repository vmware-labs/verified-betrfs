// This is, like, half-ghosty
// It doen't really exist in compiled code,
// but the type system treats it as linear
// (unlike most code labeled 'ghost')
linear type Tracker

// `in_intro(t)` is true when we only performed right-movers
predicate in_intro(t: Tracker)

// Mutexes

linear type Mutex<V>

// has(m) means that no thread is currently accessing m.
predicate has<V>(m: Mutex<V>)

function value<V>(m: Mutex<V>) : V
requires has(m)

// The `ensures has(m)` postcondition seems a bit weird.
// Obviously, the actual implementation of `acquire` will block,
// but we're treating the code as atomic (due to mover argument).
method acquire<V>(m: Mutex<V>, t: Tracker)
returns (m': Mutex<V>, v: V, t': Tracker)
requires in_intro(t) // acquire is right-mover
ensures in_intro(t')
ensures has(m)
ensures !has(m')
ensures v == value(m)

method release<V>(m: Mutex<V>, v: V, t: Tracker)
returns (m': Mutex<V>, t': Tracker)
requires !has(m)
ensures !in_intro(t') // release is left-mover
ensures has(m')
ensures value(m') == v
