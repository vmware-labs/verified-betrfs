
m: mutex

acc(m) // normal acc
write_perm(m)
read_perm(m)

m.x // non-ghosty read requires read_perm(m) (in addition to acc(m) as usual)
m.x := y // write requires write_perm(m) (in addition to acc(m) as usual)

method acquire (m: mutex)
requires acc(m)
ensures acc(m)
ensures write_perm(m)
ensures old(m.has())

method release (m: mutex)
requires acc(m)
requires write_perm(m)
ensures acc(m)
ensures m.has()

method acquire_readonly (m: mutex)
requires acc(m)
ensures acc(m)
ensures read_perm(m)

method release_readonly (m: mutex)
requires acc(m)
requires read_perm(m)
ensures acc(m)





class DummyClassObject {
  // no fields
}

linear datatype acc(ghost o: DummyClassObject)

function {:axiom} read_int(o: DummyClassObject, c: acc)

method {:axiom} write(o: DummyClassObject, c: acc, new_int: int)
returns (c': acc)
requires c.o == o
ensures c'.o == o
ensures read_int(o, c') == new_int



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
