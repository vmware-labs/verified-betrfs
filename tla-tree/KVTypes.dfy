module KVTypes {

type Key(!new,==)

predicate KeyLe(a:Key, b:Key)

predicate KeyLeq(a:Key, b:Key) {
    KeyLe(a, b) || a==b
}

function MIN_KEY() : Key
    ensures forall k :: KeyLeq( MIN_KEY(), k)

function MAX_KEY() : Key
    ensures forall k :: KeyLeq(k, MAX_KEY())


type Value(!new,==)
datatype Datum = Datum(key:Key, value:Value)

function EmptyValue() : Value

}
