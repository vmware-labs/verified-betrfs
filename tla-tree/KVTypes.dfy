module KVTypes {

type Key(!new,==)
type Value(!new,==)
datatype Datum = Datum(key:Key, value:Value)

function EmptyValue() : Value

}
