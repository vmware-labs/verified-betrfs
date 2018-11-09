datatype Message <Value,Delta> =
	Insert(value: Value) |
	Delete |
	Upsert(delta: Delta)
	
datatype Node <Key, Value, Delta, Applier, Combiner> =
	Leaf(entries: map <Key, Value>) |
	Index(pivots: map <Key, Node>, buffer: map <Key, Message <Value, Delta> >)
	
function sum(a: int, b: int) : int
{
	a + b
}

method dummy(x: int) returns (d: int)
{
	var l := Leaf<int, int, int, sum, sum>(map[7 := 8]);
	d := 0;
}
