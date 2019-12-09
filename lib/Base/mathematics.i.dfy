module Mathematics {

	function min(a: int, b: int) : int
	{
		if a < b
			then a
		else
			b
	}

	function max(a: int, b: int) : int
	{
		if a < b
			then b
		else
			a
	}

  function Set<T>(ms: multiset<T>) : set<T>
  {
    set x : T | x in ms
  }

  function ISet<T>(ms: set<T>) : iset<T>
  {
    iset x : T | x in ms
  }
}
