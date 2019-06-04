module Mathematics {

	function method min(a: int, b: int) : int
	{
		if a < b
			then a
		else
			b
	}

	function method max(a: int, b: int) : int
	{
		if a < b
			then b
		else
			a
	}

  function method Set<T>(ms: multiset<T>) : set<T>
  {
    set x : T | x in ms
  }

  function method ISet<T>(ms: set<T>) : iset<T>
  {
    iset x : T | x in ms
  }
}
