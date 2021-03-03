abstract module MonoidMap {
  type M
  type Q
  
  function unit() : M

  function add(x: M, y: M) : M

  lemma associative(x: M, y: M, z: M)
  ensures add(add(x, y), z) == add(x, add(y, z))

  lemma add_unit(x: M)
  ensures add(x, unit()) == x
  ensures add(unit(), x) == x

  function {:opaque} concat(s: seq<M>) : M
  decreases |s|
  ensures |s| == 0 ==> concat(s) == unit()
  ensures |s| == 1 ==> concat(s) == s[0]
  ensures |s| == 2 ==> concat(s) == add(s[0], s[1])
  {

    if |s| == 0 then unit()
    else (
      add_unit(s[0]); /* for |s| == 1 postcondition */
      add(concat(s[..|s|-1]), s[|s|-1])
    )
  }

  lemma concat_additive(s: seq<M>, t: seq<M>)
  ensures concat(s + t) == add(concat(s), concat(t))
  decreases |t|
  {
    if |t| == 0 {
      calc {
        concat(s + t);
        { assert s + t == s; }
        concat(s);
        { add_unit(concat(s)); }
        add(concat(s), concat(t));
      }
    } else {
      calc {
        concat(s + t);
        { reveal_concat(); }
        add(concat((s+t)[..|s+t|-1]), (s+t)[|s+t|-1]);
        {
          assert (s+t)[..|s+t|-1]
              == s + t[..|t|-1];
        }
        add(concat(s + t[..|t|-1]), t[|t|-1]);
        { concat_additive(s, t[..|t|-1]); }
        add(add(concat(s), concat(t[..|t|-1])), t[|t|-1]);
        { associative(concat(s), concat(t[..|t|-1]), t[|t|-1]); }
        add(concat(s), add(concat(t[..|t|-1]), t[|t|-1]));
        { reveal_concat(); }
        add(concat(s), concat(t));
      }
    }
  }

  function f(q: Q) : M

  function {:opaque} concat_map(s: seq<Q>) : M
  decreases |s|
  ensures |s| == 0 ==> concat_map(s) == unit()
  ensures |s| == 1 ==> concat_map(s) == f(s[0])
  ensures |s| == 2 ==> concat_map(s) == add(f(s[0]), f(s[1]))
  {
    if |s| == 0 then unit()
    else (
      add_unit(f(s[0])); /* for |s| == 1 postcondition */
      add(concat_map(s[..|s|-1]), f(s[|s|-1]))
    )
  }

  lemma concat_map_additive(s: seq<Q>, t: seq<Q>)
  ensures concat_map(s + t) == add(concat_map(s), concat_map(t))
  decreases |t|
  {
    if |t| == 0 {
      calc {
        concat_map(s + t);
        { assert s + t == s; }
        concat_map(s);
        { add_unit(concat_map(s)); }
        add(concat_map(s), concat_map(t));
      }
    } else {
      calc {
        concat_map(s + t);
        { reveal_concat_map(); }
        add(concat_map((s+t)[..|s+t|-1]), f((s+t)[|s+t|-1]));
        {
          assert (s+t)[..|s+t|-1]
              == s + t[..|t|-1];
        }
        add(concat_map(s + t[..|t|-1]), f(t[|t|-1]));
        { concat_map_additive(s, t[..|t|-1]); }
        add(add(concat_map(s), concat_map(t[..|t|-1])), f(t[|t|-1]));
        { associative(concat_map(s), concat_map(t[..|t|-1]), f(t[|t|-1])); }
        add(concat_map(s), add(concat_map(t[..|t|-1]), f(t[|t|-1])));
        { reveal_concat_map(); }
        add(concat_map(s), concat_map(t));
      }
    }
  }
}
