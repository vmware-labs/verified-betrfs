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

  predicate commutes(a: M, b: M) {
    add(a, b) == add(b, a)
  }

  lemma preserves_1_right_helper(
      table: seq<Q>,
      table': seq<Q>,
      x: M,
      y: M,
      i: int)
  requires |table| == |table'|
  requires forall j | 0 <= j < |table| && i != j :: table'[j] == table[j]
  requires 0 <= i < |table|
  requires add(f(table[i]), x) == add(f(table'[i]), y)
  requires commutes(concat_map(table[i+1..]), x)
  requires commutes(concat_map(table'[i+1..]), y)
  ensures add(concat_map(table), x)
       == add(concat_map(table'), y)
  {
    calc {
      add(concat_map(table), x);
      {
        assert table[..i+1] + table[i+1..] == table;
        concat_map_additive(table[..i+1], table[i+1..]);
      }
      add(
        add(
          concat_map(table[..i+1]),
          concat_map(table[i+1..])),
        x);
      {
        associative(
          concat_map(table[..i+1]),
          concat_map(table[i+1..]),
          x);
      }
      add(
        concat_map(table[..i+1]),
        add(
          concat_map(table[i+1..]),
          x));
      add(
        concat_map(table[..i+1]),
        add(
          x,
          concat_map(table[i+1..])));
      {
        associative(
          concat_map(table[..i+1]),
          x,
          concat_map(table[i+1..]));
      }
      add(
        add(
          concat_map(table[..i+1]),
          x),
        concat_map(table[i+1..]));
      {
        concat_map_additive(table[..i], [table[i]]);
        assert table[..i] + [table[i]] == table[..i+1];
      }
      add(
        add(
          add(
            concat_map(table[..i]),
            f(table[i])
          ),
          x),
        concat_map(table[i+1..]));
      {
        associative(
            concat_map(table[..i]),
            f(table[i]),
            x);
      }
      add(
        add(
          concat_map(table[..i]),
          add(
            f(table[i]),
            x)),
        concat_map(table[i+1..]));
      {
        assert table[..i] == table'[..i];
        assert table[i+1..] == table'[i+1..];
      }
      add(
        add(
          concat_map(table'[..i]),
          add(
            f(table'[i]),
            y)),
        concat_map(table'[i+1..]));
      {
        associative( concat_map(table'[..i]), f(table'[i]), y);
      }
      add( add( add( concat_map(table'[..i]), f(table'[i])), y), concat_map(table'[i+1..]));
      {
        assert table'[..i] + [table'[i]] == table'[..i+1];
        concat_map_additive(table'[..i], [table'[i]]);
      }
      add( add( concat_map(table'[..i+1]), y), concat_map(table'[i+1..]));
      {
        associative( concat_map(table'[..i+1]), y, concat_map(table'[i+1..]));
      }
      add( concat_map(table'[..i+1]), add( y, concat_map(table'[i+1..])));
      add( concat_map(table'[..i+1]), add( concat_map(table'[i+1..]), y));
      {
        associative( concat_map(table'[..i+1]), concat_map(table'[i+1..]), y);
      }
      add( add( concat_map(table'[..i+1]), concat_map(table'[i+1..])), y);
      {
        concat_map_additive(table'[..i+1], table'[i+1..]);
        assert table'[..i+1] + table'[i+1..] == table';
      }
      add(concat_map(table'), y);
    }
  }

  lemma preserves_1_left_helper(
      table: seq<Q>,
      table': seq<Q>,
      x: M,
      y: M,
      i: int)
  requires |table| == |table'|
  requires forall j | 0 <= j < |table| && i != j :: table'[j] == table[j]
  requires 0 <= i < |table|
  requires add(x, f(table[i])) == add(y, f(table'[i]))
  requires commutes(concat_map(table[..i]), x)
  requires commutes(concat_map(table'[..i]), y)
  ensures add(x, concat_map(table))
       == add(y, concat_map(table'))
  {
    calc {
      add(x, concat_map(table));
      {
        concat_map_additive(table[..i], table[i..]);
        assert table[..i] + table[i..] == table;
      }
      add(x,
        add(
          concat_map(table[..i]),
          concat_map(table[i..])));
      {
        associative(x,
          concat_map(table[..i]),
          concat_map(table[i..]));
      }
      add(
        add(
          x,
          concat_map(table[..i])),
        concat_map(table[i..]));
      add(
        add(
          concat_map(table[..i]),
          x),
        concat_map(table[i..]));
      {
        associative(
          concat_map(table[..i]),
          x,
          concat_map(table[i..]));
      }
      add(
        concat_map(table[..i]),
        add(
          x,
          concat_map(table[i..])));
      {
        concat_map_additive([table[i]], table[i+1..]);
        assert [table[i]] + table[i+1..] == table[i..];
      }
      add(
        concat_map(table[..i]),
        add(
          x,
          add(
            f(table[i]),
            concat_map(table[i+1..]))));
      {
        associative(x, f(table[i]),
            concat_map(table[i+1..]));
      }
      add(
        concat_map(table[..i]),
        add(
          add(
            x,
            f(table[i])),
          concat_map(table[i+1..])));
      {
        assert table[..i] == table'[..i];
        assert table[i+1..] == table'[i+1..];
      }
      add(
        concat_map(table'[..i]),
        add(
          add(
            y,
            f(table'[i])),
          concat_map(table'[i+1..])));
      {
        associative(y, f(table'[i]), concat_map(table'[i+1..]));
      }
      add( concat_map(table'[..i]), add( y, add( f(table'[i]), concat_map(table'[i+1..]))));
      {
        assert [table'[i]] + table'[i+1..] == table'[i..];
        concat_map_additive([table'[i]], table'[i+1..]);
      }
      add( concat_map(table'[..i]), add( y, concat_map(table'[i..])));
      {
        associative( concat_map(table'[..i]), y, concat_map(table'[i..]));
      }
      add( add( concat_map(table'[..i]), y), concat_map(table'[i..]));
      add( add( y, concat_map(table'[..i])), concat_map(table'[i..]));
      {
        associative(y, concat_map(table'[..i]), concat_map(table'[i..]));
      }
      add(y, add( concat_map(table'[..i]), concat_map(table'[i..])));
      {
        assert table'[..i] + table'[i..] == table';
        concat_map_additive(table'[..i], table'[i..]);
      }
      add(y, concat_map(table'));
    }
  }

  lemma preserves_1_helper(
      table: seq<Q>,
      table': seq<Q>,
      i: int)
  requires |table| == |table'|
  requires forall j | 0 <= j < |table| && i != j :: table'[j] == table[j]
  requires 0 <= i < |table|
  requires f(table[i]) == f(table'[i])
  ensures concat_map(table)
       == concat_map(table')
  {
    add_unit(f(table[i]));
    add_unit(f(table'[i]));
    add_unit(concat_map(table[..i]));
    add_unit(concat_map(table'[..i]));
    preserves_1_left_helper(table, table', unit(), unit(), i);
    add_unit(concat_map(table));
    add_unit(concat_map(table'));
  }

  lemma preserves_2_helper(table: seq<Q>,
      table': seq<Q>,
      i: int)
  requires |table| == |table'|
  requires forall j | 0 <= j < |table| && j != i && j != i+1 :: table'[j] == table[j]
  requires 0 <= i < |table| - 1
  requires add(f(table[i]), f(table[i+1]))
        == add(f(table'[i]), f(table'[i+1]));
  ensures concat_map(table)
       == concat_map(table')
  {
    calc {
      concat_map(table);
      {
        concat_map_additive(table[..i], table[i..]);
        assert table[..i] + table[i..] == table;
      }
      add(
        concat_map(table[..i]),
        concat_map(table[i..]));
      {
        concat_map_additive([table[i], table[i+1]], table[i+2..]);
        assert [table[i], table[i+1]] + table[i+2..] == table[i..];
      }
      add(
        concat_map(table[..i]),
        add(
          concat_map([table[i], table[i+1]]),
          concat_map(table[i+2..])));
      {
        assert table[..i] == table'[..i];
        calc {
          concat_map([table[i], table[i+1]]);
          add(f(table[i]), f(table[i+1]));
          add(f(table'[i]), f(table'[i+1]));
          concat_map([table'[i], table'[i+1]]);
        }
        assert table[i+2..] == table'[i+2..];
      }
      add(
        concat_map(table'[..i]),
        add(
          concat_map([table'[i], table'[i+1]]),
          concat_map(table'[i+2..])));
      {
        concat_map_additive([table'[i], table'[i+1]], table'[i+2..]);
        assert [table'[i], table'[i+1]] + table'[i+2..] == table'[i..];
      }
      add(
        concat_map(table'[..i]),
        concat_map(table'[i..]));
      {
        concat_map_additive(table'[..i], table'[i..]);
        assert table'[..i] + table'[i..] == table';
      }
      concat_map(table');
    }
  }

}
