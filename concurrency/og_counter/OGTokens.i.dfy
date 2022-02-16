include "OG.i.dfy"

module OGTokens {
  import OG
  import OGTokens = RwTokens(OG)
  import opened GhostLoc
  import opened Options

  datatype {:glinear_fold} Counter = Counter(ghost loc_s: nat, ghost n: nat)
  {
    function defn(): OGTokens.Token {
      OGTokens.T.Token(
          ExtLoc(loc_s, OGTokens.Wrap.singleton_loc()),
          OG.M(Some(n), None, None))
    }
  }

  datatype {:glinear_fold} IncA = IncA(ghost loc_s: nat, ghost b: bool)
  {
    function defn(): OGTokens.Token {
      OGTokens.T.Token(
          ExtLoc(loc_s, OGTokens.Wrap.singleton_loc()),
          OG.M(None, Some(b), None))
    }
  }

  datatype {:glinear_fold} IncB = IncB(ghost loc_s: nat, ghost b: bool)
  {
    function defn(): OGTokens.Token {
      OGTokens.T.Token(
          ExtLoc(loc_s, OGTokens.Wrap.singleton_loc()),
          OG.M(None, None, Some(b)))
    }
  }

  glinear method do_incA(glinear counter: Counter, glinear inc: IncA)
  returns (glinear counter': Counter, glinear inc': IncA)
  requires counter.loc_s == inc.loc_s
  requires inc.b == false
  ensures counter'.loc_s == inc'.loc_s == counter.loc_s
  ensures counter'.n == counter.n + 1
  ensures inc'.b == true
  {
    glinear var a_token := Counter_unfold(counter);
    glinear var b_token := IncA_unfold(inc);

    ghost var out_expect_a := Counter(counter.loc_s, counter.n + 1);
    ghost var out_token_expect_a := Counter_unfold(out_expect_a);

    ghost var out_expect_b := IncA(inc.loc_s, true);
    ghost var out_token_expect_b := IncA_unfold(out_expect_b);

    OG.DoIncA_is_transition(
        OG.dot(a_token.val, b_token.val),
        OG.dot(out_token_expect_a.val, out_token_expect_b.val));

    glinear var out_token_a, out_token_b := OGTokens.internal_transition_2_2(
      a_token, b_token, out_token_expect_a.val, out_token_expect_b.val
    );

    counter' := Counter_fold(out_expect_a, out_token_a);
    inc' := IncA_fold(out_expect_b, out_token_b);
  }

  glinear method do_incB(glinear counter: Counter, glinear inc: IncB)
  returns (glinear counter': Counter, glinear inc': IncB)
  requires counter.loc_s == inc.loc_s
  requires inc.b == false
  ensures counter'.loc_s == inc'.loc_s == counter.loc_s
  ensures counter'.n == counter.n + 1
  ensures inc'.b == true
  {
    glinear var a_token := Counter_unfold(counter);
    glinear var b_token := IncB_unfold(inc);

    ghost var out_expect_a := Counter(counter.loc_s, counter.n + 1);
    ghost var out_token_expect_a := Counter_unfold(out_expect_a);

    ghost var out_expect_b := IncB(inc.loc_s, true);
    ghost var out_token_expect_b := IncB_unfold(out_expect_b);

    OG.DoIncB_is_transition(
        OG.dot(a_token.val, b_token.val),
        OG.dot(out_token_expect_a.val, out_token_expect_b.val));

    glinear var out_token_a, out_token_b := OGTokens.internal_transition_2_2(
      a_token, b_token, out_token_expect_a.val, out_token_expect_b.val
    );

    counter' := Counter_fold(out_expect_a, out_token_a);
    inc' := IncB_fold(out_expect_b, out_token_b);
  }

  glinear method finalize(glinear counter: Counter, glinear inca: IncA, glinear incb: IncB)
  returns (glinear counter': Counter, glinear inca': IncA, glinear incb': IncB)
  requires counter.loc_s == inca.loc_s == incb.loc_s
  requires inca.b == true
  requires incb.b == true
  ensures counter' == counter
  ensures inca' == inca
  ensures incb' == incb
  ensures counter'.n == 2
  {
    glinear var a_token := Counter_unfold(counter);
    glinear var b_token := IncA_unfold(inca);
    glinear var c_token := IncB_unfold(incb);

    ghost var rest := OGTokens.obtain_invariant_3(inout a_token, inout b_token, inout c_token);
    ghost var full := OG.dot(OG.dot(OG.dot(a_token.val, b_token.val), c_token.val), rest);

    assert full.inc_a.value;
    assert full.inc_b.value;
    assert full.counter.value == 2;
    assert a_token.val.counter.value == 2;

    counter' := Counter_fold(counter, a_token);
    inca' := IncA_fold(inca, b_token);
    incb' := IncB_fold(incb, c_token);
  }

  glinear method og_initialize()
  returns (
      glinear counter: Counter,
      glinear inca: IncA,
      glinear incb: IncB
  )
  ensures counter.loc_s == inca.loc_s == incb.loc_s
  ensures counter.n == 0
  ensures inca.b == false
  ensures incb.b == false
  {
    ghost var m := OG.M(Some(0), Some(false), Some(false));
    OG.InitImpliesInv(m);
    glinear var token := OGTokens.initialize_empty(m);

    ghost var t1 := OG.M(Some(0), None, None);
    ghost var t2 := OG.M(None, Some(false), None);
    ghost var t3 := OG.M(None, None, Some(false));

    glinear var tc1, tc2, tc3 := OGTokens.split3(token, t1, t2, t3);

    counter := Counter_fold(Counter(token.loc.s, 0), tc1);
    inca := IncA_fold(IncA(token.loc.s, false), tc2);
    incb := IncB_fold(IncB(token.loc.s, false), tc3);
  }
}
