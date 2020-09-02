include "total_order.i.dfy"
 
abstract module Lexical_Order refines Total_Order {

  import Entry : Total_Order
    
  type Element = seq<Entry.Element>

  predicate method {:opaque} lte(a: Element, b: Element)
  {
    reveal_ltedef();
    ltedef_properties(a, b);
    ltedef(a, b)
  }

  predicate method {:opaque} ltedef(a: Element, b: Element)
  {
    if |a| == 0 && |b| == 0 then true
    else if |a| == 0       then true
    else if |b| == 0       then false
    else if Entry.lt(a[0], b[0])    then true
    else if Entry.lt(b[0], a[0])    then false
    else ltedef(a[1..], b[1..])
  }

  lemma ltedef_properties(a: Element, b: Element)
  ensures ltedef(a, b) || ltedef(b, a); // Total
  ensures ltedef(a, b) && ltedef(b, a) ==> a == b; // Antisymmetric
  ensures forall a, b, c :: ltedef(a, b) && ltedef(b, c) ==> ltedef(a, c); // Transitivity
  {
    reveal_ltedef();
  }
}

module Seq_Int_Lex_Order refines Lexical_Order {
    import Entry = Integer_Order
}

module Seq_Char_Lex_Order refines Lexical_Order {
    import Entry = Char_Order
}

module String_Lex_Order refines Lexical_Order {
    import Entry = Char_Order
}

// Local Variables:
// tab-width: 4
// End:
