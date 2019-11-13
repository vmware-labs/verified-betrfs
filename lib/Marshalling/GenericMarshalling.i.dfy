include "../NativeTypes.s.dfy"
include "Maps.i.dfy"
include "Seqs.i.dfy"
include "Util.i.dfy"
include "MarshallInt.i.dfy"
include "Native.s.dfy"
include "../Math/bases.i.dfy"
include "../total_order.i.dfy"
include "../../disk-betree/Message.i.dfy"

module GenericMarshalling {
//import opened Util__be_sequences_s
import opened NativeTypes
import opened Collections__Maps_i
import opened Collections__Seqs_i 
import opened Common__Util_i
import opened Common__MarshallInt_i
import opened Libraries__base_s
import opened Options
//import opened Math__power2_i
import opened Native
import opened Math
import KeyType
import ValueMessage`Internal
import ValueWithDefault`Internal

export S
  provides NativeTypes, parse_Val, ParseVal, Marshall, Demarshallable,
      ComputeSizeOf, Options, MarshallVal, lemma_parse_Val_view_specific, lemma_SeqSum_prefix,
      KeyType, ValueMessage, ValueWithDefault
  reveals G, V, ValidGrammar, ValInGrammar, ValidVal, SizeOfV, SeqSum, SeqSumLens, Key, Message, ValidMessage, MessageSize, MessageSizeUint64, SeqSumMessageLens

export extends S

type Key = KeyType.Key
type Message = ValueMessage.Message

datatype G = GUint64
           | GArray(elt:G)
           | GTuple(t:seq<G>)
           | GByteArray
           | GMessage
           | GUint64Array
           | GKeyArray
           | GMessageArray
           | GTaggedUnion(cases:seq<G>)

datatype V = VUint64(u:uint64)
           | VArray(a:seq<V>)
           | VTuple(t:seq<V>)
           | VByteArray(b:seq<byte>)
           | VMessage(m:Message)
           | VKeyArray(baa:seq<Key>)
           | VMessageArray(ma:seq<Message>)
           | VUint64Array(ua:seq<uint64>)
           | VCase(c:uint64, val:V)

predicate ValInGrammar(val:V, grammar:G)
{
    match val
        case VUint64(_) => grammar.GUint64?
        case VArray(a)  => grammar.GArray? && forall v :: v in a ==> ValInGrammar(v, grammar.elt)
        case VTuple(t)  => grammar.GTuple? && |t| == |grammar.t|
                              && forall i :: 0 <= i < |t| ==> ValInGrammar(t[i], grammar.t[i])
        case VByteArray(b) => grammar.GByteArray?
        case VMessage(b) => grammar.GMessage?
        case VKeyArray(b) => grammar.GKeyArray?
        case VMessageArray(b) => grammar.GMessageArray?
        case VUint64Array(ua) => grammar.GUint64Array?
        case VCase(c, v) => grammar.GTaggedUnion? && (c as int) < |grammar.cases| && ValInGrammar(v, grammar.cases[c])
}

// We only support reasonably sized grammars
predicate ValidGrammar(grammar:G) 
{
    match grammar
        case GUint64 => true
        case GArray(elt) => ValidGrammar(elt)
        case GTuple(t) => |t| < 0x1_0000_0000_0000_0000 && (forall g :: g in t ==> ValidGrammar(g))
        case GByteArray => true
        case GMessage => true
        case GKeyArray => true
        case GMessageArray => true
        case GUint64Array => true
        case GTaggedUnion(cases) => |cases| < 0x1_0000_0000_0000_0000 && (forall g :: g in cases ==> ValidGrammar(g))
}

predicate ValidMessage(m: Message)
{
  m != ValueMessage.IdentityMessage()
}

// We can't encode values that are not valid
predicate ValidVal(val:V)
{
    match val
        case VUint64(_)    => true
        case VArray(a)     => |a| < 0x1_0000_0000_0000_0000 && forall v :: v in a ==> ValidVal(v)
        case VTuple(t)     => |t| < 0x1_0000_0000_0000_0000 && forall v :: v in t ==> ValidVal(v)
        case VByteArray(b) => |b| < 0x1_0000_0000_0000_0000
        case VKeyArray(baa) => |baa| < 0x1_0000_0000_0000_0000
        case VMessage(m) => ValidMessage(m)
        case VMessageArray(ma) => |ma| < 0x1_0000_0000_0000_0000 && forall v :: v in ma ==> ValidMessage(v)
        case VUint64Array(ua) => |ua| < 0x1_0000_0000_0000_0000
        case VCase(c, v) => ValidVal(v)

}

function {:opaque} SeqSum(t:seq<V>) : int
    ensures SeqSum(t) >= 0;
{
    if |t| == 0 then 0
    else SizeOfV(t[0]) + SeqSum(t[1..])
}

function {:opaque} SeqSumLens(t:seq<Key>) : int
    ensures SeqSumLens(t) >= 0;
{
    if |t| == 0 then 0
    else Uint64Size() as int + |t[0]| + SeqSumLens(t[1..])
}

function MessageSize(m:Message) : int
ensures MessageSize(m) >= 0
{
  MessageSizeUint64(m) as int
}

function method {:opaque} MessageSizeUint64(m:Message) : uint64
ensures MessageSizeUint64(m) >= 0
{
  if m.Define? then Uint64Size() + |m.value| as uint64 else 0
}


function {:opaque} SeqSumMessageLens(t:seq<Message>) : int
    ensures SeqSumMessageLens(t) >= 0;
{
    if |t| == 0 then 0
    else MessageSize(t[0]) + SeqSumMessageLens(t[1..])
}

function SizeOfV(val:V) : int
    ensures SizeOfV(val) >= 0;
{
    match val
        case VUint64(_)     => 8
        case VArray(a)      => 8 + SeqSum(a)     // 8 bytes for length
        case VTuple(t)      => SeqSum(t)
        case VByteArray(b)  => 8 + |b|          // 8 bytes for a length field
        case VKeyArray(b)  => 8 + SeqSumLens(b)
        case VMessage(m)  => MessageSize(m)
        case VMessageArray(b)  => 8 + SeqSumMessageLens(b)
        case VUint64Array(b)  => 8 + 8*|b|          // 8 bytes for a length field
        case VCase(c, v)  => 8 + SizeOfV(v)     // 8 bytes for the case identifier
}

function method parse_Uint64(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
{
    if (|data| as uint64) >= Uint64Size() then
        (Some(VUint64(SeqByteToUint64(data[..Uint64Size()]))), data[Uint64Size()..])
    else
        (None, [])
}

method ParseUint64(data:seq<byte>, index:uint64) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|
    ensures  var (v', rest') := parse_Uint64(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
{
    lemma_2toX();

    if (|data| as uint64) >= 8 && index <= (|data| as uint64) - 8 {
    // Avoids overflow and equvalent to: if index + 8 < uint64(data.Length) 
        var result := (data[index + (0 as uint64)] as uint64) * 0x1_00_0000_0000_0000
                    + (data[index + (1 as uint64)] as uint64) * 0x1_00_0000_0000_00
                    + (data[index + (2 as uint64)] as uint64) * 0x1_00_0000_0000
                    + (data[index + (3 as uint64)] as uint64) * 0x1_00_0000_00
                    + (data[index + (4 as uint64)] as uint64) * 0x1_00_0000
                    + (data[index + (5 as uint64)] as uint64) * 0x1_00_00
                    + (data[index + (6 as uint64)] as uint64) * 0x1_00
                    + (data[index + (7 as uint64)] as uint64);
        success := true;
        v := VUint64(result);
        rest_index := index + Uint64Size();
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

function {:opaque} parse_Array_contents(data:seq<byte>, eltType:G, len:uint64) : (Option<seq<V>>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    decreases eltType, 1, len;
    ensures var (opt_seq, rest) := parse_Array_contents(data, eltType, len);
            |rest| <= |data| && (opt_seq.Some? ==>
            && |opt_seq.value| == len as int
            && forall i :: 0 <= i < |opt_seq.value| ==> ValidVal(opt_seq.value[i]) && ValInGrammar(opt_seq.value[i], eltType));
{
   if len == 0 then
       (Some([]), data)
   else
       var (val, rest1) := parse_Val(data, eltType);
       var (others, rest2) := parse_Array_contents(rest1, eltType, len - 1);
       if !val.None? && !others.None? then
           (Some([val.value] + others.value), rest2)
       else
           (None, [])
}

datatype ContentsTraceStep = ContentsTraceStep(data:seq<byte>, val:Option<V>)

lemma lemma_ArrayContents_helper(data:seq<byte>, eltType:G, len:uint64, v:seq<V>, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    requires |trace| == (len as int) + 1;
    requires |v| == (len as int);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < (len as int)+1 ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltType).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltType).1;
    requires forall j :: 0 < j < |trace| ==> trace[j].val.Some?;
    requires forall j :: 0 < j < |trace| ==> v[j-1] == trace[j].val.value;
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_Array_contents(data, eltType, len);
             var v_opt := Some(v);
             v_opt == v' && trace[|trace|-1].data == rest';
{
    reveal_parse_Array_contents();
    if len == 0 {
    } else {
        var tuple := parse_Val(data, eltType);
        var val, rest1 := tuple.0, tuple.1;
        assert trace[1].data == rest1;
        assert val.Some?;
        assert trace[1].val == val;
        lemma_ArrayContents_helper(rest1, eltType, len-1, v[1..], trace[1..]);
        var tuple'' := parse_Array_contents(rest1, eltType, len-1);
        var v'', rest'' := tuple''.0, tuple''.1;
        var v_opt'' := Some(v[1..]);
        assert v_opt'' == v'' && trace[1..][|trace[1..]|-1].data == rest'';

        var tuple' := parse_Array_contents(data, eltType, len);
        var v', rest' := tuple'.0, tuple'.1;
        calc { 
            v'; 
            Some([val.value] + v''.value);
            Some([val.value] + v[1..]);
            Some([v[0]] + v[1..]);
                { assert v == [v[0]] + v[1..]; }
            Some(v);
        }
        assert rest' == rest'';
    }
}

lemma lemma_ArrayContents_helper_bailout(data:seq<byte>, eltType:G, len:uint64, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    requires 1 < |trace| <= (len as int) + 1;
    //requires |v| == (len as int);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltType).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltType).1;
    requires forall j :: 0 < j < |trace| - 1 ==> trace[j].val.Some?;
    //requires forall j :: 0 < j < |trace| - 1 ==> v[j-1] == trace[j].val.value;
    requires trace[|trace|-1].val.None?;
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_Array_contents(data, eltType, len);
             v'.None? && rest' == [];
{
    reveal_parse_Array_contents();
    
    var tuple := parse_Val(data, eltType);
    var val, rest1 := tuple.0, tuple.1;
    if |trace| == 2 {
        assert val.None?;
        var tuple' := parse_Array_contents(data, eltType, len);
        var v', rest' := tuple'.0, tuple'.1;
        assert v'.None?;
        assert rest' == [];
    } else {
        lemma_ArrayContents_helper_bailout(rest1, eltType, len-1, trace[1..]);
    }
}

method{:timeLimitMultiplier 2} ParseArrayContents(data:seq<byte>, index:uint64, eltType:G, len:uint64) 
       returns (success:bool, v:seq<V>, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    decreases eltType, 1, len;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Array_contents(data[index..], eltType, len);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(VArray(v));
{
    reveal_parse_Array_contents();
    var vArr := new V[len];
    ghost var g_v := [];
    success := true;
    var i:uint64 := 0;
    var next_val_index:uint64 := index;
    ghost var trace := [ContentsTraceStep(data[index..], None())];

    while i < len
        invariant 0 <= i <= len;
        invariant index <= next_val_index <= (|data| as uint64);
        invariant |trace| == (i as int) + 1;
        invariant |g_v| == (i as int);
        invariant vArr[..i] == g_v;
        invariant trace[0].data == data[index..];
        invariant forall j :: 0 <= j < (i as int)+1 ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
        invariant trace[i].data == data[next_val_index..];
        invariant forall j :: 0 < j <= i ==> trace[j].val.Some?;
        invariant forall j :: 0 < j <= i ==> g_v[j-1] == trace[j].val.value;
        invariant forall j :: 0 < j < (i as int)+1 ==> 
            trace[j].val  == parse_Val(trace[j-1].data, eltType).0
         && trace[j].data == parse_Val(trace[j-1].data, eltType).1
        invariant ValidVal(VArray(vArr[..i]));
    {
        var some1, val, rest1 := ParseVal(data, next_val_index, eltType);
        ghost var step := ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
        ghost var old_trace := trace;
        trace := trace + [step];
        if !some1 {
            success := false;
            rest_index := (|data| as uint64);
            lemma_ArrayContents_helper_bailout(data[index..], eltType, len, trace);
            return;
        }
        g_v := g_v + [val];
        vArr[i] := val;
        next_val_index := rest1;

        i := i + 1;
    }

    success := true;
    rest_index := next_val_index;
    v := vArr[..];               
    lemma_ArrayContents_helper(data[index..], eltType, len, v, trace);
}

function parse_Array(data:seq<byte>, eltType:G) : (Option<V>, seq<byte>)
    requires ValidGrammar(eltType);
    requires |data| < 0x1_0000_0000_0000_0000;
    decreases eltType;
    ensures var (opt_val, rest) := parse_Array(data, eltType);
            |rest| <= |data| && (opt_val.Some? ==>
              && ValidVal(opt_val.value)
              && ValInGrammar(opt_val.value, GArray(eltType)));
{
    var (len, rest) := parse_Uint64(data);
    if !len.None? then
        var (contents, remainder) := parse_Array_contents(rest, eltType, len.value.u);
        if !contents.None? then
            (Some(VArray(contents.value)), remainder)
        else
            (None, [])
    else
        (None, [])
}

method ParseArray(data:seq<byte>, index:uint64, eltType:G) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    decreases eltType;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Array(data[index..], eltType);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some1, len, rest := ParseUint64(data, index);
    if some1 {
        var some2, contents, remainder := ParseArrayContents(data, rest, eltType, len.u);
        if some2 {
            success := true;
            v := VArray(contents);
            rest_index := remainder;
        } else {
            success := false;
            rest_index := (|data| as uint64);
        }
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

function {:opaque} parse_KeyArray_contents(data:seq<byte>, len:uint64) : (Option<seq<Key>>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    decreases len
    ensures var (opt_seq, rest) := parse_KeyArray_contents(data, len);
            |rest| <= |data| && (opt_seq.Some? ==>
            && |opt_seq.value| == len as int
            && (forall i :: 0 <= i < |opt_seq.value| ==> ValidVal(VByteArray(opt_seq.value[i])))
            )
{
   if len == 0 then
       (Some([]), data)
   else
       var (val, rest1) := parse_ByteArray(data);
       var (others, rest2) := parse_KeyArray_contents(rest1, len - 1);
       if !val.None? && !others.None? && |val.value.b| as uint64 <= KeyType.MaxLen() then
           var key : Key := val.value.b;
           (Some([key] + others.value), rest2)
       else
           (None, [])
}

datatype KeyArray_ContentsTraceStep = KeyArray_ContentsTraceStep(data:seq<byte>, val:Option<seq<byte>>)

lemma lemma_KeyArrayContents_helper(data:seq<byte>, len:uint64, v:seq<Key>, trace:seq<KeyArray_ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |trace| == (len as int) + 1;
    requires |v| == (len as int);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> trace[j].val.Some?;
    requires forall j :: 0 < j < (len as int)+1 ==> 
                    Some(VByteArray(trace[j].val.value)) == parse_ByteArray(trace[j-1].data).0
                 && trace[j].data == parse_ByteArray(trace[j-1].data).1;
    requires forall j :: 0 < j < |trace| ==> v[j-1] == trace[j].val.value;
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_KeyArray_contents(data, len);
             var v_opt := Some(v);
             v_opt == v' && trace[|trace|-1].data == rest';
{
    reveal_parse_KeyArray_contents();
    if len == 0 {
    } else {
        var tuple := parse_ByteArray(data);
        var val, rest1 := tuple.0, tuple.1;
        assert trace[1].data == rest1;
        assert val.Some?;
        assert trace[1].val == Some(val.value.b);
        lemma_KeyArrayContents_helper(rest1, len-1, v[1..], trace[1..]);
        var tuple'' := parse_KeyArray_contents(rest1, len-1);
        var v'', rest'' := tuple''.0, tuple''.1;
        var v_opt'' := Some(v[1..]);
        assert v_opt'' == v'' && trace[1..][|trace[1..]|-1].data == rest'';

        var tuple' := parse_KeyArray_contents(data, len);
        var v', rest' := tuple'.0, tuple'.1;
        calc { 
            v'; 
            Some([val.value.b] + v''.value);
            Some([val.value.b] + v[1..]);
            Some([v[0]] + v[1..]);
                { assert v == [v[0]] + v[1..]; }
            Some(v);
        }
        assert rest' == rest'';
    }
}

lemma lemma_KeyArrayContents_helper_bailout(data:seq<byte>, len:uint64, trace:seq<KeyArray_ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires 1 < |trace| <= (len as int) + 1;
    //requires |v| == (len as int);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> 
                    (trace[j].val.None? ==> parse_ByteArray(trace[j-1].data).0.None?)
                 && (trace[j].val.Some? ==> parse_ByteArray(trace[j-1].data).0.Some? && trace[j].val.value  == parse_ByteArray(trace[j-1].data).0.value.b)
                 && trace[j].data == parse_ByteArray(trace[j-1].data).1;
    requires forall j :: 0 < j < |trace| - 1 ==> trace[j].val.Some?;
    //requires forall j :: 0 < j < |trace| - 1 ==> v[j-1] == trace[j].val.value;
    requires trace[|trace|-1].val.None? || |trace[|trace|-1].val.value| > KeyType.MaxLen() as int
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_KeyArray_contents(data, len);
             v'.None? && rest' == [];
{
    reveal_parse_KeyArray_contents();
    
    var tuple := parse_ByteArray(data);
    var val, rest1 := tuple.0, tuple.1;
    if |trace| == 2 {
      if (trace[|trace|-1].val.None?) {
        assert val.None?;
      }
        
      assert val.None? || !(|val.value.b| as uint64 <= KeyType.MaxLen());
      var tuple' := parse_KeyArray_contents(data, len);
      var v', rest' := tuple'.0, tuple'.1;
      assert v'.None?;
      assert rest' == [];
    } else {
      lemma_KeyArrayContents_helper_bailout(rest1, len-1, trace[1..]);
    }
}

method{:timeLimitMultiplier 2} ParseKeyArrayContents(data:seq<byte>, index:uint64, len:uint64) 
       returns (success:bool, v:seq<Key>, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_KeyArray_contents(data[index..], len);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(VKeyArray(v));
{
    reveal_parse_KeyArray_contents();
    var vArr := new Key[len];
    ghost var g_v := [];
    success := true;
    var i:uint64 := 0;
    var next_val_index:uint64 := index;
    ghost var trace := [KeyArray_ContentsTraceStep(data[index..], None())];

    while i < len
        invariant 0 <= i <= len;
        invariant index <= next_val_index <= (|data| as uint64);
        invariant |trace| == (i as int) + 1;
        invariant |g_v| == (i as int);
        invariant vArr[..i] == g_v;
        invariant trace[0].data == data[index..];
        invariant forall j :: 0 <= j < (i as int)+1 ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
        invariant trace[i].data == data[next_val_index..];
        invariant forall j :: 0 < j <= i ==> trace[j].val.Some?;
        invariant forall j :: 0 < j <= i ==> g_v[j-1] == trace[j].val.value;
        invariant forall j :: 0 < j < (i as int)+1 ==> 
            Some(VByteArray(trace[j].val.value)) == parse_ByteArray(trace[j-1].data).0
         && trace[j].data == parse_ByteArray(trace[j-1].data).1
        invariant ValidVal(VKeyArray(vArr[..i]));
    {
        var some1, val, rest1 := ParseByteArray(data, next_val_index);
        ghost var step := KeyArray_ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
        ghost var old_trace := trace;
        trace := trace + [step];
        if !some1 || |val| as uint64 > KeyType.MaxLen() {
            success := false;
            rest_index := (|data| as uint64);
            lemma_KeyArrayContents_helper_bailout(data[index..], len, trace);
            return;
        }
        g_v := g_v + [val];
        vArr[i] := val;
        next_val_index := rest1;

        i := i + 1;
    }

    success := true;
    rest_index := next_val_index;
    v := vArr[..];               
    lemma_KeyArrayContents_helper(data[index..], len, v, trace);
}

function parse_KeyArray(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures var (opt_val, rest) := parse_KeyArray(data);
            |rest| <= |data| && (opt_val.Some? ==>
              && ValidVal(opt_val.value)
              && ValInGrammar(opt_val.value, GKeyArray));
{
    var (len, rest) := parse_Uint64(data);
    if !len.None? then
        var (contents, remainder) := parse_KeyArray_contents(rest, len.value.u);
        if !contents.None? then
            (Some(VKeyArray(contents.value)), remainder)
        else
            (None, [])
    else
        (None, [])
}

method ParseKeyArray(data:seq<byte>, index:uint64) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_KeyArray(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some1, len, rest := ParseUint64(data, index);
    if some1 {
        var some2, contents, remainder := ParseKeyArrayContents(data, rest, len.u);
        if some2 {
            success := true;
            v := VKeyArray(contents);
            rest_index := remainder;
        } else {
            success := false;
            rest_index := (|data| as uint64);
        }
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

function {:opaque} parse_Tuple_contents(data:seq<byte>, eltTypes:seq<G>) : (Option<seq<V>>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 0;
    ensures var (opt_val, rest) := parse_Tuple_contents(data, eltTypes);
            |rest| <= |data| &&
            (opt_val.Some? ==> (|opt_val.value| == |eltTypes|
                              && forall i :: 0 <= i < |opt_val.value| ==> ValidVal(opt_val.value[i]) && ValInGrammar(opt_val.value[i], eltTypes[i])));
{
    if eltTypes == [] then
        (Some([]), data)
    else
        var (val, rest1) := parse_Val(data, eltTypes[(0 as uint64)]);
        assert |rest1| <= |data|;
        var (contents, rest2) := parse_Tuple_contents(rest1, eltTypes[(1 as uint64)..]);
        if !val.None? && !contents.None? then
            (Some([val.value] + contents.value), rest2)
        else
            (None, [])
}


lemma lemma_TupleContents_helper(data:seq<byte>, eltTypes:seq<G>, v:seq<V>, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    requires |trace| == |eltTypes| + 1;
    requires |v| == (|eltTypes| as int);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < (|eltTypes| as int)+1 ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltTypes[j-1]).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltTypes[j-1]).1;
    requires forall j :: 0 < j < |trace| ==> trace[j].val.Some?;
    requires forall j :: 0 < j < |trace| ==> v[j-1] == trace[j].val.value;
    //requires v == ExtractValues(trace[1..]);
    decreases |eltTypes|;
    ensures  var (v', rest') := parse_Tuple_contents(data, eltTypes);
             var v_opt := Some(v);
             v_opt == v' && trace[|trace|-1].data == rest';
{
    reveal_parse_Tuple_contents();
    if |eltTypes| == 0 {
    } else {
        var tuple := parse_Val(data, eltTypes[0]);
        var val, rest1 := tuple.0, tuple.1;
        assert trace[1].data == rest1;
        assert val.Some?;
        assert trace[1].val == val;
        lemma_TupleContents_helper(rest1, eltTypes[1..], v[1..], trace[1..]);
        var tuple'' := parse_Tuple_contents(rest1, eltTypes[1..]);
        var v'', rest'' := tuple''.0, tuple''.1;
        var v_opt'' := Some(v[1..]);
        assert v_opt'' == v'' && trace[1..][|trace[1..]|-1].data == rest'';

        var tuple' := parse_Tuple_contents(data, eltTypes);
        var v', rest' := tuple'.0, tuple'.1;
        calc { 
            v'; 
            Some([val.value] + v''.value);
            Some([val.value] + v[1..]);
            Some([v[0]] + v[1..]);
                { assert v == [v[0]] + v[1..]; }
            Some(v);
        }
        assert rest' == rest'';
    }
}

lemma lemma_TupleContents_helper_bailout(data:seq<byte>, eltTypes:seq<G>, trace:seq<ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    requires 1 < |trace| <= (|eltTypes| as int) + 1;
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> 
                    trace[j].val  == parse_Val(trace[j-1].data, eltTypes[j-1]).0
                 && trace[j].data == parse_Val(trace[j-1].data, eltTypes[j-1]).1;
    requires forall j :: 0 < j < |trace| - 1 ==> trace[j].val.Some?;
    //requires forall j :: 0 < j < |trace| - 1 ==> v[j-1] == trace[j].val.value;
    requires trace[|trace|-1].val.None?;
    //requires v == ExtractValues(trace[1..]);
    decreases |eltTypes|;
    ensures  var (v', rest') := parse_Tuple_contents(data, eltTypes);
             v'.None? && rest' == [];
{
    reveal_parse_Tuple_contents();
    
    var tuple := parse_Val(data, eltTypes[0]);
    var val, rest1 := tuple.0, tuple.1;
    if |trace| == 2 {
        assert val.None?;
        var tuple' := parse_Tuple_contents(data, eltTypes);
        var v', rest' := tuple'.0, tuple'.1;
        assert v'.None?;
        assert rest' == [];
    } else {
        lemma_TupleContents_helper_bailout(rest1, eltTypes[1..], trace[1..]);
    }
}

method{:timeLimitMultiplier 2} ParseTupleContents(data:seq<byte>, index:uint64, eltTypes:seq<G>) 
       returns (success:bool, v:seq<V>, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 0;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Tuple_contents(data[index..], eltTypes);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(VTuple(v));
{
    reveal_parse_Tuple_contents();
    var vArr := new V[(|eltTypes| as uint64)];
    ghost var g_v := [];
    success := true;
    var i:uint64 := 0;
    var next_val_index:uint64 := index;
    ghost var trace := [ContentsTraceStep(data[index..], None())];

    while i < (|eltTypes| as uint64) 
        invariant 0 <= (i as int) <= |eltTypes|;
        invariant index <= next_val_index <= (|data| as uint64);
        invariant |trace| == (i as int) + 1;
        invariant |g_v| == (i as int);
        invariant vArr[..i] == g_v;
        invariant trace[0].data == data[index..];
        invariant forall j :: 0 <= j < (i as int)+1 ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
        invariant trace[i].data == data[next_val_index..];
        invariant forall j :: 0 < j <= i ==> trace[j].val.Some?;
        invariant forall j :: 0 < j <= i ==> g_v[j-1] == trace[j].val.value;
        invariant forall j :: 0 < j < (i as int)+1 ==> 
            trace[j].val  == parse_Val(trace[j-1].data, eltTypes[j-1]).0
         && trace[j].data == parse_Val(trace[j-1].data, eltTypes[j-1]).1
        invariant ValidVal(VTuple(vArr[..i]));
    {
        var some1, val, rest1 := ParseVal(data, next_val_index, eltTypes[i]);
        ghost var step := ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
        ghost var old_trace := trace;
        trace := trace + [step];
        if !some1 {
            success := false;
            rest_index := (|data| as uint64);
            lemma_TupleContents_helper_bailout(data[index..], eltTypes, trace);
            return;
        }
        g_v := g_v + [val];
        vArr[i] := val;
        next_val_index := rest1;

        i := i + 1;
    }

    success := true;
    rest_index := next_val_index;
    v := vArr[..];               
    lemma_TupleContents_helper(data[index..], eltTypes, v, trace);
}

function parse_Tuple(data:seq<byte>, eltTypes:seq<G>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 1;
    ensures var (opt_val, rest) := parse_Tuple(data, eltTypes);
            |rest| <= |data| && (opt_val.Some? ==> ValidVal(opt_val.value) && ValInGrammar(opt_val.value, GTuple(eltTypes)));
{
    var (contents, rest) := parse_Tuple_contents(data, eltTypes);
    if !contents.None? then
        (Some(VTuple(contents.value)), rest)
    else
        (None, [])
}


method ParseTuple(data:seq<byte>, index:uint64, eltTypes:seq<G>) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in eltTypes ==> ValidGrammar(elt);
    decreases eltTypes, 1;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Tuple(data[index..], eltTypes);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some, contents, rest := ParseTupleContents(data, index, eltTypes);
    if some {
        success := true;
        v := VTuple(contents);
        rest_index := rest;
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

function method parse_ByteArray(data:seq<byte>) : (res: (Option<V>, seq<byte>))
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures |res.1| < 0x1_0000_0000_0000_0000;
{
    var (len, rest) := parse_Uint64(data);
    if !len.None? && len.value.u <= (|rest| as uint64) then
        (Some(VByteArray(rest[(0 as uint64)..len.value.u])), rest[len.value.u..])
    else
        (None, [])
}

method ParseByteArray(data:seq<byte>, index:uint64) returns (success:bool, v:seq<byte>, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_ByteArray(data[index..]);
             var v_opt := if success then Some(VByteArray(v)) else None();
             v_opt == v' && data[rest_index..] == rest';
{
    var some, len, rest := ParseUint64(data, index);
    if some && len.u <= (|data| as uint64) - rest {
        ghost var rest_seq := data[rest..];
        assert len.u <= (|rest_seq| as uint64);
        calc {
            rest_seq[0..len.u];
            data[rest..rest + len.u];
        }
        success := true;
        v := data[rest..rest + len.u];
        rest_index := rest + len.u;
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

function SeqByteToSeqUint64(bytes: seq<byte>, l: int) : (us : seq<uint64>)
  requires |bytes| == Uint64Size() as int * l
  ensures |us| == l
{
  if l == 0 then [] else SeqByteToSeqUint64(bytes[0 .. (l-1) * Uint64Size() as int], l-1) + [SeqByteToUint64(bytes[(l-1) * Uint64Size() as int .. ])]
}

function parse_Uint64Array(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
{
    var (len, rest) := parse_Uint64(data);
    if !len.None? && len.value.u <= (|rest| as uint64) / Uint64Size() then
        (Some(VUint64Array(SeqByteToSeqUint64(rest[..Uint64Size()*len.value.u], len.value.u as int))), rest[Uint64Size()*len.value.u..])
    else
        (None, [])
}

method parseUint64ArrayContents(data:seq<byte>, index: uint64, len: uint64) returns (s : seq<uint64>)
    requires (index as int) + (Uint64Size() as int) * (len as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  s == SeqByteToSeqUint64(data[index .. index as int + len as int * Uint64Size() as int], len as int)
{
  lemma_2toX();

  var ar := new uint64[len];
  var j: uint64 := 0;
  while j < len
  invariant 0 <= j <= len
  invariant ar[..j] == SeqByteToSeqUint64(data[index .. index as int + j as int * Uint64Size() as int], j as int)
  {
    ar[j] :=    (data[index + 8*j + (0 as uint64)] as uint64) * 0x1_00_0000_0000_0000
              + (data[index + 8*j + (1 as uint64)] as uint64) * 0x1_00_0000_0000_00
              + (data[index + 8*j + (2 as uint64)] as uint64) * 0x1_00_0000_0000
              + (data[index + 8*j + (3 as uint64)] as uint64) * 0x1_00_0000_00
              + (data[index + 8*j + (4 as uint64)] as uint64) * 0x1_00_0000
              + (data[index + 8*j + (5 as uint64)] as uint64) * 0x1_00_00
              + (data[index + 8*j + (6 as uint64)] as uint64) * 0x1_00
              + (data[index + 8*j + (7 as uint64)] as uint64);

    assert ar[j] == SeqByteToUint64(data[index + 8*j .. index + 8*(j+1)]);
    assert ar[..j] == ar[..j+1][..j];
    assert data[index .. index as int + j as int * Uint64Size() as int]
        == data[index .. index as int + (j + 1) as int * Uint64Size() as int][0 .. j * Uint64Size()];

    j := j + 1;
  }
  s := ar[..];
}

method ParseUint64Array(data:seq<byte>, index: uint64) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Uint64Array(data[index..]);
             var v_opt := if success then Some(v) else None();
             && v_opt == v'
             && data[rest_index..] == rest';
{
    var some, len, rest := ParseUint64(data, index);
    if some && len.u <= ((|data| as uint64) - rest) / Uint64Size() {
        ghost var rest_seq := data[rest..];
        assert len.u as int * Uint64Size() as int <= |rest_seq|;
        calc {
            rest_seq[0..len.u];
            data[rest..rest + len.u];
        }
        success := true;
        var contents := parseUint64ArrayContents(data, index + Uint64Size(), len.u);
        v := VUint64Array(contents);
        rest_index := rest + len.u * Uint64Size();

        assert data[index as int + Uint64Size() as int .. index as int + Uint64Size() as int + len.u as int * Uint64Size() as int]
            == rest_seq[..Uint64Size() as int * len.u as int];
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

function parse_Case(data:seq<byte>, cases:seq<G>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |cases| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in cases ==> ValidGrammar(elt);
    decreases cases;
    ensures var (opt_val, rest) := parse_Case(data, cases);
            |rest| <= |data| && (opt_val.Some? ==> ValidVal(opt_val.value) && ValInGrammar(opt_val.value, GTaggedUnion(cases)));
{
    var (caseID, rest1) := parse_Uint64(data);

    if !caseID.None? && caseID.value.u < (|cases| as uint64) then
        var (val, rest2) := parse_Val(rest1, cases[caseID.value.u]);
        if !val.None? then
            (Some(VCase(caseID.value.u, val.value)), rest2)
        else
            (None, [])
    else
        (None, [])
}

method ParseCase(data:seq<byte>, index:uint64, cases:seq<G>) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |cases| < 0x1_0000_0000_0000_0000;
    requires forall elt :: elt in cases ==> ValidGrammar(elt);
    decreases cases;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Case(data[index..], cases);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some1, caseID, rest1 := ParseUint64(data, index);

    if some1 && caseID.u < (|cases| as uint64) {
        var some2, val, rest2 := ParseVal(data, rest1, cases[caseID.u]);
        if some2 {
            success := true;
            v := VCase(caseID.u, val);
            rest_index := rest2;
        } else {
            success := false;
            rest_index := (|data| as uint64);
        }
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

function {:opaque} parse_Val(data:seq<byte>, grammar:G) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(grammar);
    decreases grammar, 0;
    ensures  var (val, rest) := parse_Val(data, grammar);
             |rest| <= |data| && (!val.None? ==> ValidVal(val.value) && ValInGrammar(val.value, grammar));
{
    match grammar
        case GUint64             => parse_Uint64(data)
        case GArray(elt)         => parse_Array(data, elt)
        case GTuple(t)           => parse_Tuple(data, t)
        case GByteArray          => parse_ByteArray(data)
        case GMessage            => (
          var (v, rest) := parse_Message(data);
          (if v.Some? then Some(VMessage(v.value)) else None, rest)
        )
        case GUint64Array        => parse_Uint64Array(data)
        case GKeyArray           => parse_KeyArray(data)
        case GMessageArray       => parse_MessageArray(data)
        case GTaggedUnion(cases) => parse_Case(data, cases)
}

method ParseVal(data:seq<byte>, index:uint64, grammar:G) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(grammar);
    decreases grammar, 0;
    ensures  (rest_index as int) <= |data|
    ensures  var (v', rest') := parse_Val(data[index..], grammar);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    reveal_parse_Val();

    match grammar {
        case GUint64             => success, v, rest_index := ParseUint64(data, index);
        case GArray(elt)         => success, v, rest_index := ParseArray(data, index, elt);
        case GTuple(t)           => success, v, rest_index := ParseTuple(data, index, t);
        case GByteArray          => {
          var v';
          success, v', rest_index := ParseByteArray(data, index);
          v := VByteArray(v'); 
        }
        case GMessage            => {
          var v';
          success, v', rest_index := ParseMessage(data, index);
          v := VMessage(v'); 
        }
        case GUint64Array          => success, v, rest_index := ParseUint64Array(data, index);
        case GKeyArray           => success, v, rest_index := ParseKeyArray(data, index);
        case GMessageArray       => success, v, rest_index := ParseMessageArray(data, index);
        case GTaggedUnion(cases) => success, v, rest_index := ParseCase(data, index, cases);
    }
}

predicate Demarshallable(data:seq<byte>, grammar:G)
{
       |data| < 0x1_0000_0000_0000_0000
    && ValidGrammar(grammar)
    && !parse_Val(data, grammar).0.None?
    && ValidVal(parse_Val(data, grammar).0.value)
    && parse_Val(data, grammar).1 == []
}

function DemarshallFunc(data:seq<byte>, grammar:G) : V
    requires Demarshallable(data, grammar);
    decreases grammar, 0;
    ensures  var (val, rest) := parse_Val(data, grammar);
             !val.None? && ValInGrammar(val.value, grammar);
{
    parse_Val(data, grammar).0.value
}

method Demarshall(data:seq<byte>, grammar:G) returns (success:bool, v:V)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(grammar);
    ensures  success == Demarshallable(data, grammar);
    ensures  success ==> v == DemarshallFunc(data, grammar);
{
    var rest:uint64;
    success, v, rest := ParseVal(data, 0, grammar);
    if success && rest == (|data| as uint64) {
        assert v == parse_Val(data[..], grammar).0.value;
        assert Demarshallable(data[..], grammar);
        assert v == DemarshallFunc(data[..], grammar);
    } else {
        success := false;
        assert !Demarshallable(data[..], grammar);
    }
}


lemma lemma_parse_Val_view_ByteArray(data:seq<byte>, v:V, grammar:G, index:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GByteArray?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    ensures  forall bound :: Trigger(bound) ==> (index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v))));
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             parse_ByteArray(data[index..bound]).0 == Some(v) ==> parse_ByteArray(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
{
    forall bound {:trigger Trigger(bound)} | Trigger(bound)
        ensures index+SizeOfV(v) <= bound <= |data| ==> ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v)));
    {
        if index+SizeOfV(v) <= bound <= |data| {
            var narrow_tuple := parse_ByteArray(data[index..index+SizeOfV(v)]);
            var bound_tuple := parse_ByteArray(data[index..bound]);
            var narrow_len_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
            var bound_len_tuple := parse_Uint64(data[index..bound]);
            assert narrow_len_tuple.0 == bound_len_tuple.0;

            if bound_tuple.0 == Some(v) {
                assert bound_len_tuple.1[0..bound_len_tuple.0.value.u] == narrow_len_tuple.1[0..bound_len_tuple.0.value.u];     // OBSERVE
            }

            if narrow_tuple.0 == Some(v) {
                assert bound_len_tuple.1[0..bound_len_tuple.0.value.u] == narrow_len_tuple.1[0..bound_len_tuple.0.value.u];       // OBSERVE
            }
            assert ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v)));
        }
        assert index+SizeOfV(v) <= bound <= |data| ==> ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v)));
    }
    assert forall bound :: Trigger(bound) ==> (index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_ByteArray(data[index..bound]).0 == Some(v)) <==> (parse_ByteArray(data[index..index+SizeOfV(v)]).0 == Some(v))));
    assert forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             parse_ByteArray(data[index..bound]).0 == Some(v) ==> parse_ByteArray(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
}

lemma lemma_parse_Val_view_Message(data:seq<byte>, v:V, grammar:G, index:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GMessage?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    ensures  forall bound :: Trigger(bound) ==> (index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_Message(data[index..bound]).0 == Some(v.m)) <==> (parse_Message(data[index..index+SizeOfV(v)]).0 == Some(v.m))));
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             parse_Message(data[index..bound]).0 == Some(v.m) ==> parse_Message(data[index..bound]).1 == data[index+SizeOfV(v)..bound];

lemma lemma_parse_Val_view_Uint64Array(data:seq<byte>, v:V, grammar:G, index:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GUint64Array?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    ensures  forall bound :: Trigger(bound) ==> (index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_Uint64Array(data[index..bound]).0 == Some(v)) <==> (parse_Uint64Array(data[index..index+SizeOfV(v)]).0 == Some(v))));
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             parse_Uint64Array(data[index..bound]).0 == Some(v) ==> parse_Uint64Array(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
{
  forall bound | Trigger(bound) && index+SizeOfV(v) <= bound <= |data|
  ensures (parse_Uint64Array(data[index..bound]).0 == Some(v)) ==> (parse_Uint64Array(data[index..index+SizeOfV(v)]).0 == Some(v))
  ensures (parse_Uint64Array(data[index..index+SizeOfV(v)]).0 == Some(v)) ==> (parse_Uint64Array(data[index..bound]).0 == Some(v))
  {
    var len := |v.ua|;

    assert parse_Uint64(data[index..bound]).0
        == parse_Uint64(data[index..index + SizeOfV(v)]).0;
    assert parse_Uint64(data[index..bound]).1 == data[index..bound][8..];
    assert parse_Uint64(data[index..index + SizeOfV(v)]).1 == data[index..index + SizeOfV(v)][8..];
    assert data[index..bound][8..][..8*len] == data[index..index + SizeOfV(v)][8..][..8*len];

    var l := parse_Uint64(data[index..]).0;
    if (l.Some? && l.value.u as int == len) {
      assert parse_Uint64Array(data[index..bound]).0
          == parse_Uint64Array(data[index..index + SizeOfV(v)]).0;
    }
  }

  forall bound | index+SizeOfV(v) <= bound <= |data| && parse_Uint64Array(data[index..bound]).0 == Some(v)
  ensures parse_Uint64Array(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
  {
  }
}

lemma lemma_SeqSumLens_prefix(s:seq<Key>, v:Key)
    ensures SeqSumLens(s + [v]) == SeqSumLens(s) + 8 + |v|
{
    reveal_SeqSumLens();
    if |s| == 0 {
    } else {
        calc {
            SeqSumLens(s + [v]);
                { assert (s + [v])[0] == s[0];  
                  assert (s + [v])[1..] == s[1..]+[v]; }
            8 + |s[0]| + SeqSumLens(s[1..] + [v]);
                { lemma_SeqSumLens_prefix(s[1..], v); }
            8 + |s[0]| + SeqSumLens(s[1..]) + 8 + |v|;
            SeqSumLens(s) + 8 + |v|;
        }
    }
}

lemma lemma_SeqSumMessageLens_prefix(s:seq<Message>, v:Message)
    ensures SeqSumMessageLens(s + [v]) == SeqSumMessageLens(s) + MessageSize(v)
{
    reveal_SeqSumMessageLens();
    if |s| == 0 {
    } else {
        calc {
            SeqSumMessageLens(s + [v]);
                { assert (s + [v])[0] == s[0];  
                  assert (s + [v])[1..] == s[1..]+[v]; }
            MessageSize(s[0]) + SeqSumMessageLens(s[1..] + [v]);
                { lemma_SeqSumMessageLens_prefix(s[1..], v); }
            MessageSize(s[0]) + SeqSumMessageLens(s[1..]) + MessageSize(v);
            SeqSumMessageLens(s) + MessageSize(v);
        }
    }
}


lemma lemma_SeqSum_prefix(s:seq<V>, v:V)
    ensures SeqSum(s + [v]) == SeqSum(s) + SizeOfV(v);
{
    reveal_SeqSum();
    if |s| == 0 {
    } else {
        calc {
            SeqSum(s + [v]);
                { assert (s + [v])[0] == s[0];  
                  assert (s + [v])[1..] == s[1..]+[v]; }
            SizeOfV(s[0]) + SeqSum(s[1..] + [v]);
                { lemma_SeqSum_prefix(s[1..], v); }
            SizeOfV(s[0]) + SeqSum(s[1..]) + SizeOfV(v);
            SeqSum(s) + SizeOfV(v);
        }
    }
}

lemma lemma_SeqSumLens_bound(s:seq<Key>, bound:int)
    requires SeqSumLens(s) < bound;
    ensures  forall v :: v in s ==> 8 + |v| < bound;
{
    reveal_SeqSumLens();
    if |s| == 0 {
    } else {
        assert 8 + |s[0]| + SeqSumLens(s[1..]) < bound;
        assert 8 + |s[0]| < bound;
        lemma_SeqSumLens_bound(s[1..], bound);
    }
}

lemma lemma_SeqSumMessageLens_bound(s:seq<Message>, bound:int)
    requires SeqSumMessageLens(s) < bound;
    ensures  forall v :: v in s ==> MessageSize(v) < bound;
{
    reveal_MessageSizeUint64();
    reveal_SeqSumMessageLens();
    if |s| == 0 {
    } else {
        assert MessageSize(s[0]) + SeqSumMessageLens(s[1..]) < bound;
        assert MessageSize(s[0]) < bound;
        lemma_SeqSumMessageLens_bound(s[1..], bound);
    }
}

lemma lemma_SeqSum_bound(s:seq<V>, bound:int)
    requires SeqSum(s) < bound;
    ensures  forall v :: v in s ==> SizeOfV(v) < bound;
{
    reveal_SeqSum();
    if |s| == 0 {
    } else {
        assert SizeOfV(s[0]) + SeqSum(s[1..]) < bound;
        assert SizeOfV(s[0]) < bound;
        lemma_SeqSum_bound(s[1..], bound);
    }
}

lemma lemma_SeqSumLens_bound_prefix(s:seq<Key>, prefix:seq<Key>, index:int)
    requires 0 <= index <= |s|;
    requires prefix == s[..index];
    ensures  SeqSumLens(prefix) <= SeqSumLens(s);
{
    reveal_SeqSumLens();
    if |prefix| == 0 {
    } else {
        lemma_SeqSumLens_bound_prefix(s[1..], prefix[1..], index - 1);
    }
}

lemma lemma_SeqSumMessageLens_bound_prefix(s:seq<Message>, prefix:seq<Message>, index:int)
    requires 0 <= index <= |s|;
    requires prefix == s[..index];
    ensures  SeqSumMessageLens(prefix) <= SeqSumMessageLens(s);
{
    reveal_SeqSumMessageLens();
    if |prefix| == 0 {
    } else {
        lemma_SeqSumMessageLens_bound_prefix(s[1..], prefix[1..], index - 1);
    }
}



lemma lemma_SeqSum_bound_prefix(s:seq<V>, prefix:seq<V>, index:int)
    requires 0 <= index <= |s|;
    requires prefix == s[..index];
    ensures  SeqSum(prefix) <= SeqSum(s);
{
    reveal_SeqSum();
    if |prefix| == 0 {
    } else {
        lemma_SeqSum_bound_prefix(s[1..], prefix[1..], index - 1);
    }
}

lemma lemma_parse_Array_contents_len(data:seq<byte>, eltType:G, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValidGrammar(eltType);
    requires len >= 0;
    requires !parse_Array_contents(data, eltType, len).0.None?;
    decreases len;
    ensures  (len as int) == |parse_Array_contents(data, eltType, len).0.value|;
{
    reveal_parse_Array_contents();
    if len == 0 {
    } else {
       var tuple1 := parse_Val(data, eltType);
       var val   := tuple1.0;
       var rest1 := tuple1.1;
       var tuple2 := parse_Array_contents(rest1, eltType, len - 1);
       var others := tuple2.0;
       var rest2  := tuple2.1;
       assert !val.None? && !others.None?;
       lemma_parse_Array_contents_len(rest1, eltType, len - 1);
    }
}

lemma lemma_parse_Val_view_Array_contents(data:seq<byte>, vs:seq<V>, grammar:G, index:int, bound:int, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires forall v :: v in vs ==> ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires (len as int) == |vs|;
    requires 0 <= index <= |data|;
    requires 0 <= index + SeqSum(vs) <= |data|;
    requires index+SeqSum(vs) <= bound <= |data|;
    decreases grammar, 1, len;
    //decreases |vs|;
    ensures  (parse_Array_contents(data[index..bound], grammar, len).0 == Some(vs)) <==> (parse_Array_contents(data[index..index+SeqSum(vs)], grammar, len).0 == Some(vs));
    ensures  parse_Array_contents(data[index..bound], grammar, len).0 == Some(vs) ==> parse_Array_contents(data[index..bound], grammar, len).1 == data[index+SeqSum(vs)..bound];
{
    reveal_parse_Array_contents();
    if len == 0 {
        reveal_SeqSum();
    } else {
        var narrow_tuple := parse_Array_contents(data[index..index+SeqSum(vs)], grammar, len);
        var bound_tuple := parse_Array_contents(data[index..bound], grammar, len);
        var narrow_val_tuple := parse_Val(data[index..index+SeqSum(vs)], grammar);
        var bound_val_tuple := parse_Val(data[index..bound], grammar);
        var narrow_contents_tuple := parse_Array_contents(narrow_val_tuple.1, grammar, len - 1);
        var bound_contents_tuple := parse_Array_contents(bound_val_tuple.1, grammar, len - 1);


        if narrow_tuple.0 == Some(vs) {
            assert !narrow_val_tuple.0.None? && !narrow_contents_tuple.0.None?;
            calc {
                index + SeqSum(vs) <= |data|;
                SeqSum(vs) <= |data| - index;
                SeqSum(vs) < |data| - index + 1;
            }
            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar, index);

            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            lemma_SeqSum_bound(vs, bound - index + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;     // OBSERVE (trigger on forall?)
            assert (parse_Val(data[index..bound], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            assert narrow_val_tuple.0.value == vs[0] == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(narrow_val_tuple.0.value);
            calc {
                SizeOfV(narrow_val_tuple.0.value) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Array_contents(data, vs[1..], grammar, new_index, bound, len - 1);

            assert (parse_Array_contents(data[new_index..bound], grammar, len - 1).0 == Some(vs[1..])) <==> (parse_Array_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar, len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert bound_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else if bound_tuple.0 == Some(vs) {
            assert !bound_val_tuple.0.None? && !bound_contents_tuple.0.None?;

            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar, index);
            // This is exactly the ensures of the lemma above
            assert forall bound' :: index+SizeOfV(vs[0]) <= bound' <= |data| ==>
                   ((parse_Val(data[index..bound'], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0])));

            lemma_SeqSum_bound(vs, bound - index + 1);
            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= index+SeqSum(vs) <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            assert (parse_Val(data[index..bound], grammar).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar).0 == Some(vs[0]));
            assert narrow_val_tuple.0.value == vs[0] == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(narrow_val_tuple.0.value);
            calc {
                SizeOfV(narrow_val_tuple.0.value) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Array_contents(data, vs[1..], grammar, new_index, bound, len - 1);

            assert (parse_Array_contents(data[new_index..bound], grammar, len - 1).0 == Some(vs[1..])) <==> (parse_Array_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar, len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert narrow_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else {
            // Doesn't matter for our ensures clause
        }
    }
}

lemma lemma_parse_Val_view_Array(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GArray?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    decreases grammar, -1;
    ensures  (parse_Array(data[index..bound], grammar.elt).0 == Some(v)) <==> (parse_Array(data[index..index+SizeOfV(v)], grammar.elt).0 == Some(v));
    ensures  parse_Array(data[index..bound], grammar.elt).0 == Some(v) ==> parse_Array(data[index..bound], grammar.elt).1 == data[index+SizeOfV(v)..bound];
{
    var narrow_tuple := parse_Array(data[index..index+SizeOfV(v)], grammar.elt);
    var bound_tuple := parse_Array(data[index..bound], grammar.elt);
    var narrow_len_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
    var bound_len_tuple := parse_Uint64(data[index..bound]);
    var narrow_contents_tuple := parse_Array_contents(narrow_len_tuple.1, grammar.elt, narrow_len_tuple.0.value.u);
    var bound_contents_tuple := parse_Array_contents(bound_len_tuple.1, grammar.elt, bound_len_tuple.0.value.u);

    assert narrow_len_tuple.0 == bound_len_tuple.0;

    if bound_tuple.0 == Some(v) {
        assert parse_Array_contents(bound_len_tuple.1, grammar.elt, bound_len_tuple.0.value.u).0 == Some(v.a);   // OBSERVE
        lemma_parse_Array_contents_len(bound_len_tuple.1, grammar.elt, narrow_len_tuple.0.value.u);
        lemma_parse_Val_view_Array_contents(data, v.a, grammar.elt, index+8, bound, narrow_len_tuple.0.value.u);
    }

    if narrow_tuple.0 == Some(v) {
        assert parse_Array_contents(narrow_len_tuple.1, grammar.elt, narrow_len_tuple.0.value.u).0 == Some(v.a);   // OBSERVE
        lemma_parse_Array_contents_len(narrow_len_tuple.1, grammar.elt, narrow_len_tuple.0.value.u);
        lemma_parse_Val_view_Array_contents(data, v.a, grammar.elt, index+8, bound, narrow_len_tuple.0.value.u);
    }
}

lemma lemma_parse_KeyArray_contents_len(data:seq<byte>, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires len >= 0;
    requires !parse_KeyArray_contents(data, len).0.None?;
    decreases len;
    ensures  (len as int) == |parse_KeyArray_contents(data, len).0.value|;
{
    reveal_parse_KeyArray_contents();
    if len == 0 {
    } else {
       var tuple1 := parse_ByteArray(data);
       var val   := tuple1.0;
       var rest1 := tuple1.1;
       var tuple2 := parse_KeyArray_contents(rest1, len - 1);
       var others := tuple2.0;
       var rest2  := tuple2.1;
       assert !val.None? && !others.None?;
       lemma_parse_KeyArray_contents_len(rest1, len - 1);
    }
}

lemma lemma_parse_KeyArray_contents_first(data:seq<byte>, len: uint64, vs: seq<Key>)
requires |data| < 0x1_0000_0000_0000_0000;
requires parse_KeyArray_contents(data, len).0 == Some(vs)
requires len > 0
ensures parse_ByteArray(data).0.Some?
ensures parse_ByteArray(data).0.value == VByteArray(vs[0])
{
  reveal_parse_KeyArray_contents();
}

lemma {:fuel parse_ByteArray,0} lemma_parse_Val_view_KeyArray_contents(data:seq<byte>, vs:seq<Key>, index:int, bound:int, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires (len as int) == |vs|;
    requires 0 <= index <= |data|;
    requires 0 <= index + SeqSumLens(vs) <= |data|;
    requires index+SeqSumLens(vs) <= bound <= |data|;
    decreases len;
    //decreases |vs|;
    ensures  (parse_KeyArray_contents(data[index..bound], len).0 == Some(vs)) <==> (parse_KeyArray_contents(data[index..index+SeqSumLens(vs)], len).0 == Some(vs));
    ensures  parse_KeyArray_contents(data[index..bound], len).0 == Some(vs) ==> parse_KeyArray_contents(data[index..bound], len).1 == data[index+SeqSumLens(vs)..bound];
{
    reveal_parse_KeyArray_contents();
    if len == 0 {
        reveal_SeqSumLens();
    } else {
        var narrow_tuple := parse_KeyArray_contents(data[index..index+SeqSumLens(vs)], len);
        var bound_tuple := parse_KeyArray_contents(data[index..bound], len);
        var narrow_val_tuple := parse_ByteArray(data[index..index+SeqSumLens(vs)]);
        var bound_val_tuple := parse_ByteArray(data[index..bound]);
        var narrow_contents_tuple := parse_KeyArray_contents(narrow_val_tuple.1, len - 1);
        var bound_contents_tuple := parse_KeyArray_contents(bound_val_tuple.1, len - 1);


        if narrow_tuple.0 == Some(vs) {
            assert !narrow_val_tuple.0.None? && !narrow_contents_tuple.0.None?;
            calc {
                index + SeqSumLens(vs) <= |data|;
                SeqSumLens(vs) <= |data| - index;
                SeqSumLens(vs) < |data| - index + 1;
            }
            lemma_SeqSumLens_bound(vs, |data| - index + 1);
            lemma_parse_Val_view_ByteArray(data, VByteArray(vs[0]), GByteArray, index);

            lemma_SeqSumLens_bound(vs, SeqSumLens(vs) + 1);
            assert index+SizeOfV(VByteArray(vs[0])) <= bound <= |data|;
            assert (parse_ByteArray(data[index..index+SeqSumLens(vs)]).0 == Some(VByteArray(vs[0]))) <==> (parse_ByteArray(data[index..index+SizeOfV(VByteArray(vs[0]))]).0 == Some(VByteArray(vs[0])));
            lemma_SeqSumLens_bound(vs, bound - index + 1);
            assert index+SizeOfV(VByteArray(vs[0])) <= bound <= |data|;     // OBSERVE (trigger on forall?)
            assert (parse_ByteArray(data[index..bound]).0 == Some(VByteArray(vs[0]))) <==> (parse_ByteArray(data[index..index+SizeOfV(VByteArray(vs[0]))]).0 == Some(VByteArray(vs[0])));
            lemma_parse_KeyArray_contents_first(data[index..index+SeqSumLens(vs)], len, vs);
            assert narrow_val_tuple.0.value == VByteArray(vs[0])
                == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(narrow_val_tuple.0.value);
            calc {
                SizeOfV(narrow_val_tuple.0.value) + SeqSumLens(vs[1..]);
                    { reveal_SeqSumLens(); }
                SeqSumLens(vs);
            }
            assert new_index+SeqSumLens(vs[1..]) <= bound;

            lemma_parse_Val_view_KeyArray_contents(data, vs[1..], new_index, bound, len - 1);

            assert (parse_KeyArray_contents(data[new_index..bound], len - 1).0 == Some(vs[1..])) <==> (parse_KeyArray_contents(data[new_index..new_index+SeqSumLens(vs[1..])], len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSumLens(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert bound_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else if bound_tuple.0 == Some(vs) {
            assert !bound_val_tuple.0.None? && !bound_contents_tuple.0.None?;

            lemma_SeqSumLens_bound(vs, |data| - index + 1);
            lemma_parse_Val_view_ByteArray(data, VByteArray(vs[0]), GByteArray, index);
            // This is exactly the ensures of the lemma above
            assert forall bound' :: index+SizeOfV(VByteArray(vs[0])) <= bound' <= |data| ==>
                   ((parse_ByteArray(data[index..bound']).0 == Some(VByteArray(vs[0]))) <==> (parse_ByteArray(data[index..index+SizeOfV(VByteArray(vs[0]))]).0 == Some(VByteArray(vs[0]))));

            lemma_SeqSumLens_bound(vs, bound - index + 1);
            lemma_SeqSumLens_bound(vs, SeqSumLens(vs) + 1);
            assert index+SizeOfV(VByteArray(vs[0])) <= index+SeqSumLens(vs) <= |data|;
            assert (parse_ByteArray(data[index..index+SeqSumLens(vs)]).0 == Some(VByteArray(vs[0]))) <==> (parse_ByteArray(data[index..index+SizeOfV(VByteArray(vs[0]))]).0 == Some(VByteArray(vs[0])));
            assert (parse_ByteArray(data[index..bound]).0 == Some(VByteArray(vs[0]))) <==> (parse_ByteArray(data[index..index+SizeOfV(VByteArray(vs[0]))]).0 == Some(VByteArray(vs[0])));
            lemma_parse_KeyArray_contents_first(data[index..bound], len, vs);
            assert narrow_val_tuple.0.value == VByteArray(vs[0])
                == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(narrow_val_tuple.0.value);
            calc {
                SizeOfV(narrow_val_tuple.0.value) + SeqSumLens(vs[1..]);
                    { reveal_SeqSumLens(); }
                SeqSumLens(vs);
            }
            assert new_index+SeqSumLens(vs[1..]) <= bound;

            lemma_parse_Val_view_KeyArray_contents(data, vs[1..], new_index, bound, len - 1);

            // TODO I'm not sure why but this next part is really really slow.

            assert (parse_KeyArray_contents(data[new_index..bound], len - 1).0 == Some(vs[1..])) <==> (parse_KeyArray_contents(data[new_index..new_index+SeqSumLens(vs[1..])], len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSumLens(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert narrow_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else {
            // Doesn't matter for our ensures clause
        }
    }
}

lemma lemma_parse_Val_view_KeyArray(data:seq<byte>, v:V, grammar: G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GKeyArray?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    ensures  (parse_KeyArray(data[index..bound]).0 == Some(v)) <==> (parse_KeyArray(data[index..index+SizeOfV(v)]).0 == Some(v));
    ensures  parse_KeyArray(data[index..bound]).0 == Some(v) ==> parse_KeyArray(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
{
    var narrow_tuple := parse_KeyArray(data[index..index+SizeOfV(v)]);
    var bound_tuple := parse_KeyArray(data[index..bound]);
    var narrow_len_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
    var bound_len_tuple := parse_Uint64(data[index..bound]);
    var narrow_contents_tuple := parse_KeyArray_contents(narrow_len_tuple.1, narrow_len_tuple.0.value.u);
    var bound_contents_tuple := parse_KeyArray_contents(bound_len_tuple.1, bound_len_tuple.0.value.u);

    assert narrow_len_tuple.0 == bound_len_tuple.0;

    if bound_tuple.0 == Some(v) {
        assert parse_KeyArray_contents(bound_len_tuple.1, bound_len_tuple.0.value.u).0 == Some(v.baa);   // OBSERVE
        lemma_parse_KeyArray_contents_len(bound_len_tuple.1, narrow_len_tuple.0.value.u);
        lemma_parse_Val_view_KeyArray_contents(data, v.baa, index+8, bound, narrow_len_tuple.0.value.u);
    }

    if narrow_tuple.0 == Some(v) {
        assert parse_KeyArray_contents(narrow_len_tuple.1, narrow_len_tuple.0.value.u).0 == Some(v.baa);   // OBSERVE
        lemma_parse_KeyArray_contents_len(narrow_len_tuple.1, narrow_len_tuple.0.value.u);
        lemma_parse_Val_view_KeyArray_contents(data, v.baa, index+8, bound, narrow_len_tuple.0.value.u);
    }
}

lemma lemma_parse_Val_view_Tuple_contents(data:seq<byte>, vs:seq<V>, grammar:seq<G>, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |vs| == |grammar|;
    requires forall i :: 0 <= i < |vs| ==> ValInGrammar(vs[i], grammar[i]);
    requires |grammar| < 0x1_0000_0000_0000_0000;
    requires forall g :: g in grammar ==> ValidGrammar(g);
    requires 0 <= index <= |data|;
    requires 0 <= index + SeqSum(vs) <= |data|;
    requires index+SeqSum(vs) <= bound <= |data|;
    decreases grammar, -1, vs;
    ensures  (parse_Tuple_contents(data[index..bound], grammar).0 == Some(vs)) <==> (parse_Tuple_contents(data[index..index+SeqSum(vs)], grammar).0 == Some(vs));
    ensures  parse_Tuple_contents(data[index..bound], grammar).0 == Some(vs) ==> parse_Tuple_contents(data[index..bound], grammar).1 == data[index+SeqSum(vs)..bound];
{
    reveal_parse_Tuple_contents();
    if grammar == [] {
        reveal_SeqSum();
    } else {
        var narrow_tuple := parse_Tuple_contents(data[index..index+SeqSum(vs)], grammar);
        var bound_tuple := parse_Tuple_contents(data[index..bound], grammar);
        var narrow_val_tuple := parse_Val(data[index..index+SeqSum(vs)], grammar[0]);
        var bound_val_tuple := parse_Val(data[index..bound], grammar[0]);
        var narrow_contents_tuple := parse_Tuple_contents(narrow_val_tuple.1, grammar[1..]);
        var bound_contents_tuple := parse_Tuple_contents(bound_val_tuple.1, grammar[1..]);


        if narrow_tuple.0 == Some(vs) {
            assert !narrow_val_tuple.0.None? && !narrow_contents_tuple.0.None?;
            calc {
                index + SeqSum(vs) <= |data|;
                SeqSum(vs) <= |data| - index;
                SeqSum(vs) < |data| - index + 1;
            }
            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar[0], index);
            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            lemma_SeqSum_bound(vs, bound - index + 1);
            assert index+SizeOfV(vs[0]) <= bound <= |data|;     // OBSERVE (trigger on forall?)
            assert (parse_Val(data[index..bound], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            assert narrow_val_tuple.0.value == vs[0] == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(narrow_val_tuple.0.value);
            calc {
                SizeOfV(narrow_val_tuple.0.value) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Tuple_contents(data, vs[1..], grammar[1..], new_index, bound);

            assert (parse_Tuple_contents(data[new_index..bound], grammar[1..]).0 == Some(vs[1..])) <==> (parse_Tuple_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar[1..]).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert bound_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else if bound_tuple.0 == Some(vs) {
            assert !bound_val_tuple.0.None? && !bound_contents_tuple.0.None?;

            lemma_SeqSum_bound(vs, |data| - index + 1);
            lemma_parse_Val_view(data, vs[0], grammar[0], index);
            // This is exactly the ensures of the lemma above
            assert forall bound' :: index+SizeOfV(vs[0]) <= bound' <= |data| ==>
                   ((parse_Val(data[index..bound'], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0])));

            lemma_SeqSum_bound(vs, bound - index + 1);
            lemma_SeqSum_bound(vs, SeqSum(vs) + 1);
            assert index+SizeOfV(vs[0]) <= index+SeqSum(vs) <= |data|;
            assert (parse_Val(data[index..index+SeqSum(vs)], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            assert (parse_Val(data[index..bound], grammar[0]).0 == Some(vs[0])) <==> (parse_Val(data[index..index+SizeOfV(vs[0])], grammar[0]).0 == Some(vs[0]));
            assert narrow_val_tuple.0.value == vs[0] == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(narrow_val_tuple.0.value);
            calc {
                SizeOfV(narrow_val_tuple.0.value) + SeqSum(vs[1..]);
                    { reveal_SeqSum(); }
                SeqSum(vs);
            }
            assert new_index+SeqSum(vs[1..]) <= bound;

            lemma_parse_Val_view_Tuple_contents(data, vs[1..], grammar[1..], new_index, bound);

            assert (parse_Tuple_contents(data[new_index..bound], grammar[1..]).0 == Some(vs[1..])) <==> (parse_Tuple_contents(data[new_index..new_index+SeqSum(vs[1..])], grammar[1..]).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSum(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert narrow_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else {
            // Doesn't matter for our ensures clause
        }
    }

}

lemma lemma_parse_Val_view_Tuple(data:seq<byte>, v:V, grammar:seq<G>, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires v.VTuple?;
    requires |v.t| == |grammar|
    requires forall i :: 0 <= i < |v.t| ==> ValInGrammar(v.t[i], grammar[i]);
    requires |grammar| < 0x1_0000_0000_0000_0000;
    requires forall g :: g in grammar ==> ValidGrammar(g);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    decreases grammar, -1, v;
    ensures  (parse_Tuple(data[index..bound], grammar).0 == Some(v)) <==> (parse_Tuple(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
    ensures  parse_Tuple(data[index..bound], grammar).0 == Some(v) ==> parse_Tuple(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    var bound_tuple := parse_Tuple(data[index..bound], grammar);
    var bound_contents := bound_tuple.0;
    var bound_rest := bound_tuple.1;
    var narrow_tuple := parse_Tuple(data[index..index+SizeOfV(v)], grammar);
    var narrow_contents := narrow_tuple.0;
    var narrow_rest := narrow_tuple.1;

    if parse_Tuple(data[index..bound], grammar).0 == Some(v) {
        assert !bound_contents.None?;
        lemma_parse_Val_view_Tuple_contents(data, v.t, grammar, index, bound);
        assert (parse_Tuple_contents(data[index..bound], grammar).0 == Some(v.t)) <==> (parse_Tuple_contents(data[index..index+SeqSum(v.t)], grammar).0 == Some(v.t)); // OBSERVE
    } else if parse_Tuple(data[index..index+SizeOfV(v)], grammar).0 == Some(v) {
        assert !narrow_contents.None?;
        lemma_parse_Val_view_Tuple_contents(data, v.t, grammar, index, bound);
        assert (parse_Tuple_contents(data[index..bound], grammar).0 == Some(v.t)) <==> (parse_Tuple_contents(data[index..index+SeqSum(v.t)], grammar).0 == Some(v.t)); // OBSERVE
    } else {
        // Don't care
    }
}

lemma lemma_parse_Val_view_Union(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GTaggedUnion?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    decreases grammar, -1;
    ensures  (parse_Case(data[index..bound], grammar.cases).0 == Some(v)) <==> (parse_Case(data[index..index+SizeOfV(v)], grammar.cases).0 == Some(v));
    ensures  parse_Case(data[index..bound], grammar.cases).0 == Some(v) ==> parse_Case(data[index..bound], grammar.cases).1 == data[index+SizeOfV(v)..bound];
{
    var narrow_tuple := parse_Case(data[index..index+SizeOfV(v)], grammar.cases);
    var bound_tuple := parse_Case(data[index..bound], grammar.cases);
    var narrow_caseID_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
    var bound_caseID_tuple := parse_Uint64(data[index..bound]);
    assert narrow_caseID_tuple.0.value == bound_caseID_tuple.0.value;

    if parse_Case(data[index..bound], grammar.cases).0 == Some(v) {
        var narrow_val_tuple := parse_Val(narrow_caseID_tuple.1, grammar.cases[narrow_caseID_tuple.0.value.u]);
        var bound_val_tuple := parse_Val(bound_caseID_tuple.1, grammar.cases[bound_caseID_tuple.0.value.u]);

        lemma_parse_Val_view(data, v.val, grammar.cases[narrow_caseID_tuple.0.value.u], index + 8);
        assert index+SizeOfV(v.val) <= bound <= |data|;
        assert (parse_Val(data[index+8..bound], grammar.cases[narrow_caseID_tuple.0.value.u]).0 == Some(v.val)) <==> (parse_Val(data[index+8..index+8+SizeOfV(v.val)], grammar.cases[narrow_caseID_tuple.0.value.u]).0 == Some(v.val));
    } else if parse_Case(data[index..index+SizeOfV(v)], grammar.cases).0 == Some(v) {
        var narrow_val_tuple := parse_Val(narrow_caseID_tuple.1, grammar.cases[narrow_caseID_tuple.0.value.u]);
        var bound_val_tuple := parse_Val(bound_caseID_tuple.1, grammar.cases[bound_caseID_tuple.0.value.u]);

        lemma_parse_Val_view(data, v.val, grammar.cases[narrow_caseID_tuple.0.value.u], index + 8);
        assert (parse_Val(data[index+8..bound], grammar.cases[narrow_caseID_tuple.0.value.u]).0 == Some(v.val)) <==> (parse_Val(data[index+8..index+8+SizeOfV(v.val)], grammar.cases[narrow_caseID_tuple.0.value.u]).0 == Some(v.val));
    } else {
        // Doesn't matter
    }
}

lemma lemma_parse_Val_view(data:seq<byte>, v:V, grammar:G, index:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    decreases grammar, 0;
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v)));
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             (parse_Val(data[index..bound], grammar).0 == Some(v)) ==> parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    forall bound | index+SizeOfV(v) <= bound <= |data|
         ensures (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
         ensures (parse_Val(data[index..bound], grammar).0 == Some(v)) ==> parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
    {
        reveal_parse_Val();
        match grammar
            case GUint64             => assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GArray(elt)         => lemma_parse_Val_view_Array(data, v, grammar, index, bound);
                                        assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GKeyArray     => lemma_parse_Val_view_KeyArray(data, v, grammar, index, bound);
                                        assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GMessage         => lemma_parse_Val_view_Message(data, v, grammar, index);
                                        assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GMessageArray     => lemma_parse_Val_view_MessageArray(data, v, grammar, index, bound);
                                        assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GTuple(t)           => lemma_parse_Val_view_Tuple(data, v, t, index, bound); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GByteArray          => lemma_parse_Val_view_ByteArray(data, v, grammar, index); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GUint64Array          => lemma_parse_Val_view_Uint64Array(data, v, grammar, index); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GTaggedUnion(cases) => lemma_parse_Val_view_Union(data, v, grammar, index, bound); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));

    }
}


lemma lemma_parse_Val_view_specific(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|; 
    requires parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v)
    decreases grammar, 0;
    ensures  parse_Val(data[index..bound], grammar).0 == Some(v);
    ensures  parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    lemma_parse_Val_view(data, v, grammar, index);
}

lemma lemma_parse_Val_view_specific_size(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|; 
    requires parse_Val(data[index..bound], grammar).0 == Some(v)
    decreases grammar, 0;
    ensures  parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v);
    ensures  parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
{
    lemma_parse_Val_view(data, v, grammar, index);
}

method ComputeSeqSum(s:seq<V>) returns (size:uint64)
    requires |s| < 0x1_0000_0000_0000_0000;
    requires 0 <= SeqSum(s) < 0x1_0000_0000_0000_0000;
    requires forall v :: v in s ==> ValidVal(v);
    ensures (size as int) == SeqSum(s);
{
    reveal_SeqSum();
    if (|s| as uint64) == 0 {
        size := 0;
    } else {
        var v_size := ComputeSizeOf(s[(0 as uint64)]);
        var rest_size := ComputeSeqSum(s[(1 as uint64)..]);
        size := v_size + rest_size;
    }
}

method ComputeSeqSumLens(s:seq<Key>) returns (size:uint64)
    requires |s| < 0x1_0000_0000_0000_0000;
    requires 0 <= SeqSumLens(s) < 0x1_0000_0000_0000_0000;
    ensures (size as int) == SeqSumLens(s);
{
    reveal_SeqSumLens();
    if (|s| as uint64) == 0 {
        size := 0;
    } else {
        var v_size := Uint64Size() + |s[0 as uint64]| as uint64;
        var rest_size := ComputeSeqSumLens(s[(1 as uint64)..]);
        size := v_size + rest_size;
    }
}

method ComputeSeqSumMessageLens(s:seq<Message>) returns (size:uint64)
    requires |s| < 0x1_0000_0000_0000_0000;
    requires 0 <= SeqSumMessageLens(s) < 0x1_0000_0000_0000_0000;
    ensures (size as int) == SeqSumMessageLens(s);
{
    reveal_SeqSumMessageLens();
    if (|s| as uint64) == 0 {
        size := 0;
    } else {
        var v_size := MessageSizeUint64(s[0 as uint64]);
        var rest_size := ComputeSeqSumMessageLens(s[(1 as uint64)..]);
        size := v_size + rest_size;
    }
}

method ComputeSizeOf(val:V) returns (size:uint64)
    requires 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000;
    requires ValidVal(val);
    ensures (size as int) == SizeOfV(val);
{
    match val
        case VUint64(_)     => size := 8;
        case VArray(a)      => var v := ComputeSeqSum(a);
                               if v == 0 {
                                   size := 8;
                               } else {
                                   size := 8 + v;
                               }
        case VTuple(t)      => size := ComputeSeqSum(t);
        case VByteArray(b)  => size := 8 + (|b| as uint64);
        case VMessage(m)    => size := MessageSizeUint64(m);
        case VUint64Array(b)  => size := 8 + 8*(|b| as uint64);
        case VKeyArray(b)  => {
          var v := ComputeSeqSumLens(b);
          size := 8 + v;
        }
        case VMessageArray(b)  => {
          var v := ComputeSeqSumMessageLens(b);
          size := 8 + v;
        }
        case VCase(c, v)    => var vs := ComputeSizeOf(v);
                               size := 8 + vs;
}

lemma seq_ext(a: seq<byte>, b: seq<byte>)
requires |a| == |b|
requires forall i | 0 <= i < |a| :: a[i] == b[i]
ensures a == b
{
}

lemma MarshallUint64_index_splicing(data: array<byte>, index: uint64, val: V, i: int)
requires 0 <= i
requires 0 <= index
requires 8 + (i+1)*8 <= SizeOfV(val)
requires (index as int) + SizeOfV(val) <= data.Length
ensures data[index..(index as int) + SizeOfV(val)][8 + i*8 .. 8 + (i+1)*8]
     == data[index as int + 8 + i*8 .. index as int + 8 + (i+1)*8];
{
  // I had to go through enormous trouble to prove this for some reason

  var ar := data[..];
  var a := index as int;
  var b := SizeOfV(val);
  var c := 8 + i*8;
  var d := 8;

  var x1 := ar[a .. a + b][c .. c + d];
  var x2 := ar[a + c .. a + c + d];
  forall i | 0 <= i < |x1|
  ensures x1[i] == x2[i]
  {
    assert x1[i]
        == ar[a .. a + b][c .. c + d][i]
        == ar[a .. a + b][c + i]
        == ar[a + c + i]
        == ar[a + c .. a + c + d][i]
        == x2[i];
  }
  assert |x1| == |x2|;
  seq_ext(x1, x2);

  assert ar[a .. a + b][c .. c + d]
      == ar[a + c .. a + c + d];
  assert ar[index..(index as int) + SizeOfV(val)][8 + i*8 .. 8 + (i+1)*8]
     == ar[index as int + 8 + i*8 .. index as int + 8 + (i+1)*8];
}

method MarshallUint64(n:uint64, data:array<byte>, index:uint64)
    requires (index as int) + (Uint64Size() as int) <= data.Length;
    requires 0 <= (index as int) + (Uint64Size() as int) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  SeqByteToUint64(data[index..index+(Uint64Size() as uint64)]) == n;
    ensures  !parse_Uint64(data[index .. index+(Uint64Size() as uint64)]).0.None?;
    ensures  !parse_Uint64(data[index .. ]).0.None?;
    ensures  var tuple := parse_Uint64(data[index .. index+(Uint64Size() as uint64)]);
             tuple.0.value.u == n && tuple.1 == [];
    ensures  var tuple := parse_Uint64(data[index .. ]);
             tuple.0.value.u == n && tuple.1 == data[index+(Uint64Size() as uint64)..];
    ensures  data[0..index] == old(data[0..index]);
    ensures  data[index+(Uint64Size() as uint64)..] == old(data[index+(Uint64Size() as uint64)..]);
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + (Uint64Size() as int) <= i < data.Length ==> data[i] == old(data[i]);
{
    MarshallUint64_guts(n, data, index);

    forall i | 0 <= i < index ensures data[i] == old(data[i])
    {
      assert data[i] == data[..index][i] == old(data[..index])[i] == old(data[i]);
    }

    assert |data[index .. index+(Uint64Size() as uint64)]| == 8;
}

lemma lemma_marshall_array_contents(contents:seq<V>, eltType:G, marshalled_bytes:seq<byte>, trace:seq<seq<byte>>)
    requires forall v :: v in contents ==> ValInGrammar(v, eltType);
    requires forall v :: v in contents ==> ValidVal(v);
    requires ValidGrammar(eltType);
    requires |marshalled_bytes| < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    requires |contents| == |trace|;
    requires |marshalled_bytes| == SeqSum(contents);
    requires marshalled_bytes == SeqCatRev(trace);
    requires forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
    requires forall j :: 0 <= j < |trace| ==> var (val, rest) := parse_Val(trace[j], eltType); val.Some? && val.value == contents[j]; 

    ensures  parse_Array_contents(marshalled_bytes, eltType, (|contents| as uint64)).0.Some?;
    ensures  parse_Array_contents(marshalled_bytes, eltType, (|contents| as uint64)).0.value == contents;
{
    if |contents| == 0 {
        reveal_parse_Array_contents();
    } else {
        var val_tuple := parse_Val(marshalled_bytes, eltType);
        var val, rest1 := val_tuple.0, val_tuple.1;
        var rest_tuple := parse_Array_contents(rest1, eltType, (|contents| as uint64)-1);
        var others, rest2 := rest_tuple.0, rest_tuple.1;
        var target := parse_Array_contents(marshalled_bytes, eltType, (|contents| as uint64)).0;
        calc {
            target;
                { reveal_parse_Array_contents(); }
            if !val.None? && !others.None? then Some([val.value] + others.value) else None;
        }

        calc {
            SeqCatRev(trace);
                { lemma_SeqCat_equivalent(trace); }
            SeqCat(trace);
        }

        assert marshalled_bytes[0..SizeOfV(contents[0])] == trace[0];
        assert parse_Val(trace[0], eltType).0.Some?;
        assert parse_Val(trace[0], eltType).0.value == contents[0];
        lemma_parse_Val_view_specific(marshalled_bytes, contents[0], eltType, 0, |marshalled_bytes|);
        assert parse_Val(marshalled_bytes[0..|marshalled_bytes|], eltType).0 == Some(contents[0]);
        assert marshalled_bytes[0..|marshalled_bytes|] == marshalled_bytes;     // OBSERVE
        assert val.Some? && val.value == contents[0];
        assert rest1 == marshalled_bytes[SizeOfV(contents[0])..];

        // Prove a requires for the recursive call
        calc {
            marshalled_bytes[SizeOfV(contents[0])..];
                calc {
                    marshalled_bytes;
                    SeqCatRev(trace);
                        { lemma_SeqCat_equivalent(trace); }
                    SeqCat(trace);
                    trace[0] + SeqCat(trace[1..]);
                        { lemma_SeqCat_equivalent(trace[1..]); }
                    trace[0] + SeqCatRev(trace[1..]);
                }
            (trace[0] + SeqCatRev(trace[1..]))[SizeOfV(contents[0])..];
                { assert |trace[0]| == SizeOfV(contents[0]); }
            SeqCatRev(trace[1..]);
        }

        // Prove a requires for the recursive call
        calc {
            SeqSum(contents);
                { reveal_SeqSum(); }
            SizeOfV(contents[0]) + SeqSum(contents[1..]);
        }
        lemma_marshall_array_contents(contents[1..], eltType, marshalled_bytes[SizeOfV(contents[0])..], trace[1..]);
        assert others.Some?;
        assert others.value == contents[1..];
        assert contents == [contents[0]] + contents[1..];
       
    }
}

method{:timeLimitMultiplier 4} MarshallArrayContents(contents:seq<V>, ghost eltType:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires forall v :: v in contents ==> ValInGrammar(v, eltType);
    requires forall v :: v in contents ==> ValidVal(v);
    requires ValidGrammar(eltType);
    requires (index as int) + SeqSum(contents) <= data.Length;
    requires 0 <= (index as int) + SeqSum(contents) < 0x1_0000_0000_0000_0000;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    decreases eltType, 1, |contents|;
    modifies data;
    ensures  parse_Array_contents(data[index..(index as int) + SeqSum(contents)], eltType, (|contents| as uint64)).0.Some?;
    ensures  parse_Array_contents(data[index..(index as int) + SeqSum(contents)], eltType, (|contents| as uint64)).0.value == contents;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SeqSum(contents) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SeqSum(contents);
{
    var i:uint64 := 0;
    var cur_index := index;
    reveal_SeqSum();
    reveal_parse_Array_contents();

    ghost var trace := [];
    ghost var marshalled_bytes := [];

    while i < (|contents| as uint64)
        invariant 0 <= (i as int) <= |contents|;
        invariant 0 <= (index as int) <= (index as int) + SeqSum(contents[..i]) <= data.Length;
        invariant (cur_index as int) == (index as int) + SeqSum(contents[..i]);
        invariant forall j :: 0 <= j < index ==> data[j] == old(data[j]);
        invariant forall j :: (index as int) + SeqSum(contents) <= j < data.Length ==> data[j] == old(data[j]);
        invariant marshalled_bytes == data[index..cur_index];
        invariant marshalled_bytes == SeqCatRev(trace);
        invariant |trace| == (i as int);
        invariant forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
        invariant forall j :: 0 <= j < |trace| ==> 
                        var (val, rest) := parse_Val(trace[j], eltType); 
                        val.Some? && val.value == contents[j]; 
    {
        lemma_SeqSum_bound(contents, 0x1_0000_0000_0000_0000);

        // Prove we meet MarshallVal's length requirement
        calc <= {
            (cur_index as int) + SizeOfV(contents[i]);
            (index as int) + SeqSum(contents[..i]) + SizeOfV(contents[i]);
                { lemma_SeqSum_prefix(contents[..i], contents[i]); 
                  assert contents[..i] + [contents[i]] == contents[..i+1]; }
            (index as int) + SeqSum(contents[..i+1]);
                { lemma_SeqSum_bound_prefix(contents, contents[..i+1], (i as int)+1); }
                //{ lemma_SeqSum_bound(contents, data.Length - (index as int) + 1); }
            (index as int) + SeqSum(contents);
            //data.Length;
        }
        var item_size := MarshallVal(contents[i], eltType, data, cur_index);
        //var item_size := ComputeSizeOf(contents[uint64(i)]);

        ghost var fresh_bytes := data[cur_index..cur_index + item_size];
        marshalled_bytes := marshalled_bytes + fresh_bytes;
        forall () 
            ensures var (val, rest) := parse_Val(fresh_bytes, eltType);
                    val.Some? && val.value == contents[i];
        {
            assert SizeOfV(contents[i]) <= |fresh_bytes|;  // OBSERVE
            lemma_parse_Val_view(fresh_bytes, contents[i], eltType, 0);
        }

        ghost var old_trace := trace;
        trace := trace + [fresh_bytes];

        ghost var old_cur_index := cur_index;
        cur_index := cur_index + item_size;
        i := i + 1;

        // Prove the invariant that we stay within bounds
        calc <= {
            (index as int) + SeqSum(contents[..i]);
            calc {
                SeqSum(contents[..i]);
                <=  { lemma_SeqSum_bound_prefix(contents, contents[..i], (i as int)); }
                SeqSum(contents);
            }
            (index as int) + SeqSum(contents);
            data.Length;
        }
        //assert {:split_here} true;
        assert marshalled_bytes == data[index..cur_index];

        // Prove the invariant about our index tracking correctly
        calc {
            (cur_index as int);
            (old_cur_index as int) + SizeOfV(contents[i-1]);
            (index as int) + SeqSum(contents[..i-1]) + SizeOfV(contents[i-1]);
                { lemma_SeqSum_prefix(contents[..i-1], contents[i-1]); 
                  assert contents[..i-1] + [contents[i-1]] == contents[..i]; }
            (index as int) + SeqSum(contents[..i]);
        }
        assert (cur_index as int) == (index as int) + SeqSum(contents[..i]);
        assert marshalled_bytes == data[index..cur_index];
    }

    // Prove that parsing will produce the correct result

    // After the while loop, we know:
    assert contents[..i] == contents;   // OBSERVE
    assert (cur_index as int) == (index as int) + SeqSum(contents);
    assert marshalled_bytes == data[index..(index as int)+SeqSum(contents)];
    //assert marshalled_bytes == SeqCatRev(trace);
    //assert |trace| == |contents|;
    lemma_marshall_array_contents(contents, eltType, marshalled_bytes, trace);
    size := cur_index - index;
}

method MarshallArray(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VArray?;
    requires ValInGrammar(val, grammar);
    requires ValidGrammar(grammar);
    requires ValidVal(val);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    //assert{:split_here} true;
    reveal_parse_Val();
    MarshallUint64((|val.a| as uint64), data, index);

    ghost var tuple := parse_Uint64(data[index..(index as int) + SizeOfV(val)]);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert !len.None?;
    var contents_size := MarshallArrayContents(val.a, grammar.elt, data, index + Uint64Size());
    tuple := parse_Uint64(data[index..(index as int) + SizeOfV(val)]);
    //assert {:split_here} true;
    len := tuple.0;
    rest := tuple.1;
    assert !len.None?;
    ghost var contents_tuple := parse_Array_contents(rest, grammar.elt, len.value.u);
    ghost var contents  := contents_tuple.0;
    ghost var remainder := contents_tuple.1;
    assert !contents.None?;
    size := 8 + contents_size;
}

lemma lemma_marshall_keyarray_contents(contents:seq<Key>, marshalled_bytes:seq<byte>, trace:seq<seq<byte>>)
    requires forall v :: v in contents ==> |v| < 0x1_0000_0000_0000_0000
    requires |marshalled_bytes| < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    requires |contents| == |trace|;
    requires |marshalled_bytes| == SeqSumLens(contents);
    requires marshalled_bytes == SeqCatRev(trace);
    requires forall j :: 0 <= j < |trace| ==> 8 + |contents[j]| == |trace[j]| < 0x1_0000_0000_0000_0000;
    requires forall j :: 0 <= j < |trace| ==> var (val, rest) := parse_ByteArray(trace[j]); val.Some? && val.value.b == contents[j]; 

    ensures  parse_KeyArray_contents(marshalled_bytes, (|contents| as uint64)).0.Some?;
    ensures  parse_KeyArray_contents(marshalled_bytes, (|contents| as uint64)).0.value == contents;
{
    if |contents| == 0 {
        reveal_parse_KeyArray_contents();
    } else {
        var val_tuple := parse_ByteArray(marshalled_bytes);
        var val, rest1 := val_tuple.0, val_tuple.1;
        var rest_tuple := parse_KeyArray_contents(rest1, (|contents| as uint64)-1);
        var others, rest2 := rest_tuple.0, rest_tuple.1;
        var target := parse_KeyArray_contents(marshalled_bytes, (|contents| as uint64)).0;
        calc {
            target;
                { reveal_parse_KeyArray_contents(); }
            if !val.None? && !others.None? && |val.value.b| as uint64 <= KeyType.MaxLen() then Some([val.value.b] + others.value) else None;
        }

        calc {
            SeqCatRev(trace);
                { lemma_SeqCat_equivalent(trace); }
            SeqCat(trace);
        }

        assert marshalled_bytes[0..SizeOfV(VByteArray(contents[0]))] == trace[0];
        assert parse_ByteArray(trace[0]).0.Some?;
        assert parse_ByteArray(trace[0]).0.value.b == contents[0];
        //assert parse_Val(trace[0], GByteArray).0 == Some(VByteArray(contents[0]));
        //assert parse_Val(marshalled_bytes[..SizeOfV(VByteArray(contents[0]))], GByteArray).0 == Some(VByteArray(contents[0]));
        reveal_parse_Val();
        lemma_parse_Val_view_specific(marshalled_bytes, VByteArray(contents[0]), GByteArray, 0, |marshalled_bytes|);
        assert parse_ByteArray(marshalled_bytes[0..|marshalled_bytes|]).0.value.b == Some(contents[0]).value;
        assert marshalled_bytes[0..|marshalled_bytes|] == marshalled_bytes;     // OBSERVE
        assert val.Some? && val.value.b == contents[0];
        assert rest1 == marshalled_bytes[SizeOfV(VByteArray(contents[0]))..];

        // Prove a requires for the recursive call
        calc {
            marshalled_bytes[SizeOfV(VByteArray(contents[0]))..];
                calc {
                    marshalled_bytes;
                    SeqCatRev(trace);
                        { lemma_SeqCat_equivalent(trace); }
                    SeqCat(trace);
                    trace[0] + SeqCat(trace[1..]);
                        { lemma_SeqCat_equivalent(trace[1..]); }
                    trace[0] + SeqCatRev(trace[1..]);
                }
            (trace[0] + SeqCatRev(trace[1..]))[SizeOfV(VByteArray(contents[0]))..];
                { assert |trace[0]| == SizeOfV(VByteArray(contents[0])); }
            SeqCatRev(trace[1..]);
        }

        // Prove a requires for the recursive call
        calc {
            SeqSumLens(contents);
                { reveal_SeqSumLens(); }
            8 + |contents[0]| + SeqSumLens(contents[1..]);
        }
        lemma_marshall_keyarray_contents(contents[1..], marshalled_bytes[SizeOfV(VByteArray(contents[0]))..], trace[1..]);
        assert others.Some?;
        assert others.value == contents[1..];
        assert contents == [contents[0]] + contents[1..];
       
    }
}

method{:timeLimitMultiplier 4} MarshallKeyArrayContents(contents:seq<Key>, data:array<byte>, index:uint64) returns (size:uint64)
    requires (index as int) + SeqSumLens(contents) <= data.Length;
    requires 0 <= (index as int) + SeqSumLens(contents) < 0x1_0000_0000_0000_0000;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    decreases |contents|;
    modifies data;
    ensures  parse_KeyArray_contents(data[index..(index as int) + SeqSumLens(contents)], (|contents| as uint64)).0.Some?;
    ensures  parse_KeyArray_contents(data[index..(index as int) + SeqSumLens(contents)], (|contents| as uint64)).0.value == contents;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SeqSumLens(contents) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SeqSumLens(contents);
{
    var i:uint64 := 0;
    var cur_index := index;
    reveal_SeqSumLens();
    reveal_parse_KeyArray_contents();

    ghost var trace := [];
    ghost var marshalled_bytes := [];

    while i < (|contents| as uint64)
        invariant 0 <= (i as int) <= |contents|;
        invariant 0 <= (index as int) <= (index as int) + SeqSumLens(contents[..i]) <= data.Length;
        invariant (cur_index as int) == (index as int) + SeqSumLens(contents[..i]);
        invariant forall j :: 0 <= j < index ==> data[j] == old(data[j]);
        invariant forall j :: (index as int) + SeqSumLens(contents) <= j < data.Length ==> data[j] == old(data[j]);
        invariant marshalled_bytes == data[index..cur_index];
        invariant marshalled_bytes == SeqCatRev(trace);
        invariant |trace| == (i as int);
        invariant forall j :: 0 <= j < |trace| ==> SizeOfV(VByteArray(contents[j])) == |trace[j]| < 0x1_0000_0000_0000_0000;
        invariant forall j :: 0 <= j < |trace| ==> 
                        var (val, rest) := parse_ByteArray(trace[j]); 
                        val.Some? && val.value.b == contents[j]; 
    {
        lemma_SeqSumLens_bound(contents, 0x1_0000_0000_0000_0000);

        // Prove we meet MarshallVal's length requirement
        calc <= {
            (cur_index as int) + SizeOfV(VByteArray(contents[i]));
            (index as int) + SeqSumLens(contents[..i]) + SizeOfV(VByteArray(contents[i]));
                { lemma_SeqSumLens_prefix(contents[..i], contents[i]); 
                  assert contents[..i] + [contents[i]] == contents[..i+1]; }
            (index as int) + SeqSumLens(contents[..i+1]);
                { lemma_SeqSumLens_bound_prefix(contents, contents[..i+1], (i as int)+1); }
                //{ lemma_SeqSum_bound(contents, data.Length - (index as int) + 1); }
            (index as int) + SeqSumLens(contents);
            //data.Length;
        }
        var item_size := MarshallByteArrayInterior(contents[i], data, cur_index);
        //var item_size := ComputeSizeOf(contents[uint64(i)]);

        ghost var fresh_bytes := data[cur_index..cur_index + item_size];
        marshalled_bytes := marshalled_bytes + fresh_bytes;
        forall () 
            ensures var (val, rest) := parse_ByteArray(fresh_bytes);
                    val.Some? && val.value.b == contents[i];
        {
            assert SizeOfV(VByteArray(contents[i])) <= |fresh_bytes|;  // OBSERVE
            reveal_parse_Val();
            lemma_parse_Val_view(fresh_bytes, VByteArray(contents[i]), GByteArray, 0);
        }

        ghost var old_trace := trace;
        trace := trace + [fresh_bytes];

        ghost var old_cur_index := cur_index;
        cur_index := cur_index + item_size;
        i := i + 1;

        // Prove the invariant that we stay within bounds
        calc <= {
            (index as int) + SeqSumLens(contents[..i]);
            calc {
                SeqSumLens(contents[..i]);
                <=  { lemma_SeqSumLens_bound_prefix(contents, contents[..i], (i as int)); }
                SeqSumLens(contents);
            }
            (index as int) + SeqSumLens(contents);
            data.Length;
        }
        //assert {:split_here} true;
        assert marshalled_bytes == data[index..cur_index];

        // Prove the invariant about our index tracking correctly
        calc {
            (cur_index as int);
            (old_cur_index as int) + SizeOfV(VByteArray(contents[i-1]));
            (index as int) + SeqSumLens(contents[..i-1]) + SizeOfV(VByteArray(contents[i-1]));
                { lemma_SeqSumLens_prefix(contents[..i-1], contents[i-1]); 
                  assert contents[..i-1] + [contents[i-1]] == contents[..i]; }
            (index as int) + SeqSumLens(contents[..i]);
        }
        assert (cur_index as int) == (index as int) + SeqSumLens(contents[..i]);
        assert marshalled_bytes == data[index..cur_index];
    }

    // Prove that parsing will produce the correct result

    // After the while loop, we know:
    assert contents[..i] == contents;   // OBSERVE
    assert (cur_index as int) == (index as int) + SeqSumLens(contents);
    assert marshalled_bytes == data[index..(index as int)+SeqSumLens(contents)];
    //assert marshalled_bytes == SeqCatRev(trace);
    //assert |trace| == |contents|;
    lemma_marshall_keyarray_contents(contents, marshalled_bytes, trace);
    size := cur_index - index;
}

method MarshallKeyArray(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VKeyArray?;
    requires ValInGrammar(val, grammar);
    requires ValidGrammar(grammar);
    requires ValidVal(val);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    //assert{:split_here} true;
    reveal_parse_Val();
    MarshallUint64((|val.baa| as uint64), data, index);

    ghost var tuple := parse_Uint64(data[index..(index as int) + SizeOfV(val)]);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert !len.None?;
    var contents_size := MarshallKeyArrayContents(val.baa, data, index + Uint64Size());
    tuple := parse_Uint64(data[index..(index as int) + SizeOfV(val)]);
    assert {:split_here} true;
    len := tuple.0;
    rest := tuple.1;
    assert !len.None?;
    ghost var contents_tuple := parse_KeyArray_contents(rest, len.value.u);
    ghost var contents  := contents_tuple.0;
    ghost var remainder := contents_tuple.1;
    assert !contents.None?;
    size := 8 + contents_size;
}

lemma lemma_marshall_tuple_contents(contents:seq<V>, eltTypes:seq<G>, marshalled_bytes:seq<byte>, trace:seq<seq<byte>>)
    requires |contents| == |eltTypes|;
    requires forall i :: 0 <= i < |contents| ==> ValInGrammar(contents[i], eltTypes[i]);
    requires forall g :: g in eltTypes ==> ValidGrammar(g);
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall i :: 0 <= i < |contents| ==> ValidVal(contents[i]);
    requires |marshalled_bytes| < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    requires |contents| == |trace|;
    requires |marshalled_bytes| == SeqSum(contents);
    requires marshalled_bytes == SeqCatRev(trace);
    requires forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
    requires forall j :: 0 <= j < |trace| ==> var (val, rest) := parse_Val(trace[j], eltTypes[j]); val.Some? && val.value == contents[j]; 

    ensures  parse_Tuple_contents(marshalled_bytes, eltTypes).0.Some?;
    ensures  parse_Tuple_contents(marshalled_bytes, eltTypes).0.value == contents;
{
    if |contents| == 0 {
        reveal_parse_Tuple_contents();
    } else {
        var val_tuple := parse_Val(marshalled_bytes, eltTypes[0]);
        var val, rest1 := val_tuple.0, val_tuple.1;
        var rest_tuple := parse_Tuple_contents(rest1, eltTypes[1..]);
        var others, rest2 := rest_tuple.0, rest_tuple.1;
        var target := parse_Tuple_contents(marshalled_bytes, eltTypes).0;
        calc {
            target;
                { reveal_parse_Tuple_contents(); }
            if !val.None? && !others.None? then Some([val.value] + others.value) else None;
        }

        calc {
            SeqCatRev(trace);
                { lemma_SeqCat_equivalent(trace); }
            SeqCat(trace);
        }

        assert marshalled_bytes[0..SizeOfV(contents[0])] == trace[0];
        assert parse_Val(trace[0], eltTypes[0]).0.Some?;
        assert parse_Val(trace[0], eltTypes[0]).0.value == contents[0];
        lemma_parse_Val_view_specific(marshalled_bytes, contents[0], eltTypes[0], 0, |marshalled_bytes|);
        assert parse_Val(marshalled_bytes[0..|marshalled_bytes|], eltTypes[0]).0 == Some(contents[0]);
        assert marshalled_bytes[0..|marshalled_bytes|] == marshalled_bytes;     // OBSERVE
        assert val.Some? && val.value == contents[0];
        assert rest1 == marshalled_bytes[SizeOfV(contents[0])..];

        // Prove a requires for the recursive call
        calc {
            marshalled_bytes[SizeOfV(contents[0])..];
                calc {
                    marshalled_bytes;
                    SeqCatRev(trace);
                        { lemma_SeqCat_equivalent(trace); }
                    SeqCat(trace);
                    trace[0] + SeqCat(trace[1..]);
                        { lemma_SeqCat_equivalent(trace[1..]); }
                    trace[0] + SeqCatRev(trace[1..]);
                }
            (trace[0] + SeqCatRev(trace[1..]))[SizeOfV(contents[0])..];
                { assert |trace[0]| == SizeOfV(contents[0]); }
            SeqCatRev(trace[1..]);
        }

        // Prove a requires for the recursive call
        calc {
            SeqSum(contents);
                { reveal_SeqSum(); }
            SizeOfV(contents[0]) + SeqSum(contents[1..]);
        }
        lemma_marshall_tuple_contents(contents[1..], eltTypes[1..], marshalled_bytes[SizeOfV(contents[0])..], trace[1..]);
        assert others.Some?;
        assert others.value == contents[1..];
        assert contents == [contents[0]] + contents[1..];
       
    }
}

method{:timeLimitMultiplier 2} MarshallTupleContents(contents:seq<V>, ghost eltTypes:seq<G>, data:array<byte>, index:uint64) returns (size:uint64)
    requires |contents| == |eltTypes|;
    requires forall i :: 0 <= i < |contents| ==> ValInGrammar(contents[i], eltTypes[i]);
    requires forall g :: g in eltTypes ==> ValidGrammar(g);
    requires |eltTypes| < 0x1_0000_0000_0000_0000;
    requires forall i :: 0 <= i < |contents| ==> ValidVal(contents[i]);
    requires (index as int) + SeqSum(contents) <= data.Length;
    requires 0 <= (index as int) + SeqSum(contents) < 0x1_0000_0000_0000_0000;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    decreases eltTypes, 1, |contents|;
    modifies data;
    ensures  parse_Tuple_contents(data[index..(index as int) + SeqSum(contents)], eltTypes).0.Some?;
    ensures  parse_Tuple_contents(data[index..(index as int) + SeqSum(contents)], eltTypes).0.value == contents;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SeqSum(contents) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SeqSum(contents);
{
    var i:uint64 := 0;
    var cur_index := index;
    reveal_SeqSum();
    reveal_parse_Tuple_contents();

    ghost var trace := [];
    ghost var marshalled_bytes := [];

    while i < (|contents| as uint64)
        invariant 0 <= (i as int) <= |contents|;
        invariant 0 <= (index as int) <= (index as int) + SeqSum(contents[..i]) <= data.Length;
        invariant (cur_index as int) == (index as int) + SeqSum(contents[..i]);
        invariant forall j :: 0 <= j < index ==> data[j] == old(data[j]);
        invariant forall j :: (index as int) + SeqSum(contents) <= j < data.Length ==> data[j] == old(data[j]);
        invariant marshalled_bytes == data[index..cur_index];
        invariant marshalled_bytes == SeqCatRev(trace);
        invariant |trace| == (i as int);
        invariant forall j :: 0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
        invariant forall j :: 0 <= j < |trace| ==> 
                        var (val, rest) := parse_Val(trace[j], eltTypes[j]); 
                        val.Some? && val.value == contents[j]; 
    {
        lemma_SeqSum_bound(contents, 0x1_0000_0000_0000_0000);
        ghost var old_marshalled_bytes := marshalled_bytes;
        ghost var old_data := data[index..cur_index];
        assert old_marshalled_bytes == old_data;

        // Prove we meet MarshallVal's length requirement
        calc <= {
            (cur_index as int) + SizeOfV(contents[i]);
            (index as int) + SeqSum(contents[..i]) + SizeOfV(contents[i]);
                { lemma_SeqSum_prefix(contents[..i], contents[i]); 
                  assert contents[..i] + [contents[i]] == contents[..i+1]; }
            (index as int) + SeqSum(contents[..i+1]);
                { lemma_SeqSum_bound_prefix(contents, contents[..i+1], (i as int)+1); }
                //{ lemma_SeqSum_bound(contents, data.Length - (index as int) + 1); }
            (index as int) + SeqSum(contents);
            //data.Length;
        }
        var item_size := MarshallVal(contents[i], eltTypes[i], data, cur_index);
        //var item_size := ComputeSizeOf(contents[uint64(i)]);

        ghost var fresh_bytes := data[cur_index..cur_index + item_size];
        marshalled_bytes := marshalled_bytes + fresh_bytes;
        forall () 
            ensures var (val, rest) := parse_Val(fresh_bytes, eltTypes[i]);
                    val.Some? && val.value == contents[i];
        {
            assert SizeOfV(contents[i]) <= |fresh_bytes|;  // OBSERVE
            lemma_parse_Val_view(fresh_bytes, contents[i], eltTypes[i], 0);
        }

        ghost var old_trace := trace;
        trace := trace + [fresh_bytes];

        ghost var old_cur_index := cur_index;
        cur_index := cur_index + item_size;
        i := i + 1;
        
        assert {:split_here} true;

        // Prove the invariant about marshalled_bytes' contents
        calc {
            marshalled_bytes;
            old_marshalled_bytes + fresh_bytes;
            old_data + fresh_bytes;
            data[index..old_cur_index] + fresh_bytes;
            data[index..old_cur_index] + data[old_cur_index..cur_index];
            data[..][index..old_cur_index] + data[..][old_cur_index..cur_index];
            data[..][index..cur_index];
            data[index..cur_index];
        }

        // Prove the invariant that we stay within bounds
        calc <= {
            (index as int) + SeqSum(contents[..i]);
            calc {
                SeqSum(contents[..i]);
                <=  { lemma_SeqSum_bound_prefix(contents, contents[..i], (i as int)); }
                SeqSum(contents);
            }
            (index as int) + SeqSum(contents);
            data.Length;
        }

        // Prove the invariant about our index tracking correctly
        calc {
            (cur_index as int);
            (old_cur_index as int) + SizeOfV(contents[i-1]);
            (index as int) + SeqSum(contents[..i-1]) + SizeOfV(contents[i-1]);
                { lemma_SeqSum_prefix(contents[..i-1], contents[i-1]); 
                  assert contents[..i-1] + [contents[i-1]] == contents[..i]; }
            (index as int) + SeqSum(contents[..i]);
        }
        assert (cur_index as int) == (index as int) + SeqSum(contents[..i]);
    }

    // Prove that parsing will produce the correct result

    // After the while loop, we know:
    assert contents[..i] == contents;   // OBSERVE
    assert (cur_index as int) == (index as int) + SeqSum(contents);
    assert marshalled_bytes == data[index..(index as int)+SeqSum(contents)];
    //assert marshalled_bytes == SeqCatRev(trace);
    //assert |trace| == |contents|;
    lemma_marshall_tuple_contents(contents, eltTypes, marshalled_bytes, trace);
    size := cur_index - index;
}

method MarshallTuple(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VTuple?;
    requires ValidVal(val);
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    size := MarshallTupleContents(val.t, grammar.t, data, index);

    calc {
        parse_Val(data[index..(index as int) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_Tuple(data[index..(index as int) + SizeOfV(val)], grammar.t);
    }
}

method MarshallUint64s(ints:seq<uint64>, data:array<byte>, index:uint64)
    requires (index as int) + (Uint64Size() as int)*|ints| <= data.Length;
    requires 0 <= (index as int) + (Uint64Size() as int)*|ints| < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures forall i :: 0 <= i < |ints| ==> SeqByteToUint64(data[index as int + i*(Uint64Size() as int) .. index as int + (i+1)*(Uint64Size() as int)]) == ints[i]
    ensures  forall i :: (index as int) + (Uint64Size() as int)*|ints| <= i < data.Length ==> data[i] == old(data[i]);
{
    //Arrays.CopySeqIntoArray(bytes, 0, data, index, (|bytes| as uint64));

    var j:uint64 := 0;

    while (j < |ints| as uint64)
        invariant 0 <= (j as int) <= |ints|;
        invariant forall i :: 0 <= i < index ==> data[i] == old(data[i]);
        invariant forall i :: 0 <= i < j as int ==> SeqByteToUint64(data[index as int + i*(Uint64Size() as int) .. index as int + (i+1)*(Uint64Size() as int)]) == ints[i]
        invariant forall i :: (index as int) + (Uint64Size() as int)*|ints| <= i < data.Length ==> data[i] == old(data[i]);
    {
        MarshallUint64(ints[j], data, index + 8*j);
        j := j + 1;
    }
}

method MarshallBytes(bytes:seq<byte>, data:array<byte>, index:uint64)
    requires (index as int) + |bytes| <= data.Length;
    requires 0 <= (index as int) + |bytes| < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) <= i < (index as int) + |bytes| ==> data[i] == bytes[i - (index as int)];
    ensures  forall i :: (index as int) + |bytes| <= i < data.Length ==> data[i] == old(data[i]);
{
    Arrays.CopySeqIntoArray(bytes, 0, data, index, (|bytes| as uint64));

    /*
    var j:uint64 := 0;

    while (j < uint64(|bytes|))
        invariant 0 <= (j as int) <= |bytes|;
        invariant forall i:int :: 0 <= i < (index as int) ==> data[i] == old(data[i]);
        invariant forall i:int :: (index as int) <= i < (index as int) + (j as int) ==> data[i] == bytes[i-(index as int)];
        invariant forall i:int :: (index as int) + |bytes| <= i < data.Length ==> data[i] == old(data[i]);
    {
        data[index + j] := bytes[j];
        j := j + 1;
    }
    */
}

method MarshallByteArrayInterior(b:seq<byte>, data:array<byte>, index:uint64) returns (size:uint64)
    requires ValidVal(VByteArray(b));
    requires (index as int) + SizeOfV(VByteArray(b)) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(VByteArray(b)) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(VByteArray(b))], GByteArray).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(VByteArray(b))], GByteArray).0.value == VByteArray(b);
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(VByteArray(b)) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(VByteArray(b));
{
    MarshallUint64((|b| as uint64), data, index);
    assert SeqByteToUint64(data[index..index+(Uint64Size() as uint64)]) == (|b| as uint64);
    MarshallBytes(b, data, index + 8);

    calc {
        parse_Val(data[index..(index as int) + SizeOfV(VByteArray(b))], GByteArray);
            { reveal_parse_Val(); }
        parse_ByteArray(data[index..(index as int) + SizeOfV(VByteArray(b))]);
    }
    ghost var data_seq := data[index..(index as int) + SizeOfV(VByteArray(b))];
    ghost var tuple := parse_Uint64(data_seq);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert{:split_here} true;
    assert len.value.u == (|b| as uint64);
    
    assert rest == data[index + 8..(index as int) + SizeOfV(VByteArray(b))] == b;
    assert !len.None? && (len.value.u as int) <= |rest|;
    assert rest[0..len.value.u] == b;       // OBSERVE
    size := 8 + (|b| as uint64);
}

method MarshallMessage(m:Message, data:array<byte>, index:uint64) returns (size:uint64)
    requires ValidVal(VMessage(m));
    requires (index as int) + SizeOfV(VMessage(m)) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(VMessage(m)) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(VMessage(m))], GMessage).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(VMessage(m))], GMessage).0.value == VMessage(m);
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(VMessage(m)) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(VMessage(m));
{
  reveal_MessageSizeUint64();
  reveal_parse_Val();
  size := MarshallByteArrayInterior(m.value, data, index);
}

method MarshallByteArray(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VByteArray?;
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    MarshallUint64((|val.b| as uint64), data, index);
    assert SeqByteToUint64(data[index..index+(Uint64Size() as uint64)]) == (|val.b| as uint64);
    MarshallBytes(val.b, data, index + 8);

    calc {
        parse_Val(data[index..(index as int) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_ByteArray(data[index..(index as int) + SizeOfV(val)]);
    }
    ghost var data_seq := data[index..(index as int) + SizeOfV(val)];
    ghost var tuple := parse_Uint64(data_seq);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert{:split_here} true;
    assert len.value.u == (|val.b| as uint64);
    
    assert rest == data[index + 8..(index as int) + SizeOfV(val)] == val.b;
    assert !len.None? && (len.value.u as int) <= |rest|;
    assert rest[0..len.value.u] == val.b;       // OBSERVE
    size := 8 + (|val.b| as uint64);
}

lemma parse_Uint64ArrayContents_eq_seq(data: seq<byte>, ints: seq<uint64>)
  requires |data| < 0x1_0000_0000_0000_0000;
  requires |data| == 8 * |ints|
  requires forall i :: 0 <= i < |ints| ==> SeqByteToUint64(data[i*8 .. (i+1)*8]) == ints[i]
  ensures SeqByteToSeqUint64(data, |ints|) == ints
{
  if (|ints| == 0) {
  } else {
    forall i | 0 <= i < |ints| - 1
    ensures SeqByteToUint64(data[.. (|ints| - 1) * 8][i*8 .. (i+1)*8]) == ints[.. |ints| - 1][i]
    {
    }
    parse_Uint64ArrayContents_eq_seq(data[.. (|ints| - 1) * 8], ints[.. |ints| - 1]);
  }
}

lemma parse_Uint64Array_eq_seq(data: seq<byte>, ints: seq<uint64>)
  requires |data| < 0x1_0000_0000_0000_0000;
  requires |data| == 8 + 8 * |ints|
  requires SeqByteToUint64(data[0..8]) as int == |ints|
  requires forall i :: 0 <= i < |ints| ==> SeqByteToUint64(data[8 + i*8 .. 8 + (i+1)*8]) == ints[i]
  ensures parse_Uint64Array(data).0.Some?
  ensures parse_Uint64Array(data).0.value.ua == ints
{
  forall i | 0 <= i < |ints| ensures SeqByteToUint64(data[8..][i*8 .. (i+1)*8]) == ints[i]
  {
    assert data[8..][i*8 .. (i+1)*8] == data[8 + i*8 .. 8 + (i+1)*8];
  }
  parse_Uint64ArrayContents_eq_seq(data[8..], ints);
  assert data[8..] == data[8..][..8*|ints|];
}

method MarshallUint64Array(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VUint64Array?;
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some?
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    MarshallUint64((|val.ua| as uint64), data, index);
    assert SeqByteToUint64(data[index..index+(Uint64Size() as uint64)]) == (|val.ua| as uint64);
    MarshallUint64s(val.ua, data, index + 8);
    assert SeqByteToUint64(data[index..index+(Uint64Size() as uint64)]) == (|val.ua| as uint64);

    calc {
        parse_Val(data[index..(index as int) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_Uint64Array(data[index..(index as int) + SizeOfV(val)]);
    }
    ghost var data_seq := data[index..(index as int) + SizeOfV(val)];
    ghost var tuple := parse_Uint64(data_seq);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    //assert{:split_here} true;
    assert data[index..(index as int) + SizeOfV(val)][..8] == data[index..index+8];
    assert len.value.u
        == SeqByteToUint64(data_seq[..8])
        == SeqByteToUint64(data[index .. index + 8])
        == SeqByteToUint64(data[index .. index + (Uint64Size() as uint64)])
        == (|val.ua| as uint64);
    
    //assert rest == data[index + 8..(index as int) + SizeOfV(val)] == val.ua;
    assert !len.None? && (len.value.u as int) <= |rest|;
    //assert rest[0..len.value.u] == val.ua;       // OBSERVE
    size := 8 + (Uint64Size() * |val.ua| as uint64);

    forall i | 0 <= i < |val.ua|
    ensures SeqByteToUint64(data_seq[8 + i*8 .. 8 + (i+1)*8]) == val.ua[i]
    {
      MarshallUint64_index_splicing(data, index, val, i);
    }
    parse_Uint64Array_eq_seq(data_seq, val.ua);
}


method MarshallCase(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VCase?;
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    MarshallUint64(val.c, data, index);
    ghost var int_bytes := data[index..index+Uint64Size()];
    ghost var tuple0 := parse_Uint64(int_bytes);
    ghost var caseID0 := tuple0.0;
    ghost var rest10   := tuple0.1;
    assert !caseID0.None?;
    assert caseID0.value.u == val.c;

    var val_size := MarshallVal(val.val, grammar.cases[val.c], data, index + 8);

    ghost var new_int_bytes := data[index..index+Uint64Size()];
    assert forall i {:auto_trigger} :: 0 <= i < Uint64Size() ==> int_bytes[i] == new_int_bytes[i];
    assert int_bytes == new_int_bytes;

    assert val.VCase?; 
    assert grammar.GTaggedUnion?; 
    assert (val.c as int) < |grammar.cases|;

    ghost var bytes := data[index..(index as int) + SizeOfV(val)];
    assert bytes[..8] == new_int_bytes;
    calc {
        parse_Val(bytes, grammar);
            { reveal_parse_Val(); }
        parse_Case(bytes, grammar.cases);
    }

    assert{:split_here} true;
    ghost var tuple1 := parse_Uint64(bytes);
    ghost var caseID := tuple1.0;
    ghost var rest1   := tuple1.1;

    assert !caseID.None?;
    assert caseID.value.u == val.c;
    assert (caseID.value.u as int) < |grammar.cases|;
    ghost var tuple2 := parse_Val(rest1, grammar.cases[caseID.value.u]);
    ghost var v:= tuple2.0;
    ghost var rest2 := tuple2.1;
    assert !v.None?;

    size := 8 + val_size;
}

function parse_Message(data:seq<byte>)
  : (res : (Option<Message>, seq<byte>))
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures |res.1| < 0x1_0000_0000_0000_0000;
{
  var (val, rest1) := parse_ByteArray(data);
  if !val.None? && |val.value.b| as uint64 <= ValueWithDefault.MaxLen() then
    (Some(ValueMessage.Define(val.value.b)), rest1)
  else
    (None, [])
}

method ParseMessage(data:seq<byte>, index:uint64) returns (success:bool, v:Message, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Message(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
{
  var bytes;
  success, bytes, rest_index := ParseByteArray(data, index);
  if success && |bytes| as uint64 <= ValueWithDefault.MaxLen() {
    v := ValueMessage.Define(bytes);
  } else {
    success := false;
    rest_index := |data| as uint64;
  }
}


function {:opaque} parse_MessageArray_contents(data:seq<byte>, len:uint64) : (Option<seq<Message>>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    decreases len
    ensures var (opt_seq, rest) := parse_MessageArray_contents(data, len);
            |rest| <= |data| && (opt_seq.Some? ==>
            && |opt_seq.value| == len as int
            && (forall i :: 0 <= i < |opt_seq.value| ==> ValidMessage(opt_seq.value[i]))
            )
{
   if len == 0 then
       (Some([]), data)
   else
       var (val, rest1) := parse_Message(data);
       var (others, rest2) := parse_MessageArray_contents(rest1, len - 1);
       if !val.None? && !others.None? then
           (Some([val.value] + others.value), rest2)
       else
           (None, [])
}

datatype MessageArray_ContentsTraceStep = MessageArray_ContentsTraceStep(data:seq<byte>, val:Option<Message>)

lemma lemma_MessageArrayContents_helper(data:seq<byte>, len:uint64, v:seq<Message>, trace:seq<MessageArray_ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires |trace| == (len as int) + 1;
    requires |v| == (len as int);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> trace[j].val.Some?;
    requires forall j :: 0 < j < (len as int)+1 ==> 
                    Some(trace[j].val.value) == parse_Message(trace[j-1].data).0
                 && trace[j].data == parse_Message(trace[j-1].data).1;
    requires forall j :: 0 < j < |trace| ==> v[j-1] == trace[j].val.value;
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_MessageArray_contents(data, len);
             var v_opt := Some(v);
             v_opt == v' && trace[|trace|-1].data == rest';
{
    reveal_parse_MessageArray_contents();
    if len == 0 {
    } else {
        var tuple := parse_Message(data);
        var val, rest1 := tuple.0, tuple.1;
        assert trace[1].data == rest1;
        assert val.Some?;
        assert trace[1].val == Some(val.value);
        lemma_MessageArrayContents_helper(rest1, len-1, v[1..], trace[1..]);
        var tuple'' := parse_MessageArray_contents(rest1, len-1);
        var v'', rest'' := tuple''.0, tuple''.1;
        var v_opt'' := Some(v[1..]);
        assert v_opt'' == v'' && trace[1..][|trace[1..]|-1].data == rest'';

        var tuple' := parse_MessageArray_contents(data, len);
        var v', rest' := tuple'.0, tuple'.1;
        calc { 
            v'; 
            Some([val.value] + v''.value);
            Some([val.value] + v[1..]);
            Some([v[0]] + v[1..]);
                { assert v == [v[0]] + v[1..]; }
            Some(v);
        }
        assert rest' == rest'';
    }
}

lemma lemma_MessageArrayContents_helper_bailout(data:seq<byte>, len:uint64, trace:seq<MessageArray_ContentsTraceStep>)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires 1 < |trace| <= (len as int) + 1;
    //requires |v| == (len as int);
    requires forall j :: 0 <= j < |trace| ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
    requires trace[0].data == data;
    requires forall j :: 0 < j < |trace| ==> 
                    (trace[j].val.None? ==> parse_Message(trace[j-1].data).0.None?)
                 && (trace[j].val.Some? ==> parse_Message(trace[j-1].data).0.Some? && trace[j].val.value  == parse_Message(trace[j-1].data).0.value)
                 && trace[j].data == parse_Message(trace[j-1].data).1;
    requires forall j :: 0 < j < |trace| - 1 ==> trace[j].val.Some?;
    //requires forall j :: 0 < j < |trace| - 1 ==> v[j-1] == trace[j].val.value;
    requires trace[|trace|-1].val.Some? ==> trace[|trace|-1].val.value.Define?
    requires trace[|trace|-1].val.None? || |trace[|trace|-1].val.value.value| > ValueWithDefault.MaxLen() as int
    //requires v == ExtractValues(trace[1..]);
    decreases len;
    ensures  var (v', rest') := parse_MessageArray_contents(data, len);
             v'.None? && rest' == [];
{
    reveal_parse_MessageArray_contents();
    
    var tuple := parse_Message(data);
    var val, rest1 := tuple.0, tuple.1;
    if |trace| == 2 {
      if (trace[|trace|-1].val.None?) {
        assert val.None?;
      }
        
      assert val.None? || !(|val.value.value| as uint64 <= ValueWithDefault.MaxLen());
      var tuple' := parse_MessageArray_contents(data, len);
      var v', rest' := tuple'.0, tuple'.1;
      assert v'.None?;
      assert rest' == [];
    } else {
      lemma_MessageArrayContents_helper_bailout(rest1, len-1, trace[1..]);
    }
}

method{:timeLimitMultiplier 2} ParseMessageArrayContents(data:seq<byte>, index:uint64, len:uint64) 
       returns (success:bool, v:seq<Message>, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_MessageArray_contents(data[index..], len);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(VMessageArray(v));
{
    reveal_parse_MessageArray_contents();
    var vArr := new Message[len];
    ghost var g_v := [];
    success := true;
    var i:uint64 := 0;
    var next_val_index:uint64 := index;
    ghost var trace := [MessageArray_ContentsTraceStep(data[index..], None())];

    while i < len
        invariant 0 <= i <= len;
        invariant index <= next_val_index <= (|data| as uint64);
        invariant |trace| == (i as int) + 1;
        invariant |g_v| == (i as int);
        invariant vArr[..i] == g_v;
        invariant trace[0].data == data[index..];
        invariant forall j :: 0 <= j < (i as int)+1 ==> |trace[j].data| < 0x1_0000_0000_0000_0000;
        invariant trace[i].data == data[next_val_index..];
        invariant forall j :: 0 < j <= i ==> trace[j].val.Some?;
        invariant forall j :: 0 < j <= i ==> g_v[j-1] == trace[j].val.value;
        invariant forall j :: 0 < j < (i as int)+1 ==> 
            Some(trace[j].val.value) == parse_Message(trace[j-1].data).0
         && trace[j].data == parse_Message(trace[j-1].data).1
        invariant ValidVal(VMessageArray(vArr[..i]));
    {
        var some1, val, rest1 := ParseMessage(data, next_val_index);
        ghost var step := MessageArray_ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
        ghost var old_trace := trace;
        trace := trace + [step];
        if !some1 || |val.value| as uint64 > ValueWithDefault.MaxLen() {
            success := false;
            rest_index := (|data| as uint64);
            lemma_MessageArrayContents_helper_bailout(data[index..], len, trace);
            return;
        }
        g_v := g_v + [val];
        vArr[i] := val;
        next_val_index := rest1;

        i := i + 1;
    }

    success := true;
    rest_index := next_val_index;
    v := vArr[..];               
    lemma_MessageArrayContents_helper(data[index..], len, v, trace);
}

function parse_MessageArray(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures var (opt_val, rest) := parse_MessageArray(data);
            |rest| <= |data| && (opt_val.Some? ==>
              && ValidVal(opt_val.value)
              && ValInGrammar(opt_val.value, GMessageArray));
{
    var (len, rest) := parse_Uint64(data);
    if !len.None? then
        var (contents, remainder) := parse_MessageArray_contents(rest, len.value.u);
        if !contents.None? then
            (Some(VMessageArray(contents.value)), remainder)
        else
            (None, [])
    else
        (None, [])
}

method ParseMessageArray(data:seq<byte>, index:uint64) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_MessageArray(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
    ensures  success ==> ValidVal(v);
{
    var some1, len, rest := ParseUint64(data, index);
    if some1 {
        var some2, contents, remainder := ParseMessageArrayContents(data, rest, len.u);
        if some2 {
            success := true;
            v := VMessageArray(contents);
            rest_index := remainder;
        } else {
            success := false;
            rest_index := (|data| as uint64);
        }
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

lemma lemma_parse_MessageArray_contents_len(data:seq<byte>, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires len >= 0;
    requires !parse_MessageArray_contents(data, len).0.None?;
    decreases len;
    ensures  (len as int) == |parse_MessageArray_contents(data, len).0.value|;
{
    reveal_parse_MessageArray_contents();
    if len == 0 {
    } else {
       var tuple1 := parse_Message(data);
       var val   := tuple1.0;
       var rest1 := tuple1.1;
       var tuple2 := parse_MessageArray_contents(rest1, len - 1);
       var others := tuple2.0;
       var rest2  := tuple2.1;
       assert !val.None? && !others.None?;
       lemma_parse_MessageArray_contents_len(rest1, len - 1);
    }
}

lemma lemma_parse_MessageArray_contents_first(data:seq<byte>, len: uint64, vs: seq<Message>)
requires |data| < 0x1_0000_0000_0000_0000;
requires parse_MessageArray_contents(data, len).0 == Some(vs)
requires len > 0
ensures parse_Message(data).0.Some?
ensures parse_Message(data).0.value == vs[0]
{
  reveal_parse_MessageArray_contents();
}

lemma {:fuel parse_Message,0} lemma_parse_Val_view_MessageArray_contents(data:seq<byte>, vs:seq<Message>, index:int, bound:int, len:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires (len as int) == |vs|;
    requires 0 <= index <= |data|;
    requires 0 <= index + SeqSumMessageLens(vs) <= |data|;
    requires index+SeqSumMessageLens(vs) <= bound <= |data|;
    decreases len;
    //decreases |vs|;
    ensures  (parse_MessageArray_contents(data[index..bound], len).0 == Some(vs)) <==> (parse_MessageArray_contents(data[index..index+SeqSumMessageLens(vs)], len).0 == Some(vs));
    ensures  parse_MessageArray_contents(data[index..bound], len).0 == Some(vs) ==> parse_MessageArray_contents(data[index..bound], len).1 == data[index+SeqSumMessageLens(vs)..bound];
{
    reveal_parse_MessageArray_contents();
    if len == 0 {
        reveal_SeqSumMessageLens();
    } else {
        var narrow_tuple := parse_MessageArray_contents(data[index..index+SeqSumMessageLens(vs)], len);
        var bound_tuple := parse_MessageArray_contents(data[index..bound], len);
        var narrow_val_tuple := parse_Message(data[index..index+SeqSumMessageLens(vs)]);
        var bound_val_tuple := parse_Message(data[index..bound]);
        var narrow_contents_tuple := parse_MessageArray_contents(narrow_val_tuple.1, len - 1);
        var bound_contents_tuple := parse_MessageArray_contents(bound_val_tuple.1, len - 1);


        if narrow_tuple.0 == Some(vs) {
            assert !narrow_val_tuple.0.None? && !narrow_contents_tuple.0.None?;
            calc {
                index + SeqSumMessageLens(vs) <= |data|;
                SeqSumMessageLens(vs) <= |data| - index;
                SeqSumMessageLens(vs) < |data| - index + 1;
            }
            lemma_SeqSumMessageLens_bound(vs, |data| - index + 1);
            lemma_parse_Val_view_Message(data, VMessage(vs[0]), GMessage, index);

            lemma_SeqSumMessageLens_bound(vs, SeqSumMessageLens(vs) + 1);
            assert index+SizeOfV(VMessage(vs[0])) <= bound <= |data|;
            assert (parse_Message(data[index..index+SeqSumMessageLens(vs)]).0 == Some(vs[0])) <==> (parse_Message(data[index..index+SizeOfV(VMessage(vs[0]))]).0 == Some(vs[0]));
            lemma_SeqSumMessageLens_bound(vs, bound - index + 1);
            assert index+SizeOfV(VMessage(vs[0])) <= bound <= |data|;     // OBSERVE (trigger on forall?)
            assert (parse_Message(data[index..bound]).0 == Some(vs[0])) <==> (parse_Message(data[index..index+SizeOfV(VMessage(vs[0]))]).0 == Some(vs[0]));
            lemma_parse_MessageArray_contents_first(data[index..index+SeqSumMessageLens(vs)], len, vs);
            assert narrow_val_tuple.0.value == vs[0]
                == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(VMessage(narrow_val_tuple.0.value));
            calc {
                SizeOfV(VMessage(narrow_val_tuple.0.value)) + SeqSumMessageLens(vs[1..]);
                    { reveal_SeqSumMessageLens(); }
                SeqSumMessageLens(vs);
            }
            assert new_index+SeqSumMessageLens(vs[1..]) <= bound;

            lemma_parse_Val_view_MessageArray_contents(data, vs[1..], new_index, bound, len - 1);

            assert (parse_MessageArray_contents(data[new_index..bound], len - 1).0 == Some(vs[1..])) <==> (parse_MessageArray_contents(data[new_index..new_index+SeqSumMessageLens(vs[1..])], len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSumMessageLens(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert bound_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else if bound_tuple.0 == Some(vs) {
            assert !bound_val_tuple.0.None? && !bound_contents_tuple.0.None?;

            lemma_SeqSumMessageLens_bound(vs, |data| - index + 1);
            lemma_parse_Val_view_Message(data, VMessage(vs[0]), GMessage, index);
            // This is exactly the ensures of the lemma above
            assert forall bound' :: index+SizeOfV(VMessage(vs[0])) <= bound' <= |data| ==>
                   ((parse_Message(data[index..bound']).0 == Some(vs[0])) <==> (parse_Message(data[index..index+SizeOfV(VMessage(vs[0]))]).0 == Some(vs[0])));

            lemma_SeqSumMessageLens_bound(vs, bound - index + 1);
            lemma_SeqSumMessageLens_bound(vs, SeqSumMessageLens(vs) + 1);
            assert index+SizeOfV(VMessage(vs[0])) <= index+SeqSumMessageLens(vs) <= |data|;
            assert (parse_Message(data[index..index+SeqSumMessageLens(vs)]).0 == Some(vs[0])) <==> (parse_Message(data[index..index+SizeOfV(VMessage(vs[0]))]).0 == Some(vs[0]));
            assert (parse_Message(data[index..bound]).0 == Some(vs[0])) <==> (parse_Message(data[index..index+SizeOfV(VMessage(vs[0]))]).0 == Some(vs[0]));
            lemma_parse_MessageArray_contents_first(data[index..bound], len, vs);
            assert narrow_val_tuple.0.value == vs[0]
                == bound_val_tuple.0.value;

            var new_index := index + SizeOfV(VMessage(narrow_val_tuple.0.value));
            calc {
                SizeOfV(VMessage(narrow_val_tuple.0.value)) + SeqSumMessageLens(vs[1..]);
                    { reveal_SeqSumMessageLens(); }
                SeqSumMessageLens(vs);
            }
            assert new_index+SeqSumMessageLens(vs[1..]) <= bound;

            lemma_parse_Val_view_MessageArray_contents(data, vs[1..], new_index, bound, len - 1);

            // TODO I'm not sure why but this next part is really really slow.

            assert (parse_MessageArray_contents(data[new_index..bound], len - 1).0 == Some(vs[1..])) <==> (parse_MessageArray_contents(data[new_index..new_index+SeqSumMessageLens(vs[1..])], len - 1).0 == Some(vs[1..]));
            assert data[new_index..new_index+SeqSumMessageLens(vs[1..])] == narrow_val_tuple.1;
            assert data[new_index..bound] == bound_val_tuple.1;

            assert narrow_tuple.0 == Some([vs[0]] + vs[1..]) == Some(vs);
        } else {
            // Doesn't matter for our ensures clause
        }
    }
}

lemma lemma_parse_Val_view_MessageArray(data:seq<byte>, v:V, grammar: G, index:int, bound:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GMessageArray?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    requires index+SizeOfV(v) <= bound <= |data|;
    ensures  (parse_MessageArray(data[index..bound]).0 == Some(v)) <==> (parse_MessageArray(data[index..index+SizeOfV(v)]).0 == Some(v));
    ensures  parse_MessageArray(data[index..bound]).0 == Some(v) ==> parse_MessageArray(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
{
    var narrow_tuple := parse_MessageArray(data[index..index+SizeOfV(v)]);
    var bound_tuple := parse_MessageArray(data[index..bound]);
    var narrow_len_tuple := parse_Uint64(data[index..index+SizeOfV(v)]);
    var bound_len_tuple := parse_Uint64(data[index..bound]);
    var narrow_contents_tuple := parse_MessageArray_contents(narrow_len_tuple.1, narrow_len_tuple.0.value.u);
    var bound_contents_tuple := parse_MessageArray_contents(bound_len_tuple.1, bound_len_tuple.0.value.u);

    assert narrow_len_tuple.0 == bound_len_tuple.0;

    if bound_tuple.0 == Some(v) {
        assert parse_MessageArray_contents(bound_len_tuple.1, bound_len_tuple.0.value.u).0 == Some(v.ma);   // OBSERVE
        lemma_parse_MessageArray_contents_len(bound_len_tuple.1, narrow_len_tuple.0.value.u);
        lemma_parse_Val_view_MessageArray_contents(data, v.ma, index+8, bound, narrow_len_tuple.0.value.u);
    }

    if narrow_tuple.0 == Some(v) {
        assert parse_MessageArray_contents(narrow_len_tuple.1, narrow_len_tuple.0.value.u).0 == Some(v.ma);   // OBSERVE
        lemma_parse_MessageArray_contents_len(narrow_len_tuple.1, narrow_len_tuple.0.value.u);
        lemma_parse_Val_view_MessageArray_contents(data, v.ma, index+8, bound, narrow_len_tuple.0.value.u);
    }
}

lemma lemma_marshall_messagearray_contents(contents:seq<Message>, marshalled_bytes:seq<byte>, trace:seq<seq<byte>>)
    requires forall v :: v in contents ==> ValidMessage(v)
    requires |marshalled_bytes| < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    requires |contents| == |trace|;
    requires |marshalled_bytes| == SeqSumMessageLens(contents);
    requires marshalled_bytes == SeqCatRev(trace);
    requires forall j :: 0 <= j < |trace| ==> MessageSize(contents[j]) == |trace[j]| < 0x1_0000_0000_0000_0000;
    requires forall j :: 0 <= j < |trace| ==> var (val, rest) := parse_Message(trace[j]); val.Some? && val.value == contents[j];

    ensures  parse_MessageArray_contents(marshalled_bytes, (|contents| as uint64)).0.Some?;
    ensures  parse_MessageArray_contents(marshalled_bytes, (|contents| as uint64)).0.value == contents;
{
    if |contents| == 0 {
        reveal_parse_MessageArray_contents();
    } else {
        var val_tuple := parse_Message(marshalled_bytes);
        var val, rest1 := val_tuple.0, val_tuple.1;
        var rest_tuple := parse_MessageArray_contents(rest1, (|contents| as uint64)-1);
        var others, rest2 := rest_tuple.0, rest_tuple.1;
        var target := parse_MessageArray_contents(marshalled_bytes, (|contents| as uint64)).0;
        calc {
            target;
                { reveal_parse_MessageArray_contents(); }
            if !val.None? && !others.None? && |val.value.value| as uint64 <= ValueWithDefault.MaxLen() then Some([val.value] + others.value) else None;
        }

        calc {
            SeqCatRev(trace);
                { lemma_SeqCat_equivalent(trace); }
            SeqCat(trace);
        }

        assert marshalled_bytes[0..SizeOfV(VMessage(contents[0]))] == trace[0];
        assert parse_Message(trace[0]).0.Some?;
        assert parse_Message(trace[0]).0.value == contents[0];
        //assert parse_Val(trace[0], GByteArray).0 == Some(VByteArray(contents[0]));
        //assert parse_Val(marshalled_bytes[..SizeOfV(VByteArray(contents[0]))], GByteArray).0 == Some(VByteArray(contents[0]));
        reveal_parse_Val();
        lemma_parse_Val_view_specific(marshalled_bytes, VMessage(contents[0]), GMessage, 0, |marshalled_bytes|);
        assert parse_Message(marshalled_bytes[0..|marshalled_bytes|]).0.value == contents[0];
        assert marshalled_bytes[0..|marshalled_bytes|] == marshalled_bytes;     // OBSERVE
        assert val.Some? && val.value == contents[0];
        assert rest1 == marshalled_bytes[SizeOfV(VMessage(contents[0]))..];

        // Prove a requires for the recursive call
        calc {
            marshalled_bytes[SizeOfV(VMessage(contents[0]))..];
                calc {
                    marshalled_bytes;
                    SeqCatRev(trace);
                        { lemma_SeqCat_equivalent(trace); }
                    SeqCat(trace);
                    trace[0] + SeqCat(trace[1..]);
                        { lemma_SeqCat_equivalent(trace[1..]); }
                    trace[0] + SeqCatRev(trace[1..]);
                }
            (trace[0] + SeqCatRev(trace[1..]))[SizeOfV(VMessage(contents[0]))..];
                { assert |trace[0]| == SizeOfV(VMessage(contents[0])); }
            SeqCatRev(trace[1..]);
        }

        // Prove a requires for the recursive call
        calc {
            SeqSumMessageLens(contents);
                { reveal_SeqSumMessageLens(); }
            SizeOfV(VMessage(contents[0])) + SeqSumMessageLens(contents[1..]);
        }
        lemma_marshall_messagearray_contents(contents[1..], marshalled_bytes[SizeOfV(VMessage(contents[0]))..], trace[1..]);
        assert others.Some?;
        assert others.value == contents[1..];
        assert contents == [contents[0]] + contents[1..];
       
    }
}

method{:timeLimitMultiplier 4} MarshallMessageArrayContents(contents:seq<Message>, data:array<byte>, index:uint64) returns (size:uint64)
    requires (index as int) + SeqSumMessageLens(contents) <= data.Length;
    requires 0 <= (index as int) + SeqSumMessageLens(contents) < 0x1_0000_0000_0000_0000;
    requires data.Length < 0x1_0000_0000_0000_0000;
    requires |contents| < 0x1_0000_0000_0000_0000;
    requires forall j | 0 <= j < |contents| :: ValidMessage(contents[j])
    decreases |contents|;
    modifies data;
    ensures  parse_MessageArray_contents(data[index..(index as int) + SeqSumMessageLens(contents)], (|contents| as uint64)).0.Some?;
    ensures  parse_MessageArray_contents(data[index..(index as int) + SeqSumMessageLens(contents)], (|contents| as uint64)).0.value == contents;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SeqSumMessageLens(contents) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SeqSumMessageLens(contents);
{
    var i:uint64 := 0;
    var cur_index := index;
    reveal_SeqSumMessageLens();
    reveal_parse_MessageArray_contents();

    ghost var trace := [];
    ghost var marshalled_bytes := [];

    while i < (|contents| as uint64)
        invariant 0 <= (i as int) <= |contents|;
        invariant 0 <= (index as int) <= (index as int) + SeqSumMessageLens(contents[..i]) <= data.Length;
        invariant (cur_index as int) == (index as int) + SeqSumMessageLens(contents[..i]);
        invariant forall j :: 0 <= j < index ==> data[j] == old(data[j]);
        invariant forall j :: (index as int) + SeqSumMessageLens(contents) <= j < data.Length ==> data[j] == old(data[j]);
        invariant marshalled_bytes == data[index..cur_index];
        invariant marshalled_bytes == SeqCatRev(trace);
        invariant |trace| == (i as int);
        invariant forall j :: 0 <= j < |trace| ==> SizeOfV(VMessage(contents[j])) == |trace[j]| < 0x1_0000_0000_0000_0000;
        invariant forall j :: 0 <= j < |trace| ==> 
                        var (val, rest) := parse_Message(trace[j]); 
                        val.Some? && val.value == contents[j]; 
    {
        lemma_SeqSumMessageLens_bound(contents, 0x1_0000_0000_0000_0000);

        // Prove we meet MarshallVal's length requirement
        calc <= {
            (cur_index as int) + SizeOfV(VMessage(contents[i]));
            (index as int) + SeqSumMessageLens(contents[..i]) + SizeOfV(VMessage(contents[i]));
                { lemma_SeqSumMessageLens_prefix(contents[..i], contents[i]); 
                  assert contents[..i] + [contents[i]] == contents[..i+1]; }
            (index as int) + SeqSumMessageLens(contents[..i+1]);
                { lemma_SeqSumMessageLens_bound_prefix(contents, contents[..i+1], (i as int)+1); }
                //{ lemma_SeqSum_bound(contents, data.Length - (index as int) + 1); }
            (index as int) + SeqSumMessageLens(contents);
            //data.Length;
        }
        var item_size := MarshallMessage(contents[i], data, cur_index);
        //var item_size := ComputeSizeOf(contents[uint64(i)]);

        ghost var fresh_bytes := data[cur_index..cur_index + item_size];
        marshalled_bytes := marshalled_bytes + fresh_bytes;
        forall () 
            ensures var (val, rest) := parse_Message(fresh_bytes);
                    val.Some? && val.value == contents[i];
        {
            assert SizeOfV(VMessage(contents[i])) <= |fresh_bytes|;  // OBSERVE
            reveal_parse_Val();
            lemma_parse_Val_view(fresh_bytes, VMessage(contents[i]), GMessage, 0);
        }

        ghost var old_trace := trace;
        trace := trace + [fresh_bytes];

        ghost var old_cur_index := cur_index;
        cur_index := cur_index + item_size;
        i := i + 1;

        // Prove the invariant that we stay within bounds
        calc <= {
            (index as int) + SeqSumMessageLens(contents[..i]);
            calc {
                SeqSumMessageLens(contents[..i]);
                <=  { lemma_SeqSumMessageLens_bound_prefix(contents, contents[..i], (i as int)); }
                SeqSumMessageLens(contents);
            }
            (index as int) + SeqSumMessageLens(contents);
            data.Length;
        }
        assert {:split_here} true;
        assert marshalled_bytes == data[index..cur_index];

        // Prove the invariant about our index tracking correctly
        calc {
            (cur_index as int);
            (old_cur_index as int) + SizeOfV(VMessage(contents[i-1]));
            (index as int) + SeqSumMessageLens(contents[..i-1]) + SizeOfV(VMessage(contents[i-1]));
                { lemma_SeqSumMessageLens_prefix(contents[..i-1], contents[i-1]); 
                  assert contents[..i-1] + [contents[i-1]] == contents[..i]; }
            (index as int) + SeqSumMessageLens(contents[..i]);
        }
        assert (cur_index as int) == (index as int) + SeqSumMessageLens(contents[..i]);
        assert marshalled_bytes == data[index..cur_index];
    }

    // Prove that parsing will produce the correct result

    // After the while loop, we know:
    assert contents[..i] == contents;   // OBSERVE
    assert (cur_index as int) == (index as int) + SeqSumMessageLens(contents);
    assert marshalled_bytes == data[index..(index as int)+SeqSumMessageLens(contents)];
    //assert marshalled_bytes == SeqCatRev(trace);
    //assert |trace| == |contents|;
    lemma_marshall_messagearray_contents(contents, marshalled_bytes, trace);
    size := cur_index - index;
}

method MarshallMessageArray(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VMessageArray?;
    requires ValInGrammar(val, grammar);
    requires ValidGrammar(grammar);
    requires ValidVal(val);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, -1;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    //assert{:split_here} true;
    reveal_parse_Val();
    MarshallUint64((|val.ma| as uint64), data, index);

    ghost var tuple := parse_Uint64(data[index..(index as int) + SizeOfV(val)]);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert !len.None?;
    var contents_size := MarshallMessageArrayContents(val.ma, data, index + Uint64Size());
    tuple := parse_Uint64(data[index..(index as int) + SizeOfV(val)]);
    assert {:split_here} true;
    len := tuple.0;
    rest := tuple.1;
    assert !len.None?;
    ghost var contents_tuple := parse_MessageArray_contents(rest, len.value.u);
    ghost var contents  := contents_tuple.0;
    ghost var remainder := contents_tuple.1;
    assert !contents.None?;
    size := 8 + contents_size;
}

method MarshallVUint64(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VUint64?;
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires 0 <= (index as int) + SizeOfV(val) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    MarshallUint64(val.u, data, index);
    calc {
        parse_Val(data[index..(index as int) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_Uint64(data[index..(index as int) + SizeOfV(val)]);
    }
    return 8;
}

method MarshallVal(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000;
    requires (index as int) + SizeOfV(val) <= data.Length;
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    decreases grammar, 0;
    ensures  parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.Some? &&
             parse_Val(data[index..(index as int) + SizeOfV(val)], grammar).0.value == val;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i]);
    ensures  (size as int) == SizeOfV(val);
{
    match val
        case VUint64(_)    => size := MarshallVUint64(val, grammar, data, index);
        case VArray(_)     => size := MarshallArray(val, grammar, data, index);
        case VKeyArray(_) => size := MarshallKeyArray(val, grammar, data, index);
        case VTuple(_)     => size := MarshallTuple(val, grammar, data, index);
        case VUint64Array(_) => size := MarshallUint64Array(val, grammar, data, index);
        case VByteArray(_) => size := MarshallByteArray(val, grammar, data, index);
        case VMessage(_) => size := MarshallMessage(val.m, data, index);
        case VMessageArray(_) => size := MarshallMessageArray(val, grammar, data, index);
        case VCase(_,_)    => size := MarshallCase(val, grammar, data, index);
}

method Marshall(val:V, ghost grammar:G) returns (data:array<byte>)
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000;
    ensures fresh(data);
    ensures Demarshallable(data[..], grammar);
    ensures parse_Val(data[..], grammar).0.Some? && parse_Val(data[..], grammar).0.value == val;
    ensures parse_Val(data[..], grammar).1 == [];
    ensures |data[..]| == SizeOfV(val);
{
    var size := ComputeSizeOf(val);
    data := new byte[size];

    var computed_size := MarshallVal(val, grammar, data, 0);

    assert data[0..0 + SizeOfV(val)] == data[0..0 + size] == data[..];      // OBSERVE

    lemma_parse_Val_view_specific(data[..], val, grammar, 0, (size as int));
}


} 
