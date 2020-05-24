include "../Lang/NativeTypes.s.dfy"
include "../Base/total_order.i.dfy"
include "../Math/bases.i.dfy"
include "Maps.i.dfy"
include "Seqs.i.dfy"
include "Util.i.dfy"
include "../Base/NativeArrays.s.dfy"
include "../Base/PackedInts.s.dfy"

module GenericMarshalling {
//import opened Util__be_sequences_s
import opened NativeTypes
import opened Collections__Maps_i
import opened Collections__Seqs_i 
import opened Common__Util_i
import opened Libraries__base_s
import opened Options
//import opened Math__power2_i
import NativeArrays
import opened Math
import opened NativePackedInts
import opened Sequences

export S
  provides NativeTypes, parse_Val, ParseVal, Marshall, Demarshallable,
      ComputeSizeOf, Options, MarshallVal, lemma_parse_Val_view_specific, lemma_SeqSum_prefix,
      lemma_SizeOfV_parse_Val
  reveals G, V, ValidGrammar, ValInGrammar, ValidVal, SizeOfV, SeqSum

export Internal reveals *

export extends S

datatype G = GUint32
           | GUint64
           | GArray(elt:G)
           | GTuple(t:seq<G>)
           | GByteArray
           | GUint32Array
           | GUint64Array
           | GTaggedUnion(cases:seq<G>)

datatype V = VUint32(v:uint32)
           | VUint64(u:uint64)
           | VArray(a:seq<V>)
           | VTuple(t:seq<V>)
           | VByteArray(b:seq<byte>)
           | VUint32Array(va:seq<uint32>)
           | VUint64Array(ua:seq<uint64>)
           | VCase(c:uint64, val:V)

predicate ValInGrammar(val:V, grammar:G)
{
    match val
        case VUint32(_) => grammar.GUint32?
        case VUint64(_) => grammar.GUint64?
        case VArray(a)  => grammar.GArray? && forall v :: v in a ==> ValInGrammar(v, grammar.elt)
        case VTuple(t)  => grammar.GTuple? && |t| == |grammar.t|
                              && forall i :: 0 <= i < |t| ==> ValInGrammar(t[i], grammar.t[i])
        case VByteArray(b) => grammar.GByteArray?
        case VUint32Array(va) => grammar.GUint32Array?
        case VUint64Array(ua) => grammar.GUint64Array?
        case VCase(c, v) => grammar.GTaggedUnion? && (c as int) < |grammar.cases| && ValInGrammar(v, grammar.cases[c])
}

// We only support reasonably sized grammars
predicate ValidGrammar(grammar:G) 
{
    match grammar
        case GUint32 => true
        case GUint64 => true
        case GArray(elt) => ValidGrammar(elt)
        case GTuple(t) => |t| < 0x1_0000_0000_0000_0000 && (forall g :: g in t ==> ValidGrammar(g))
        case GByteArray => true
        case GUint32Array => true
        case GUint64Array => true
        case GTaggedUnion(cases) => |cases| < 0x1_0000_0000_0000_0000 && (forall g :: g in cases ==> ValidGrammar(g))
}

// We can't encode values that are not valid
predicate ValidVal(val:V)
{
    match val
        case VUint32(_)    => true
        case VUint64(_)    => true
        case VArray(a)     => |a| < 0x1_0000_0000_0000_0000 && forall v :: v in a ==> ValidVal(v)
        case VTuple(t)     => |t| < 0x1_0000_0000_0000_0000 && forall v :: v in t ==> ValidVal(v)
        case VByteArray(b) => |b| < 0x1_0000_0000_0000_0000
        case VUint32Array(va) => |va| < 0x1_0000_0000_0000_0000
        case VUint64Array(ua) => |ua| < 0x1_0000_0000_0000_0000
        case VCase(c, v) => ValidVal(v)

}

function {:opaque} SeqSum(t:seq<V>) : int
    ensures SeqSum(t) >= 0;
{
    if |t| == 0 then 0
    else SizeOfV(t[0]) + SeqSum(t[1..])
}

function SizeOfV(val:V) : int
    ensures SizeOfV(val) >= 0;
{
    match val
        case VUint32(_)     => 4
        case VUint64(_)     => 8
        case VArray(a)      => 8 + SeqSum(a)     // 8 bytes for length
        case VTuple(t)      => SeqSum(t)
        case VByteArray(b)  => 8 + |b|          // 8 bytes for a length field
        case VUint32Array(b)  => 8 + 4*|b|          // 8 bytes for a length field
        case VUint64Array(b)  => 8 + 8*|b|          // 8 bytes for a length field
        case VCase(c, v)  => 8 + SizeOfV(v)     // 8 bytes for the case identifier
}

function parse_Uint32(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
{
    if (|data| as uint64) >= Uint32Size() then
        (Some(VUint32(unpack_LittleEndian_Uint32(data[..Uint32Size()]))), data[Uint32Size()..])
    else
        (None, [])
}

function parse_Uint64(data:seq<byte>) : (result: (Option<V>, seq<byte>))
    requires |data| < 0x1_0000_0000_0000_0000;
  ensures result.0.Some? ==> result.0.value.VUint64?
{
    if (|data| as uint64) >= Uint64Size() then
        (Some(VUint64(unpack_LittleEndian_Uint64(data[..Uint64Size()]))), data[Uint64Size()..])
    else
        (None, [])
}

method ParseUint32(data:seq<byte>, index:uint64) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|
    ensures  var (v', rest') := parse_Uint32(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
{
    if |data| as uint64 - index >= 4 {
        var result := Unpack_LittleEndian_Uint32(data, index);
        success := true;
        v := VUint32(result);
        rest_index := index + Uint32Size();

        assert data[index..][..Uint32Size()] == data[index .. index + Uint32Size()];
    } else {
        success := false;
        rest_index := (|data| as uint64);
    }
}

method ParseUint64(data:seq<byte>, index:uint64) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|
    ensures  var (v', rest') := parse_Uint64(data[index..]);
             var v_opt := if success then Some(v) else None();
             v_opt == v' && data[rest_index..] == rest';
{
    if |data| as uint64 - index >= 8 {
        var result := Unpack_LittleEndian_Uint64(data, index);
        success := true;
        v := VUint64(result);
        rest_index := index + Uint64Size();

        assert data[index..][..Uint64Size()] == data[index .. index + Uint64Size()];
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
        assert len.value.VUint64?;
        var len64: uint64 := len.value.u;
        var (contents, remainder) := parse_Array_contents(rest, eltType, len64);
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

function parse_ByteArray(data:seq<byte>) : (res: (Option<V>, seq<byte>))
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

function parse_Uint32Array(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
{
  if |data| >= 8 then (
    var len := unpack_LittleEndian_Uint64(data[..8]) as uint64;
    if len <= (|data| as uint64 - 8) / 4 then
        (Some(VUint32Array(unpack_LittleEndian_Uint32_Seq(data[8..8 + 4*len], len as int))), data[8 + 4*len..])
    else
        (None, [])
  ) else (
    (None, [])
  )
}

method ParseUint32Array(data:seq<byte>, index: uint64) returns (success:bool, v:V, rest_index:uint64)
    requires (index as int) <= |data|;
    requires |data| < 0x1_0000_0000_0000_0000;
    ensures  (rest_index as int) <= |data|;
    ensures  var (v', rest') := parse_Uint32Array(data[index..]);
             var v_opt := if success then Some(v) else None();
             && v_opt == v'
             && data[rest_index..] == rest';
{
  if |data| as uint64 - index >= 8 {
    var len := Unpack_LittleEndian_Uint64(data, index);
    assert data[index..][..8] == data[index..index+8];
    if len <= ((|data| as uint64) - index - 8) / Uint32Size() {
      success := true;
      var contents := Unpack_LittleEndian_Uint32_Seq(data, index + Uint64Size(), len);
      v := VUint32Array(contents);
      rest_index := index + 8 + len * Uint32Size();

      assert data[index..][8..8+4*len] == data[index+8..index+8+4*len];
    } else {
      success := false;
      rest_index := (|data| as uint64);
    }
  } else {
    success := false;
    rest_index := (|data| as uint64);
  }
}

function parse_Uint64Array(data:seq<byte>) : (Option<V>, seq<byte>)
    requires |data| < 0x1_0000_0000_0000_0000;
{
  if |data| >= 8 then (
    var len := unpack_LittleEndian_Uint64(data[..8]);
    if len <= (|data| as uint64 - 8) / 8 then
        (Some(VUint64Array(unpack_LittleEndian_Uint64_Seq(data[8..8 + 8*len], len as int))), data[8 + 8*len..])
    else
        (None, [])
  ) else (
    (None, [])
  )
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
  if |data| as uint64 - index >= 8 {
    var len := Unpack_LittleEndian_Uint64(data, index);
    assert data[index..][..8] == data[index..index+8];
    if len <= ((|data| as uint64) - index - 8) / Uint64Size() {
      success := true;
      var contents := Unpack_LittleEndian_Uint64_Seq(data, index + Uint64Size(), len);
      v := VUint64Array(contents);
      rest_index := index + 8 + len * Uint64Size();

      assert data[index..][8..8+8*len] == data[index+8..index+8+8*len];
    } else {
      success := false;
      rest_index := (|data| as uint64);
    }
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
        case GUint32             => parse_Uint32(data)
        case GUint64             => parse_Uint64(data)
        case GArray(elt)         => parse_Array(data, elt)
        case GTuple(t)           => parse_Tuple(data, t)
        case GByteArray          => parse_ByteArray(data)
        case GUint32Array        => parse_Uint32Array(data)
        case GUint64Array        => parse_Uint64Array(data)
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
        case GUint32             => success, v, rest_index := ParseUint32(data, index);
        case GUint64             => success, v, rest_index := ParseUint64(data, index);
        case GArray(elt)         => success, v, rest_index := ParseArray(data, index, elt);
        case GTuple(t)           => success, v, rest_index := ParseTuple(data, index, t);
        case GByteArray          => {
          var v';
          success, v', rest_index := ParseByteArray(data, index);
          v := VByteArray(v'); 
        }
        case GUint32Array          => success, v, rest_index := ParseUint32Array(data, index);
        case GUint64Array          => success, v, rest_index := ParseUint64Array(data, index);
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
            assert data[index..index+SizeOfV(v)][..Uint64Size()]
                == data[index..bound][..Uint64Size()];
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

lemma lemma_parse_Val_view_Uint32Array(data:seq<byte>, v:V, grammar:G, index:int)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires ValInGrammar(v, grammar);
    requires ValidGrammar(grammar);
    requires grammar.GUint32Array?;
    requires 0 <= index <= |data|;
    requires 0 <= index + SizeOfV(v) <= |data|;
    ensures  forall bound :: Trigger(bound) ==> (index+SizeOfV(v) <= bound <= |data| ==>
             ((parse_Uint32Array(data[index..bound]).0 == Some(v)) <==> (parse_Uint32Array(data[index..index+SizeOfV(v)]).0 == Some(v))));
    ensures  forall bound :: index+SizeOfV(v) <= bound <= |data| ==>
             parse_Uint32Array(data[index..bound]).0 == Some(v) ==> parse_Uint32Array(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
{
  forall bound | Trigger(bound) && index+SizeOfV(v) <= bound <= |data|
  ensures (parse_Uint32Array(data[index..bound]).0 == Some(v)) ==> (parse_Uint32Array(data[index..index+SizeOfV(v)]).0 == Some(v))
  ensures (parse_Uint32Array(data[index..index+SizeOfV(v)]).0 == Some(v)) ==> (parse_Uint32Array(data[index..bound]).0 == Some(v))
    {
    var len := |v.va|;

    assert data[index..bound][..Uint64Size()]
        == data[index..index + SizeOfV(v)][..Uint64Size()];
    assert parse_Uint64(data[index..bound]).0
        == parse_Uint64(data[index..index + SizeOfV(v)]).0;
    assert parse_Uint64(data[index..bound]).1 == data[index..bound][8..];
    assert parse_Uint64(data[index..index + SizeOfV(v)]).1 == data[index..index + SizeOfV(v)][8..];
    lemma_seq_slice_slice(data, index, bound, 8, 8+4*len);
    lemma_seq_slice_slice(data, index, index + SizeOfV(v), 8, 8+4*len);
    assert data[index..bound][8..8+4*len] == data[index..index + SizeOfV(v)][8..8+4*len];

    reveal_unpack_LittleEndian_Uint64();
    if index + 8 <= |data| {
      var l := unpack_LittleEndian_Uint64(data[index..index+8]);
      if (l as int == len) {
        /*var rest0 := data[index..bound][8..];
        var rest1 := data[index..index + SizeOfV(v)][8..];
        PackedStringArray.lemma_seq_slice_suffix(data, index, bound, 8);
        PackedStringArray.lemma_seq_slice_suffix(data, index, index + SizeOfV(v), 8);
        PackedStringArray.lemma_seq_slice_slice(data, index + 8, bound, 0, 8*len);
        PackedStringArray.lemma_seq_slice_slice(data, index + 8, index + SizeOfV(v), 0, 8*len);
        assert data[index..bound][Uint64Size()..][..Uint64Size() as int * len]
            == data[index..index + SizeOfV(v)][Uint64Size()..][..Uint64Size() as int * len];
        assert parse_Uint64Array(data[index..bound]).0.Some?;
        assert parse_Uint64Array(data[index..index + SizeOfV(v)]).0.Some?;*/
        assert parse_Uint32Array(data[index..bound]).0
            == parse_Uint32Array(data[index..index + SizeOfV(v)]).0;
              }
          }
        }

  forall bound | index+SizeOfV(v) <= bound <= |data| && parse_Uint32Array(data[index..bound]).0 == Some(v)
  ensures parse_Uint32Array(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
  {
    }
}

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

    assert data[index..bound][..Uint64Size()]
        == data[index..index + SizeOfV(v)][..Uint64Size()];
    assert parse_Uint64(data[index..bound]).0
        == parse_Uint64(data[index..index + SizeOfV(v)]).0;
    assert parse_Uint64(data[index..bound]).1 == data[index..bound][8..];
    assert parse_Uint64(data[index..index + SizeOfV(v)]).1 == data[index..index + SizeOfV(v)][8..];
    lemma_seq_slice_slice(data, index, bound, 8, 8+8*len);
    lemma_seq_slice_slice(data, index, index + SizeOfV(v), 8, 8+8*len);
    assert data[index..bound][8..8+8*len] == data[index..index + SizeOfV(v)][8..8+8*len];

    reveal_unpack_LittleEndian_Uint64();
    if index + 8 <= |data| {
      var l := unpack_LittleEndian_Uint64(data[index..index+8]);
      if (l as int == len) {
        /*var rest0 := data[index..bound][8..];
        var rest1 := data[index..index + SizeOfV(v)][8..];
        PSA.lemma_seq_slice_suffix(data, index, bound, 8);
        PSA.lemma_seq_slice_suffix(data, index, index + SizeOfV(v), 8);
        PSA.lemma_seq_slice_slice(data, index + 8, bound, 0, 8*len);
        PSA.lemma_seq_slice_slice(data, index + 8, index + SizeOfV(v), 0, 8*len);
        assert data[index..bound][Uint64Size()..][..Uint64Size() as int * len]
            == data[index..index + SizeOfV(v)][Uint64Size()..][..Uint64Size() as int * len];
        assert parse_Uint64Array(data[index..bound]).0.Some?;
        assert parse_Uint64Array(data[index..index + SizeOfV(v)]).0.Some?;*/
        assert parse_Uint64Array(data[index..bound]).0
            == parse_Uint64Array(data[index..index + SizeOfV(v)]).0;
      }
    }
  }

  forall bound | index+SizeOfV(v) <= bound <= |data| && parse_Uint64Array(data[index..bound]).0 == Some(v)
  ensures parse_Uint64Array(data[index..bound]).1 == data[index+SizeOfV(v)..bound];
  {
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

    assert data[index..index+SizeOfV(v)][..Uint64Size()]
        == data[index..bound][..Uint64Size()];
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
    assert data[index..index+SizeOfV(v)][..Uint64Size()]
        == data[index..bound][..Uint64Size()];
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
            case GUint32             => {
              assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v)) by {
                assert data[index..bound][..Uint32Size()] == data[index..index+SizeOfV(v)][..Uint32Size()];
                reveal_parse_Val();
              }
            }
            case GUint64             => {
              assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v)) by {
                assert data[index..bound][..Uint64Size()] == data[index..index+SizeOfV(v)][..Uint64Size()];
                reveal_parse_Val();
              }
            }
            case GArray(elt)         => lemma_parse_Val_view_Array(data, v, grammar, index, bound);
                                        assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GTuple(t)           => lemma_parse_Val_view_Tuple(data, v, t, index, bound); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GByteArray          => lemma_parse_Val_view_ByteArray(data, v, grammar, index); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
            case GUint32Array          => lemma_parse_Val_view_Uint32Array(data, v, grammar, index); assert (parse_Val(data[index..bound], grammar).0 == Some(v)) <==> (parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v));
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

//~ lemma lemma_parse_Val_view_specific_size(data:seq<byte>, v:V, grammar:G, index:int, bound:int)
//~     requires |data| < 0x1_0000_0000_0000_0000;
//~     requires ValInGrammar(v, grammar);
//~     requires ValidGrammar(grammar);
//~     requires 0 <= index <= |data|;
//~     requires 0 <= index + SizeOfV(v) <= |data|;
//~     requires index+SizeOfV(v) <= bound <= |data|; 
//~     requires parse_Val(data[index..bound], grammar).0 == Some(v)
//~     decreases grammar, 0;
//~     ensures  parse_Val(data[index..index+SizeOfV(v)], grammar).0 == Some(v);
//~     ensures  parse_Val(data[index..bound], grammar).1 == data[index+SizeOfV(v)..bound];
//~ {
//~     lemma_parse_Val_view(data, v, grammar, index);
//~ }

method ComputeSeqSum(s:seq<V>) returns (size:uint64)
    requires |s| < 0x1_0000_0000_0000_0000;
    requires 0 <= SeqSum(s) < 0x1_0000_0000_0000_0000;
    requires forall v :: v in s ==> ValidVal(v);
    ensures (size as int) == SeqSum(s);
{
  assert SeqSum([]) == 0 by { reveal_SeqSum(); }

  var i: uint64 := 0;
  var res: uint64 := 0;
  while i < |s| as uint64
  invariant 0 <= i as int <= |s|
  invariant res as int == SeqSum(s[..i])
  {
    calc {
      SeqSum(s[..i+1]);
      { assert s[..i+1] == s[..i] + [s[i]]; }
      SeqSum(s[..i] + [s[i]]);
      { lemma_SeqSum_prefix(s[..i], s[i]); }
      SeqSum(s[..i]) + SizeOfV(s[i]);
    }

    lemma_SeqSum_bound(s, 0x1_0000_0000_0000_0000);
    lemma_SeqSum_bound_prefix(s, s[..i+1], (i+1) as int);

    var v_size := ComputeSizeOf(s[i]);
    res := res + v_size;
    i := i + 1;
  }
  assert s[..|s|] == s;
  return res;
}

method ComputeSizeOf(val:V) returns (size:uint64)
    requires 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000;
    requires ValidVal(val);
    ensures (size as int) == SizeOfV(val);
{
  match val {
    case VUint32(_)     => size := 4;
    case VUint64(_)     => size := 8;
    case VArray(a)      => var v := ComputeSeqSum(a);
                           if v == 0 {
                               size := 8;
                           } else {
                               size := 8 + v;
                           }
    case VTuple(t)      => size := ComputeSeqSum(t);
    case VByteArray(b)  => size := 8 + (|b| as uint64);
    case VUint32Array(b)  => size := 8 + 4*(|b| as uint64);
    case VUint64Array(b)  => size := 8 + 8*(|b| as uint64);
    case VCase(c, v)    => var vs := ComputeSizeOf(v);
                           size := 8 + vs;
  }
}

//~ lemma seq_ext(a: seq<byte>, b: seq<byte>)
//~ requires |a| == |b|
//~ requires forall i | 0 <= i < |a| :: a[i] == b[i]
//~ ensures a == b
//~ {
//~ }

//~ lemma MarshallUint64_index_splicing(data: array<byte>, index: uint64, val: V, i: int)
//~ requires 0 <= i
//~ requires 0 <= index
//~ requires 8 + (i+1)*8 <= SizeOfV(val)
//~ requires (index as int) + SizeOfV(val) <= data.Length
//~ ensures data[index..(index as int) + SizeOfV(val)][8 + i*8 .. 8 + (i+1)*8]
//~      == data[index as int + 8 + i*8 .. index as int + 8 + (i+1)*8];
//~ {
//~   // I had to go through enormous trouble to prove this for some reason
//~ 
//~   var ar := data[..];
//~   var a := index as int;
//~   var b := SizeOfV(val);
//~   var c := 8 + i*8;
//~   var d := 8;
//~ 
//~   var x1 := ar[a .. a + b][c .. c + d];
//~   var x2 := ar[a + c .. a + c + d];
//~   forall i | 0 <= i < |x1|
//~   ensures x1[i] == x2[i]
//~   {
//~     assert x1[i]
//~         == ar[a .. a + b][c .. c + d][i]
//~         == ar[a .. a + b][c + i]
//~         == ar[a + c + i]
//~         == ar[a + c .. a + c + d][i]
//~         == x2[i];
//~   }
//~   assert |x1| == |x2|;
//~   seq_ext(x1, x2);
//~ 
//~   assert ar[a .. a + b][c .. c + d]
//~       == ar[a + c .. a + c + d];
//~   assert ar[index..(index as int) + SizeOfV(val)][8 + i*8 .. 8 + (i+1)*8]
//~      == ar[index as int + 8 + i*8 .. index as int + 8 + (i+1)*8];
//~ }

method MarshallUint32(n:uint32, data:array<byte>, index:uint64)
    requires (index as int) + (Uint32Size() as int) <= data.Length;
    requires 0 <= (index as int) + (Uint32Size() as int) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  unpack_LittleEndian_Uint32(data[index..index+(Uint32Size() as uint64)]) == n;
    ensures  !parse_Uint32(data[index .. index+(Uint32Size() as uint64)]).0.None?;
    ensures  !parse_Uint32(data[index .. ]).0.None?;
    ensures  var tuple := parse_Uint32(data[index .. index+(Uint32Size() as uint64)]);
             tuple.0.value.v == n && tuple.1 == [];
    ensures  var tuple := parse_Uint32(data[index .. ]);
             tuple.0.value.v == n && tuple.1 == data[index+(Uint32Size() as uint64)..];
    ensures  data[0..index] == old(data[0..index]);
    ensures  data[index+(Uint32Size() as uint64)..] == old(data[index+(Uint32Size() as uint64)..]);
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) + (Uint32Size() as int) <= i < data.Length ==> data[i] == old(data[i]);
{
    Pack_LittleEndian_Uint32_into_Array(n, data, index);

    forall i | 0 <= i < index ensures data[i] == old(data[i])
    {
      assert data[i] == data[..index][i] == old(data[..index])[i] == old(data[i]);
    }

    assert |data[index .. index+(Uint32Size() as uint64)]| == 4;

    reveal_unpack_LittleEndian_Uint32();
}

method MarshallUint64(n:uint64, data:array<byte>, index:uint64)
    requires (index as int) + (Uint64Size() as int) <= data.Length;
    requires 0 <= (index as int) + (Uint64Size() as int) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  unpack_LittleEndian_Uint64(data[index..index+(Uint64Size() as uint64)]) == n;
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
    Pack_LittleEndian_Uint64_into_Array(n, data, index);

    forall i | 0 <= i < index ensures data[i] == old(data[i])
    {
      assert data[i] == data[..index][i] == old(data[..index])[i] == old(data[i]);
    }

    assert |data[index .. index+(Uint64Size() as uint64)]| == 8;

    reveal_unpack_LittleEndian_Uint64();
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
    reveal_unpack_LittleEndian_Uint64();
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
    assert len.value.u as int == |val.a|;
    assert contents.value == val.a;
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

method MarshallBytes(bytes:seq<byte>, data:array<byte>, index:uint64)
    requires (index as int) + |bytes| <= data.Length;
    requires 0 <= (index as int) + |bytes| < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow below
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  forall i :: 0 <= i < index ==> data[i] == old(data[i]);
    ensures  forall i :: (index as int) <= i < (index as int) + |bytes| ==> data[i] == bytes[i - (index as int)];
    ensures  forall i :: (index as int) + |bytes| <= i < data.Length ==> data[i] == old(data[i]);
{
    NativeArrays.CopySeqIntoArray(bytes, 0, data, index, (|bytes| as uint64));

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
    reveal_unpack_LittleEndian_Uint64();
    MarshallUint64((|b| as uint64), data, index);
    assert unpack_LittleEndian_Uint64(data[index..index+(Uint64Size() as uint64)]) == (|b| as uint64);
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
    //assert{:split_here} true;
    assert data_seq[..8] == data[index .. index + 8];
    
    assert rest == data[index + 8..(index as int) + SizeOfV(VByteArray(b))] == b;
    assert !len.None? && (len.value.u as int) <= |rest|;
    assert rest[0..len.value.u] == b;       // OBSERVE
    size := 8 + (|b| as uint64);
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
    reveal_unpack_LittleEndian_Uint64();
    MarshallUint64((|val.b| as uint64), data, index);
    assert unpack_LittleEndian_Uint64(data[index..index+(Uint64Size() as uint64)]) == (|val.b| as uint64);
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
    //assert{:split_here} true;
    //assert len.value.u == (|val.b| as uint64);
    
    assert rest == data[index + 8..(index as int) + SizeOfV(val)] == val.b;
    assert !len.None? && (len.value.u as int) <= |rest|;
    assert rest[0..len.value.u] == val.b;       // OBSERVE
    size := 8 + (|val.b| as uint64);
}

method MarshallUint32Array(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VUint32Array?;
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
  reveal_unpack_LittleEndian_Uint64();
  reveal_parse_Val();

  ghost var data_seq0 := data[index..(index as int) + SizeOfV(val)];

  MarshallUint64((|val.va| as uint64), data, index);

  ghost var data_seq1 := data[index..(index as int) + SizeOfV(val)];
  assert unpack_LittleEndian_Uint64(data_seq1[..8]) as int == |val.va|;

  Pack_LittleEndian_Uint32_Seq_into_Array(val.va, data, index + 8);

  ghost var data_seq2 := data[index..(index as int) + SizeOfV(val)];
  //assert unpack_LittleEndian_Uint64(data_seq2[..8]) as int == |val.va|;
  lemma_array_slice_slice(data, index as int, (index as int) + SizeOfV(val), 8, 8 + 4*|val.va|);
  assert unpack_LittleEndian_Uint32_Seq(
      data_seq2[8..8 + 4*|val.va|], |val.va|) == val.va;

  ghost var len := unpack_LittleEndian_Uint64(data_seq2[..8]);
  assert |data_seq2| >= 8;
  //assert len <= (|data_seq2| as uint64 - 8) / 4;
  assert parse_Uint32Array(data_seq2).0.Some?;
  assert parse_Val(data_seq2, grammar).0.Some?;
  assert parse_Uint32Array(data_seq2).0.value.va == val.va;
  assert parse_Val(data_seq2, grammar).0.value.va == val.va;

  size := 8 + |val.va| as uint64 * 4;
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
  reveal_unpack_LittleEndian_Uint64();
  reveal_parse_Val();

  ghost var data_seq0 := data[index..(index as int) + SizeOfV(val)];

  MarshallUint64((|val.ua| as uint64), data, index);

  ghost var data_seq1 := data[index..(index as int) + SizeOfV(val)];
  assert unpack_LittleEndian_Uint64(data_seq1[..8]) as int == |val.ua|;

  Pack_LittleEndian_Uint64_Seq_into_Array(val.ua, data, index + 8);

  ghost var data_seq2 := data[index..(index as int) + SizeOfV(val)];
  //assert unpack_LittleEndian_Uint64(data_seq2[..8]) as int == |val.ua|;
  lemma_array_slice_slice(data, index as int, (index as int) + SizeOfV(val), 8, 8 + 8*|val.ua|);
  assert unpack_LittleEndian_Uint64_Seq(
      data_seq2[8..8 + 8*|val.ua|], |val.ua|) == val.ua;

  ghost var len := unpack_LittleEndian_Uint64(data_seq2[..8]);
  assert |data_seq2| >= 8;
  //assert len <= (|data_seq2| as uint64 - 8) / 8;
  //assert parse_Uint64Array(data_seq2).0.Some?;
  assert parse_Val(data_seq2, grammar).0.Some?;
  //assert parse_Uint64Array(data_seq2).0.value.ua == val.ua;
  //assert parse_Val(data_seq2, grammar).0.value.ua == val.ua;

  size := 8 + |val.ua| as uint64 * 8;
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

    ghost var data_seq := data[..];
    ghost var new_int_bytes := data_seq[index..index+Uint64Size()];
    assert forall i {:auto_trigger} :: 0 <= i < Uint64Size() ==> int_bytes[i] == new_int_bytes[i];
    assert int_bytes == new_int_bytes;

    assert val.VCase?; 
    assert grammar.GTaggedUnion?; 
    assert (val.c as int) < |grammar.cases|;

    ghost var bytes := data_seq[index..(index as int) + SizeOfV(val)];
    lemma_seq_slice_slice(data_seq, index as int, index as int + SizeOfV(val), 0, 8);
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

method MarshallVUint32(val:V, ghost grammar:G, data:array<byte>, index:uint64) returns (size:uint64)
    requires val.VUint32?;
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
    MarshallUint32(val.v, data, index);
    calc {
        parse_Val(data[index..(index as int) + SizeOfV(val)], grammar);
            { reveal_parse_Val(); }
        parse_Uint32(data[index..(index as int) + SizeOfV(val)]);
    }
    return 4;
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
        case VUint32(_)    => size := MarshallVUint32(val, grammar, data, index);
        case VUint64(_)    => size := MarshallVUint64(val, grammar, data, index);
        case VArray(_)     => size := MarshallArray(val, grammar, data, index);
        case VTuple(_)     => size := MarshallTuple(val, grammar, data, index);
        case VUint32Array(_) => size := MarshallUint32Array(val, grammar, data, index);
        case VUint64Array(_) => size := MarshallUint64Array(val, grammar, data, index);
        case VByteArray(_) => size := MarshallByteArray(val, grammar, data, index);
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

lemma lemma_SizeOfV_parse_Val_Uint64(data: seq<byte>)
requires |data| < 0x1_0000_0000_0000_0000;
ensures var (v, rest) := parse_Uint64(data);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
}

lemma lemma_SizeOfV_parse_Val_Uint32(data: seq<byte>)
requires |data| < 0x1_0000_0000_0000_0000;
ensures var (v, rest) := parse_Uint32(data);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
}

lemma lemma_SizeOfV_parse_Val_Array_contents(data: seq<byte>, eltType: G, len: uint64)
requires |data| < 0x1_0000_0000_0000_0000;
requires ValidGrammar(eltType);
decreases eltType, 1, len;
ensures var (v, rest) := parse_Array_contents(data, eltType, len);
  v.Some? ==> SeqSum(v.value) + |rest| == |data|
{
  reveal_parse_Array_contents();
  reveal_SeqSum();
  if len == 0 {
  } else {
    lemma_SizeOfV_parse_Val(data, eltType);
    var (val, rest1) := parse_Val(data, eltType);
    lemma_SizeOfV_parse_Val_Array_contents(rest1, eltType, len - 1);
  }
}

lemma lemma_SizeOfV_parse_Val_Array(data: seq<byte>, eltType: G)
requires |data| < 0x1_0000_0000_0000_0000;
requires ValidGrammar(eltType)
decreases eltType;
ensures var (v, rest) := parse_Array(data, eltType);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
  lemma_SizeOfV_parse_Val_Uint64(data);
  var (len, rest) := parse_Uint64(data);
  if !len.None? {
    lemma_SizeOfV_parse_Val_Array_contents(rest, eltType, len.value.u);
  }
}

lemma lemma_SizeOfV_parse_Val_Tuple_contents(data: seq<byte>, eltTypes: seq<G>)
requires |data| < 0x1_0000_0000_0000_0000;
requires |eltTypes| < 0x1_0000_0000_0000_0000;
requires forall elt | elt in eltTypes :: ValidGrammar(elt);
decreases eltTypes, 0
ensures var (v, rest) := parse_Tuple_contents(data, eltTypes);
  v.Some? ==> SeqSum(v.value) + |rest| == |data|
{
  reveal_parse_Tuple_contents();
  reveal_SeqSum();
  if eltTypes == [] {
  } else {
    lemma_SizeOfV_parse_Val(data, eltTypes[0]);
    var (val, rest1) := parse_Val(data, eltTypes[0]);
    lemma_SizeOfV_parse_Val_Tuple_contents(rest1, eltTypes[1..]);
  }
}

lemma lemma_SizeOfV_parse_Val_Tuple(data: seq<byte>, eltTypes: seq<G>)
requires |data| < 0x1_0000_0000_0000_0000;
requires |eltTypes| < 0x1_0000_0000_0000_0000;
requires forall elt | elt in eltTypes :: ValidGrammar(elt);
decreases eltTypes, 1;
ensures var (v, rest) := parse_Tuple(data, eltTypes);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
  lemma_SizeOfV_parse_Val_Tuple_contents(data, eltTypes);
}

lemma lemma_SizeOfV_parse_Val_Case(data: seq<byte>, cases: seq<G>)
requires |data| < 0x1_0000_0000_0000_0000;
requires |cases| < 0x1_0000_0000_0000_0000;
requires forall elt :: elt in cases ==> ValidGrammar(elt);
decreases cases;
ensures var (v, rest) := parse_Case(data, cases);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
  lemma_SizeOfV_parse_Val_Uint64(data);
  var (caseID, rest1) := parse_Uint64(data);
  if !caseID.None? && caseID.value.u < (|cases| as uint64) {
    lemma_SizeOfV_parse_Val(rest1, cases[caseID.value.u]);
    var (val, rest2) := parse_Val(rest1, cases[caseID.value.u]);
    if !val.None? {
      assert |data| - |rest1| == 8;
      assert |rest1| - |rest2| == SizeOfV(val.value);
    }
  }
}

lemma lemma_SizeOfV_parse_Val_ByteArray(data: seq<byte>)
requires |data| < 0x1_0000_0000_0000_0000;
ensures var (v, rest) := parse_ByteArray(data);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
}

lemma lemma_SizeOfV_parse_Val_Uint32Array(data: seq<byte>)
requires |data| < 0x1_0000_0000_0000_0000;
ensures var (v, rest) := parse_Uint32Array(data);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
}

lemma lemma_SizeOfV_parse_Val_Uint64Array(data: seq<byte>)
requires |data| < 0x1_0000_0000_0000_0000;
ensures var (v, rest) := parse_Uint64Array(data);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
}

lemma lemma_SizeOfV_parse_Val(data: seq<byte>, grammar: G)
requires |data| < 0x1_0000_0000_0000_0000;
requires ValidGrammar(grammar);
decreases grammar, 0
ensures var (v, rest) := parse_Val(data, grammar);
  v.Some? ==> SizeOfV(v.value) + |rest| == |data|
{
  reveal_parse_Val();
  match grammar {
    case GUint32             => lemma_SizeOfV_parse_Val_Uint32(data);
    case GUint64             => lemma_SizeOfV_parse_Val_Uint64(data);
    case GArray(elt)         => lemma_SizeOfV_parse_Val_Array(data, elt);
    case GTuple(t)           => lemma_SizeOfV_parse_Val_Tuple(data, t);
    case GByteArray          => lemma_SizeOfV_parse_Val_ByteArray(data);
    case GUint32Array        => lemma_SizeOfV_parse_Val_Uint32Array(data);
    case GUint64Array        => lemma_SizeOfV_parse_Val_Uint64Array(data);
    case GTaggedUnion(cases) => lemma_SizeOfV_parse_Val_Case(data, cases);
  }
}

} 
