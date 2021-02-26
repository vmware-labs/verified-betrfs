include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/LinearSequence.i.dfy"

import opened NativeTypes
import opened LinearSequence_s
import opened LinearSequence_i

function interp_word(bs:seq<byte>) : (v:uint32)
    requires |bs| == 4

function as_word(bs:seq<byte>, offset:nat) : (v:uint32)
    requires 0 <= offset <= |bs|-4
    ensures v == interp_word(bs[offset..offset+4])

method extract_word(shared bs:seq<byte>, offset:nat) returns (v:uint32)
    requires 0 <= offset <= |bs|-4
    ensures v == as_word(bs, offset)

method replace_word(linear inout bs:seq<byte>, offset:nat, v:uint32) returns ()
    requires 0 <= offset <= |old_bs|-4
    ensures |bs| == |old_bs|
    ensures forall i | 0<=i<offset || offset+4<=i<|old_bs| :: bs[i]==old_bs[i]
    ensures as_word(bs, offset) == v;

method entire_file() returns (linear v:seq<byte>)
    ensures |v|>=8192;

method read_page(shared v1: seq<byte>, page:nat) returns (linear v2:seq<byte>)
    requires |v1|>=(page+1)*4096;
    ensures v2[..] == v1[page*4096..(page+1)*4096];

method discard<T>(linear v:T) returns ()

method main() {
    linear var orig_raw_data:seq<byte> := entire_file();
    linear var offset_raw_data:seq<byte> := read_page(orig_raw_data, 1);
    var orig_word:uint32 := extract_word(orig_raw_data, 4100);
    var offset_word:uint32 := extract_word(offset_raw_data, 4);
    calc {
        orig_raw_data[..][4100..4104];
        {   // having some extensionality troubles.
            var x:= orig_raw_data[..];
//            assert 4100==4096+4;
//            assert 4104==4096+8;
//            assert |x[4100..4104]| == 4 == |x[4096..8192][4..8]|;
            assert forall i | 0<=i<4 ::
                x[4100..4104][i] == x[4096..8192][4..8][i];
            assert x[4100..4104] == x[4096..8192][4..8];
        }
        orig_raw_data[..][4096..8192][4..8];
        offset_raw_data[..][4..8];
    }
    calc {
        orig_word;
        as_word(orig_raw_data[..], 4100);
        as_word(offset_raw_data[..], 4);
        offset_word;
    }
    var new_word:uint32;
    assert as_word(orig_raw_data, 4100) == orig_word;
    ghost var snap := orig_raw_data[..];
    assert snap[4100..4104] == orig_raw_data[4100..4104];
    replace_word(inout orig_raw_data, 4104, new_word);
    assert snap[4100..4104] == orig_raw_data[4100..4104];
    assert as_word(orig_raw_data, 4100) == orig_word;
    assert as_word(orig_raw_data, 4104) == new_word;
    discard(orig_raw_data);
    discard(offset_raw_data);
}

/*
FastMarshalling.i.dfy(30,0): Error: linear variable offset_raw_data must be unavailable at end of block
FastMarshalling.i.dfy(30,0): Error: linear variable _v0 must be unavailable at end of block
*/
