include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

module seqcomp {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i

function{:opaque} seq0() : seq<uint32>
    ensures (var x := seq0(); |x| == 0)
{
    []
}

function{:opaque} seq1(a:uint32) : seq<uint32>
    ensures (var x := seq1(a); |x| == 1 && x[0] == a)
{
    [a]
}

function{:opaque} seq2(a:uint32, b:uint32)  : seq<uint32>
    ensures (var x := seq2(a, b); |x| == 2 && x[0] == a && x[1] == b)
{
    [a, b]
}

function{:opaque} seq3(a:uint32, b:uint32, c:uint32)  : seq<uint32>
    ensures (var x := seq3(a, b, c); |x| == 3 && x[0] == a && x[1] == b && x[2] == c)
{
    [a, b, c]
}

function{:opaque} seq4(a:uint32, b:uint32, c:uint32, d:uint32) : seq<uint32>
    ensures (var x := seq4(a, b, c, d); |x| == 4 && x[0] == a && x[1] == b && x[2] == c && x[3] == d)
{
    [a, b, c, d]
}

function{:opaque} seq5(a:uint32, b:uint32, c:uint32, d:uint32, e:uint32) : seq<uint32>
    ensures (var x := seq5(a, b, c, d, e); |x| == 5 && x[0] == a && x[1] == b && x[2] == c && x[3] == d && x[4] == e)
{
    [a, b, c, d, e]
}


function{:opaque} seq6(a:uint32, b:uint32, c:uint32, d:uint32, e:uint32, f:uint32) : seq<uint32>
    ensures (var x := seq6(a, b, c, d, e, f); |x| == 6 && x[0] == a && x[1] == b && x[2] == c && x[3] == d && x[4] == e && x[5] == f)
{
    [a, b, c, d, e, f]
}

function{:opaque} seq7(a:uint32, b:uint32, c:uint32, d:uint32, e:uint32, f:uint32, g:uint32) : seq<uint32>
    ensures (var x := seq7(a, b, c, d, e, f, g); |x| == 7 && x[0] == a && x[1] == b && x[2] == c && x[3] == d && x[4] == e && x[5] == f && x[6] == g)
{
    [a, b, c, d, e, f, g]
}


function{:opaque} seq8(a:uint32, b:uint32, c:uint32, d:uint32, e:uint32, f:uint32, g:uint32, h:uint32):seq<uint32>
    ensures (var x := seq8(a, b, c, d, e, f, g, h); |x| == 8 && x[0] == a && x[1] == b && x[2] == c && x[3] == d && x[4] == e && x[5] == f && x[6] == g && x[7] == h)
{
    [a, b, c, d, e, f, g, h]
}

}
