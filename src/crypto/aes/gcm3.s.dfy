include "aes.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../loopunroll/regions128.dfy" // TODO where should this really go?

// Derived from NIST Special Publication 800-38D
// http://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf

module GCMModule {

import opened x64_def_s
import opened AESModule
import opened x64_vale_i
import opened regions128


// 6.2 
// This is specified big endian, thank gosh.
function inc32(iv96ctr32 : Quadword) : Quadword
{
  reveal_BitwiseAdd32();
  iv96ctr32.(lo := BitwiseAdd32(iv96ctr32.lo,1))
}

// 6.3 block multiply 
function QuadwordShr(w : Quadword, n : nat) : Quadword
{
  w // TODO
}

function LEBit(w : Quadword, i : nat) : bool 
  requires i < 128;
{
  true // TODO
}

// The specification uses a while loop but we'd like a functional specification
// and can only put while's in functions in dafny.
// The reduction polynomial is 0xE100_0000_0000_0000. Note our quadwords constructor 
// is in lo uint32 to highest uint32 argument order.
// This is called bit-reflection, it is not byte endianness, see
// "Intel® Carry-Less Multiplication Instruction and its Usage for Computing the GCM Mode".

function BlockMul1'(i : nat, Z : Quadword, V : Quadword) : Quadword
  requires 0 <= i <= 128;
  decreases 128 - i;
{
  if (i == 128) then 
    Z 
  else 
    BlockMul1'(i+1, 
      if (LEBit(Z,i)) then QuadwordXor(Z,V) else Z,
      if (LEBit(V,0)) then QuadwordXor(QuadwordShr(V,1), Quadword(1, 0, 0, 0xE100_0000))
                      else QuadwordShr(V,1)) 
}

function BlockMul1(X : Quadword, Y : Quadword) : Quadword
{
  var Z_0 := Quadword(0,0,0,0);
  var V_0 := Y;
  BlockMul1'(0,Z_0,V_0)
}

function GHASH(H:Quadword, X:seq<Quadword>) : Quadword
    requires |X| > 0;
{
    if (|X| == 1) then 
        var Y_0 := Quadword(0, 0, 0, 0);
         BlockMul1(QuadwordXor(Y_0, X[0]), H)
    else 
        var Y_i_minus_1 := GHASH(H, all_but_last(X));
         BlockMul1(QuadwordXor(Y_i_minus_1, last(X)), H)
}

// 6.5 GCTR 
function CB(i : nat, ICB : Quadword) : Quadword
{
    if i == 0 then 
      Quadword(1, ICB.mid_lo, ICB.mid_hi, ICB.hi)
    else inc32(CB(i-1, ICB))
}

predicate KeyReq(key : seq<uint32>) {
  |key| == Nk(AES_128) && 
  (Nb() * (Nr(AES_128) + 1)) / 4 == Nr(AES_128) + 1 &&
  (Nb() * (Nr(AES_128) + 1)) % 4 == 0
}

// Algorithm 3 

// This version is easier to prove but a bit farther from the spec.
// With an index and a head list recursion, as this looks more like the spec. 
function AES_GCTR(n : nat, key : seq<uint32>, ICB : Quadword, X : seq<Quadword>) : seq<Quadword>
    decreases |X|;
    requires  0 <= n + |X| < 0x1_0000_0000 - 1;
    requires KeyReq(key);
    ensures  |AES_GCTR(n, key, ICB, X)| == |X|;
    ensures forall i : nat :: i < |X| ==> 
      AES_GCTR(n, key, ICB, X)[i] == QuadwordXor(X[i], AES_Encrypt(key, CB(n + i, ICB), AES_128));
{
  if |X| == 0 then
    []
   else 
    [QuadwordXor(X[0], AES_Encrypt(key, CB(n, ICB), AES_128))] + 
    AES_GCTR(n + 1, key, ICB, all_but_first(X))
}

// Use a ghost var of G, for ghosts, to cut the size of the code.
datatype GCMSpec = GCMSpecCon(
               ghost alg: Algorithm,
// The key is purely ghostly.
               ghost key      : seq<uint32>,
// The expanded key is here of fixed size. 
               ghost exp_key_addr : uint64,
               ghost exp_key      : seq<uint32>,
               ghost exp_key_heap : heaplet_id,
// The input is here of this size in this heap.
               ghost iaddr : uint64,
               ghost iendaddr : uint64,
               ghost iheap : heaplet_id,
               ghost isize : nat, 
// The output is here of this size in this heap.
               ghost oaddr : uint64,
               ghost osize : nat,
               ghost oheap : heaplet_id,
// The input counter block (ICB) is in the high 92 bits of ivaddr, 
// ivsize is 16 bytes.
               ghost ICB     : Quadword,
               ghost ivaddr  : uint64,
               ghost ivsize  : nat,
               ghost ivheap  : heaplet_id
               )

// AESGCTR is in the style of CopyNSeq proofs, see regions64.vad writeup.
// It's mapping its input memory directly into the desired output Quadword sequence.

function AESGCTR(mem : Heaplets, g : GCMSpec, i : nat) : Quadword
 requires ValidDstReg128(mem, g.iheap, g.iaddr, g.isize);
 requires 0 <= i < g.isize;
 requires |g.key| == Nk(AES_128);

{
  QuadwordXor(mem[g.iheap].quads[(addr128(g.iaddr, i))].v, AES_Encrypt(g.key, CB(i, g.ICB), AES_128))
}

// Generate the whole sequence with this function that knows what the values are to
// obviate any subsequence proof problems.

function AESGCTRSeq(mem : Heaplets, g : GCMSpec, count : nat) : seq<Quadword>
 requires ValidDstReg128(mem, g.iheap, g.iaddr, g.isize);
 requires |g.key| == Nk(AES_128);
 requires 0 <= count <= g.isize;
 ensures  |AESGCTRSeq(mem, g, count)| == count;
 // Doing this here at the function definition is CRITICAL as it proves and then is available
 // when you need it in specifications.
 ensures forall i : nat :: 0 <= i < count ==> AESGCTRSeq(mem, g, count)[i] == AESGCTR(mem, g, i);
{
  if (count == 0) then
    []
  else 
   AESGCTRSeq(mem, g, count - 1) + [AESGCTR(mem, g, count - 1)]
}

// Algorithm 4 
//
// From 8.3 
// The  total  number  of  invocations  of  the  authenticated  encryption function shall  not  exceed  
// 2^32, including all IV lengths and all instances of the authenticated encryption function with 
// the given key. 
// The lengths are 64 bit numbers of bits in A and C, GHASH of these do not need padding as we
// are taking only 128 bit inputs.
//
// This is currently fixed to an IV of 96 bits in the high bits of the IV.

//The bit lengths of the input strings to the authenticated encryption
//function shall meet the following requirements:
//
//• len(P) ≤ 2^39-256; 
//• len(A) ≤ 2^64-1; 
//• 1 ≤ len(IV) ≤ 2^64-1. 
//
//Although GCM is defined on bit strings, the bit lengths of the
//plaintext, the AAD, and the IV shall all be multiples of 8, so that
//these values are byte strings

predicate LenReq(PorC : seq<Quadword>, A : seq<Quadword>, IV : Quadword) {
  (|PorC| * 128 <  0x8_000_000_000 - 256) &&  
  (|A|    * 128 < 0x1_0000_0000_0000_0000 - 1)
}

function AES_GCTR_AE(key : seq<uint32>, IV : Quadword, P : seq<Quadword>, A : seq<Quadword>)  :
  (seq<Quadword>, Quadword)
    requires KeyReq(key);
    requires 0 <= |P| < 0x1_0000_0000 - 1;
    requires KeyReq(key);
    requires LenReq(P,A,IV);
    ensures  |AES_GCTR_AE(key, IV, P, A).0| == |P|;
{
    var H := AES_Encrypt(key, Quadword(0, 0, 0, 0), AES_128);
    var J_0 := IV.(lo := 1);        // Consider the top 96 bits of the IV quadword to be the "real" IV
    var C := AES_GCTR(0, key, inc32(J_0), P);
    var C128 := |C| * 128;
    var A128 := |A| * 128;
    var lengths := Quadword(lower64(C128), upper64(C128), lower64(A128), upper64(A128));
    var S := GHASH(H, A + C + [lengths]);
    var T := AES_GCTR(0, key, J_0, [S])[0];
    (C, T)
}

// Algorithm 5

function AES_GCTR_AD(key : seq<uint32>, IV : Quadword, C : seq<Quadword>, A : seq<Quadword>, T: Quadword) : (seq<Quadword>, bool)
    requires KeyReq(key);
    requires 0 <= |C| < 0x1_0000_0000 - 1;
    requires KeyReq(key);
    requires LenReq(C,A,IV);
    ensures |AES_GCTR_AD(key, IV, C, A, T).0| == |C|;
{
    var H := AES_Encrypt(key, Quadword(0, 0, 0, 0), AES_128);
    var J_0 := IV.(lo := 1);        // Consider the top 96 bits of the IV quadword to be the "real" IV
    var P := AES_GCTR(0, key, inc32(J_0), C);
    var C128 := |C| * 128;
    var A128 := |A| * 128;
    var lengths := Quadword(lower64(C128), upper64(C128), lower64(A128), upper64(A128));
    var S := GHASH(H, A + C + [lengths]);
    var T' := AES_GCTR(0, key, J_0, [S])[0];
    (P, T == T')
}

}
