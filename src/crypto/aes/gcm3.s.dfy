include "aes.s.dfy"
include "../../arch/x64/def.s.dfy"

// Derived from NIST Special Publication 800-38D
// http://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf

module GCM {

import opened x64_def_s
import opened AESModule

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
  w
}

function LEBit(w : Quadword, i : nat) : bool 
  requires i < 128;
{
  true
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
// We count by 0 here instead of by 1 in the spec.

function CB(i : nat, ICB : Quadword) : Quadword
{
    if i == 0 then ICB else inc32(CB(i-1, ICB))
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
{
  if |X| == 0 then
    []
   else 
    [QuadwordXor(X[0], AES_Encrypt(key, CB(n, ICB), AES_128))] + 
    AES_GCTR(n + 1, key, ICB, all_but_first(X))
}

lemma lemma_AES_GCTR_empty_X_is(n : nat, key : seq<uint32>, ICB : Quadword, X : seq<Quadword>) 
    requires  |X| == 0;
    requires  0 <= n + |X| < 0x1_0000_0000 - 1;
    requires KeyReq(key);
    ensures |AES_GCTR(n, key, ICB, X)| == |X|;
    ensures AES_GCTR(n, key, ICB, X) == [];
{
}

lemma {:timeLimitMultiplier 6} lemma_AES_GCTR_n_is(n : nat, key : seq<uint32>, ICB : Quadword, X : seq<Quadword>)
    requires  0 <= n + |X| < 0x1_0000_0000 - 1;
    requires KeyReq(key);
    ensures |AES_GCTR(n, key, ICB, X)| == |X|;
    ensures forall i : nat :: i < |X| ==> 
      AES_GCTR(n, key, ICB, X)[i] == QuadwordXor(X[i], AES_Encrypt(key, CB(n + i, ICB), AES_128));
    decreases |X|;
{
  if (|X| == 0) {
    lemma_AES_GCTR_empty_X_is(n, key, ICB, X);
  } else if |X| == 1 {
     assert AES_GCTR(n, key, ICB, X)[0] == QuadwordXor(X[0], AES_Encrypt(key, CB(n + 0, ICB), AES_128));
  } else {
    lemma_AES_GCTR_n_is(n + 1, key, ICB, all_but_first(X));
  }
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
//plaintext, the AAD, and the IV shall all be multiples of 8, so th at
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
