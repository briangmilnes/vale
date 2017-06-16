include "aes.s.dfy"

// Derived from NIST Special Publication 800-38D
// http://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf

module GCM {

import opened AESModule

// 6.2 
// This is specified big endian, thank gosh.
function inc32(iv96ctr32 : Quadword) : Quadword
{
  reveal_BitwiseAdd32();
  iv96ctr32.(lo := BitwiseAdd32(iv96ctr32.lo,1));
}

// 6.3 block multiply 

function {:axiom} QuadwordShr(w : Quadword) : Quadword;
function {:axiom} LEBit(w : Quadword) : bool;

var R := Quadword(0b11100001000000000000000000000000, 0, 0, 0);

function BlockMul(X : Quadword, Y : Quadword) {
  var Z := Quadword(0,0,0,0);
  var V := Y;
  var i = 0;
  while (i < 128) {
    if (LEBit(X,i)) {
      Z := QuadwordXor(Z,V);
    } else {
      Z := Z;
    };
    if (LEBit(V,0)) {
      V := QuadwordXor(QuadwordShr(V,1), R);
    } else {
      V := QuadwordShr(V,1);
    }
  }
  return Z;
}

function GHASH(H:Quadword, X:seq<Quadword>) : Quadword
    requires |X| > 0;
{
    if |X| == 1 then
        var Y_0 := Quadword(0, 0, 0, 0);
        BlockMul(QuadwordXor(Y_0, X[0]), H)
    else
        var Y_i_minus_1 := GHASH(H, all_but_last(X));
        BlockMul(QuadwordXor(Y_i_minus_1, last(X)), H)
}

// 6.5 GCTR 
// We count by 0 here instead of by 1 in the spec.

function CB(i : nat, ICB : Quadword) : Quadword
{
    if i = 0 then ICB else inc32(CB(i-1, ICB))
}

function ctr_n(ICB : Quadword, n : uint32) : Quadword 
{
  reveal_BitwiseAdd32();
  Quadword(BitwiseAdd32(ICB.lo, n),
          ICB.mid_lo,
          ICB.mid_hi,
          ICB.hi);
}

lemma CB_ctr_n_equivalent(ICB : Quadword, n : nat)
  requires n < 0x1_0000_0000;
  ensures CB(ICB,n) == ctr_n(ICB,n);
{
}

// Algorithm 3 

function AES_GCTR(key : seq<uint32>, CB : Quadword, X : seq<Quadword>) : seq<Quadword>
    decreases |X|;
    requires  |X| < 0x1_0000_0000 - 1;
    ensures   |AES_GCTR( key, CB, X)| = |X|;
{
   if |X| == 1 then
    [QuadwordXor(X[0], AES_Encrypt(key, ctr_n(CB, 0), AES_128))]
   else 
      var rest := CTR_Encrypt(key, CB, all_but_last(X));
      rest + [QuadwordXor(X[|X| - 1], AES_Encrypt(key, ctr_n(CB, |X| - 1), AES_128))]
}

// Algorithm 4 
// From 8.3 
// The  total  number  of  invocations  of  the  authenticated  encryption  function  shall  not  exceed  
// 2^32, including all IV lengths and all instances of the authenticated encryption function with 
// the given key. 
// So how do I get the lengths?
//
// This is currently fixed to an IV of 96 bits in the high bits of the IV.

function AES_GCTR_AE(key : seq<uint32>, IV : Quadword, P : seq<Quadword>, A : seq<Quadword>) : (seq<Quadword>, Quadword)
{
    var H := AES_Encrypt(key, Quadword(0, 0, 0, 0), AES_128);
    var J_0 := IV.(lo := 1);        // Consider the top 96 bits of the IV quadword to be the "real" IV
    var C := AES_GCTR(key, inc32(J_0), P);
    var lengths := Quadword(|C|*128, 0, |A|*128, 0);
    var S := GHASH(H, additional_data + C + [lengths]);
    var T := AES_GCTR(key, J_0, [S])[0];
    (C, T)
}

// Algorithm 5

function AES_GCTR_AD(key : seq<uint32>, IV : Quadword, C : seq<Quadword>, T: Quadword) : (seq<Quadword>, bool)
{
    var H := AES_Encrypt(key, Quadword(0, 0, 0, 0), AES_128);
    var J_0 := IV.(lo := 1);        // Consider the top 96 bits of the IV quadword to be the "real" IV
    var P := AES_GCTR(key, inc32(J_0), C);
    var lengths := Quadword(|C|*128, 0, |A|*128, 0);
    var S := GHASH(H, additional_data + C + [lengths]);
    var T' := AES_GCTR(key, J_0, [S])[0];
    (P, T == T')
}
