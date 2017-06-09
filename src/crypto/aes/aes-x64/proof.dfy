include "../../../lib/util/types.s.dfy"
include "../../../lib/util/operations.s.dfy"
include "../../../lib/util/words_and_bytes.s.dfy"
include "../../../lib/collections/Seqs.s.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../arch/x64/vale64.i.dfy"
include "../../../lib/util/dafny_wrappers.i.dfy"
include "../ctr.s.dfy"
include "../aes.s.dfy"
//include "../aes_helpers.i.dfy"
include "ctr_helpers.i.dfy"

module proof {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened dafny_wrappers_i
import opened AESModule
//import opened AESHelpersModule
import opened CTRModule
import opened CTRHelpers

/*
lemma lemma_BitwiseAdd64xy(x : uint64, y: uint64)
    ensures  x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
    ensures  x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
    ensures  forall x:uint64 :: BitwiseAdd64(x, 0) == x;
{
    reveal_BitwiseAdd64();
}

lemma {:timeLimitMultiplier 6} lemma_CTR_Encrypt'_Is(inp : seq<Quadword>, key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64, n : uint64, i : nat)
  requires CTR_Encrypt_Req(inp, key, alg);
  requires 0 < |inp| < 0x1_0000_0000_0000_0000 - 1;
  requires i < |inp|;
  ensures |CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)| == |inp|;
  ensures 
    CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)[i] == 
      QuadwordXor(inp[i], AES_Encrypt(key, ctr_n(iv, init_ctr, BitwiseAdd64(n,i)), alg));
{
  lemma_CTR_Encrypt'_length(inp);
  lemma_BitwiseAdd64xy(n,1); // works but times out a lot.
  if i == 0 {
    assert
      CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)[0] == 
       QuadwordXor(inp[0], AES_Encrypt(key, ctr_n(iv, init_ctr, n), alg));
  } else {
    lemma_CTR_Encrypt'_Is(inp[1..], key, alg, iv, init_ctr, BitwiseAdd64(n,1), i - 1);
  }
}
*/

lemma{:timeLimitMultiplier 6} lemma_CTR_Encrypt'_Is_QuadwordXor_AES(inp : seq<Quadword>, key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64, n : uint64) 
  requires CTR_Encrypt_Req(inp, key, alg);
  requires 0 < |inp| < 0x1_0000_0000_0000_0000 - 1;
  ensures |CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)| == |inp|;
  ensures forall i : nat :: i < |inp| ==>
   CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)[i] == 
    QuadwordXor(inp[i], AES_Encrypt(key, ctr_n(iv, init_ctr, BitwiseAdd64(n,i)), alg));
{
  lemma_CTR_Encrypt'_length(inp);
  lemma_BitwiseAdd64(); // works but times out a lot.
  //lemma_BitwiseAdd64xy(n,i);
  //lemma_BitwiseAdd64xy(n,1);
  if |inp| == 1 {
    assert
      CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)[0] == 
       QuadwordXor(inp[0], AES_Encrypt(key, ctr_n(iv, init_ctr, n), alg));
  } else {
    lemma_CTR_Encrypt'_Is_QuadwordXor_AES(inp[1..], key, alg, iv, init_ctr, BitwiseAdd64(n,1));
  }
}

lemma{:timeLimitMultiplier 6} lemma_CTR_Encrypt_Is_Encrypt'_zero(inp : seq<Quadword>, key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64) 
  requires CTR_Encrypt_Req(inp, key, alg);
  requires 0 < |inp| < 0x1_0000_0000_0000_0000 - 1;
  ensures |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == |inp|;
  ensures CTR_Encrypt(inp, key, alg, iv, init_ctr) == CTR_Encrypt'(inp, key, alg, iv, init_ctr, 0);
{
  lemma_CTR_Encrypt_length(inp);
}

lemma{:timeLimitMultiplier 6} lemma_CTR_Encrypt_Is_Encrypt'_zero_gen(inp : seq<Quadword>, key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64) 
  requires CTR_Encrypt_Req(inp, key, alg);
  requires 0 < |inp| < 0x1_0000_0000_0000_0000 - 1;
  ensures |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == |inp|;
  ensures forall i : nat :: i < |inp| ==> 
    CTR_Encrypt(inp, key, alg, iv, init_ctr)[i] == CTR_Encrypt'(inp, key, alg, iv, init_ctr, 0)[i];
{
  lemma_CTR_Encrypt_length(inp);
  lemma_CTR_Encrypt_Is_Encrypt'_zero(inp, key, alg, iv, init_ctr);
}

lemma{:timeLimitMultiplier 6} lemma_CTR_Encrypt_Is_QuadwordXor_AES(inp : seq<Quadword>, key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64, n : uint64)
  requires CTR_Encrypt_Req(inp, key, alg);
  requires 0 < |inp| < 0x1_0000_0000_0000_0000 - 1;
  ensures |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == |inp|;
  ensures forall i : nat :: i < |inp| ==>
   CTR_Encrypt(inp, key, alg, iv, init_ctr)[i] == 
    QuadwordXor(inp[i], AES_Encrypt(key, ctr_n(iv, init_ctr, BitwiseAdd64(n,i)), alg));
{
  lemma_CTR_Encrypt'_length(inp);
  lemma_BitwiseAdd64(); // works but times out a lot.

 lemma_CTR_Encrypt'_Is_QuadwordXor_AES(inp, key, alg, iv, init_ctr, n);
 lemma_CTR_Encrypt_Is_Encrypt'_zero(inp, key, alg, iv, init_ctr);
// lemma_CTR_Encrypt_Is_Encrypt'_zero_gen(inp, key, alg, iv, init_ctr);
}

}
