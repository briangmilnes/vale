include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "aes.s.dfy"

module CTRModule {

import opened x64_def_s
import opened types_s
import opened AESModule

// The counter at N increments.
function ctr_n(iv : uint64, init_ctr : uint64, n : uint64) : Quadword 
{
  reveal_BitwiseAdd64();
  reveal_upper64();
  reveal_lower64();
  Quadword(lower64(iv), 
           upper64(iv),
           lower64(bswap64(BitwiseAdd64(init_ctr,n))), 
           upper64(bswap64(BitwiseAdd64(init_ctr,n))))
}

predicate CTR_Encrypt_Req_AES(key : seq<uint32>, alg : Algorithm)  {
    |key| == Nk(alg) &&
    (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1 &&
    (Nb() * (Nr(alg) + 1)) % 4 == 0
}

predicate CTR_Encrypt_Req(inp : seq<Quadword>, key : seq<uint32>, alg: Algorithm) {
    CTR_Encrypt_Req_AES(key, alg) &&
    |inp| > 0 &&
    |inp| < 0x1_0000_0000_0000_0000 - 1
}

function CTR_Encrypt_At(inp : Quadword, key : seq<uint32>, alg: Algorithm, iv : uint64, init_ctr : uint64, n : uint64) : Quadword
  requires CTR_Encrypt_Req_AES(key, alg);
{
     QuadwordXor(inp, AES_Encrypt(key, ctr_n(iv, init_ctr, n), alg))
}

function CTR_Encrypt'(inp : seq<Quadword>, key : seq<uint32>, alg: Algorithm, iv : uint64, init_ctr : uint64, n : uint64) : seq<Quadword>
    requires CTR_Encrypt_Req(inp, key, alg);
    requires |inp| < 0x1_0000_0000_0000_0000 - 1;
    decreases |inp|;
{
   if |inp| == 1 then
    [CTR_Encrypt_At(inp[0], key, alg, iv, init_ctr, n)]
    else
      [CTR_Encrypt_At(inp[0], key, alg, iv, init_ctr, n)] +
       CTR_Encrypt'(inp[1..], key, alg, iv, init_ctr, BitwiseAdd64(n,1))
}

lemma lemma_CTR_Encrypt_length_specific(inp : seq<Quadword>, key:seq<uint32>, alg:Algorithm, iv: uint64, init_ctr : uint64, n : uint64) 
    requires CTR_Encrypt_Req(inp, key, alg);
    requires 0 < |inp| < 0x1_0000_0000_0000_0000 - 1
    decreases |inp|;
    ensures  |CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)| == |inp|;
{
    if |inp| == 1 {
      assert |CTR_Encrypt'(inp, key, alg, iv, init_ctr, n)| == 1;
    } else {
      lemma_CTR_Encrypt_length_specific(inp[1..], key, alg, iv, init_ctr, BitwiseAdd64(n,1));
    }
}

function CTR_Encrypt(inp : seq<Quadword>, key : seq<uint32>, alg: Algorithm, iv : uint64, init_ctr : uint64) : seq<Quadword>
  requires CTR_Encrypt_Req(inp, key, alg);
  ensures  |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == |inp|;
{
   lemma_CTR_Encrypt_length_specific(inp, key, alg, iv, init_ctr, 0);
   CTR_Encrypt'(inp, key, alg, iv, init_ctr, 0)
}

// An unused alternative specification, as recursive functions are closer to the original spec.

predicate CTR_Encrypt_Is(inp : seq<Quadword>, key : seq<uint32>, alg: Algorithm, iv : uint64, init_ctr : uint64, outp : seq<Quadword>) 
    requires CTR_Encrypt_Req(inp, key, alg);
{
 |inp| == |outp| &&
  forall i : nat :: 0 <= i < |inp| ==>
    outp[i] == CTR_Encrypt_At(inp[i], key, alg, iv, init_ctr, i)
}


predicate CTR_Encrypt_Upto(inp : seq<Quadword>, key : seq<uint32>, alg: Algorithm, iv : uint64, init_ctr : uint64, outp : seq<Quadword>, upto : nat) 
    requires upto < |inp|;
    requires CTR_Encrypt_Req(inp, key, alg);
{
 |inp| == |outp| &&
  forall i : nat :: 0 <= i < upto ==>
    outp[i] == CTR_Encrypt_At(inp[i], key, alg, iv, init_ctr, i)
}

// We don't need a decrypt predicate as the standard uses encrypt again and the xor decrypts.
}
