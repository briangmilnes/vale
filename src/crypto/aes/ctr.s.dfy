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
  Quadword(lower64(BitwiseAdd64(init_ctr,n)), 
           upper64(BitwiseAdd64(init_ctr,n)),
           lower64(iv), 
           upper64(iv))
}


predicate CTR_EncryptReq(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, n : uint64) {
    |input| > 0 &&
    |input| < 0x1_0000_0000_0000_0000 - 1 &&
    n + |input| < 0x1_0000_0000_0000_0000 - 1 &&
    |key| == Nk(alg) &&
    (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1 &&
    (Nb() * (Nr(alg) + 1)) % 4 == 0
}

function CTR_EncryptAt(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, iv : uint64, init_ctr : uint64, n : uint64) : Quadword
    requires CTR_EncryptReq(key, input, alg, n);
    decreases |input|;
{
     QuadwordXor(input[0], AES_Encrypt(key, ctr_n(iv, init_ctr, n), alg))
}

function CTR_Encrypt(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, iv : uint64, init_ctr : uint64, n : uint64) : seq<Quadword>
    decreases |input|;
    requires CTR_EncryptReq(key, input, alg, n);
{
    if |input| == 1 then
      [QuadwordXor(input[0], AES_Encrypt(key, ctr_n(iv, init_ctr, n), alg))]
    else
      var first := [CTR_EncryptAt(key,input,alg, iv, init_ctr, n)];
      first + CTR_Encrypt(key, all_but_first(input), alg, iv, init_ctr, n + 1)
}

// We don't need a decrypt predicate as the standard uses encrypt again and the xor decrypts.
}
