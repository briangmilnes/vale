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
  // BP: Why do you need these three reveals?  I suspect you can remove some or all of them.
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

function CTR_Encrypt(inp : seq<Quadword>, key : seq<uint32>, alg: Algorithm, iv : uint64, init_ctr : uint64) : seq<Quadword>
    requires CTR_Encrypt_Req(inp, key, alg);
    decreases |inp|;
{
   if |inp| == 1 then
    [QuadwordXor(inp[0], AES_Encrypt(key, ctr_n(iv, init_ctr, 0), alg))]
   else 
      var prefix := CTR_Encrypt(all_but_last(inp), key, alg, iv, init_ctr);
      prefix + [QuadwordXor(inp[|inp| - 1], AES_Encrypt(key, ctr_n(iv, init_ctr, |inp| - 1), alg))]
}

// We don't need a decrypt predicate as the standard uses encrypt again and the xor decrypts.
}
