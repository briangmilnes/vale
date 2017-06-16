include "../../../lib/util/types.s.dfy"
include "../../../lib/util/operations.s.dfy"
include "../../../lib/util/words_and_bytes.s.dfy"
include "../../../lib/collections/Seqs.s.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../arch/x64/vale64.i.dfy"
include "../../../lib/util/dafny_wrappers.i.dfy"
include "../ctr.s.dfy"
include "../aes.s.dfy"
include "ctr_helpers.i.dfy"

module proof {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened dafny_wrappers_i
import opened AESModule
import opened CTRModule
import opened CTRHelpers

lemma {:timeLimitMultiplier 2} lemma_CTR_Encrypt_Upto_Done(g : G, iv : uint64, init_ctr : uint64, out_ptr : uint64, mem: Heaplets, n : uint64)
  requires CTR_Encrypt_Req(g.inp, g.key, g.alg);
  requires |g.inp| == |g.outp|;
  requires n < |g.inp|;
  requires n < |g.outp|;
  requires |g.inp| < 0x1_0000_0000_0000_0000 - 1;
  requires OutWriteable(g.inp, g.out_heap, out_ptr, mem);
  requires CTR_Encrypt_Upto_Done(g, iv, init_ctr, out_ptr, mem, n);
  requires |CTR_Encrypt(g.inp, g.key, g.alg, iv, init_ctr)| > n;
  ensures  |CTR_Encrypt(g.inp, g.key, g.alg, iv, init_ctr)| == |g.outp|;
  requires CTR_Encrypt(g.inp, g.key, g.alg, iv, init_ctr)[n] == 
              mem[g.out_heap].quads[out_ptr + n * 16].v;
  ensures  CTR_Encrypt_Upto_Done(g, iv, init_ctr, out_ptr, mem, n + 1);
{
  lemma_CTR_Encrypt_length'(g.inp, g.key, g.alg, iv, init_ctr);
}

}
