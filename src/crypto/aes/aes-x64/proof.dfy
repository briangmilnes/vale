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

lemma lemma_CTROutput(g : G, iv_reg : uint64, init_ctr : uint64, out_ptr : uint64, mem : Heaplets)
  returns (output : seq<Quadword>)
  requires CTR_Encrypt_Req(g.inp, g.key, g.alg);
  requires OutWriteable(g.inp, g.out_heap, out_ptr, mem);
  requires ValidSrcAddrs(mem, g.out_heap, out_ptr, 128, Secret, SeqLength(g.inp)*16)
  requires CTR_Encrypt_Upto_Done(g, iv_reg, init_ctr, out_ptr, mem, SeqLength(g.inp));
  ensures  output == CTR_Encrypt(g.inp, g.key, g.alg, iv_reg, init_ctr);
{
  output := CTR_Encrypt(g.inp, g.key, g.alg, iv_reg, init_ctr);
  lemma_CTR_Encrypt_length(g.inp);
  assert  forall j : nat :: 0 <= j < |output| ==>
    output[j] == mem[g.out_heap].quads[out_ptr + j*16].v;
  assert forall j : nat :: j < |output| ==>
   CTR_Encrypt(g.inp, g.key, g.alg, iv_reg, init_ctr)[j] == mem[g.out_heap].quads[out_ptr + j * 16].v;
}

}
