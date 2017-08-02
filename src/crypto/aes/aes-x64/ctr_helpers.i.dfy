include "../../../lib/util/types.s.dfy"
include "../../../lib/util/operations.s.dfy"
include "../../../lib/util/words_and_bytes.s.dfy"
include "../../../lib/collections/Seqs.s.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../lib/util/dafny_wrappers.i.dfy"

include "../ctr.s.dfy"

include "../aes.s.dfy"
include "../aes_helpers.i.dfy"

module CTRHelpers {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened dafny_wrappers_i
import opened AESModule
import opened AESHelpersModule
import opened CTRModule

// Use a ghost var of G, for ghosts, to cut the size of the code.
datatype G = G(ghost key : seq<uint32>,
               ghost key_heap : heaplet_id,
               ghost exp_key : seq<uint32>,
               ghost exp_key_heap : heaplet_id,
               ghost inp :seq<Quadword>,
               ghost inp_heap : heaplet_id,
               ghost out_heap : heaplet_id,
               ghost alg: Algorithm)

// Bind the registers, passed as operators, to a physical register.
predicate BindRegsPhy1(key_ptr : operand, exp_key_ptr : operand, iv_reg : operand, inp_ptr : operand, inp_end_ptr : operand,  out_ptr : operand, iv_ctr : operand, init_ctr : operand, ctr : operand) {
 key_ptr.OReg?      && key_ptr     == OReg(X86Edi) &&
 exp_key_ptr.OReg?  && exp_key_ptr == OReg(X86R8) && 
 iv_reg.OReg?       && iv_reg      == OReg(X86Edx) && 
 inp_ptr.OReg?      && inp_ptr     == OReg(X86Ecx) && 
 inp_end_ptr.OReg?  && inp_end_ptr == OReg(X86Esi) &&
 out_ptr.OReg?      && out_ptr     == OReg(X86R9) &&
 iv_ctr.OReg?      && iv_ctr     == OReg(X86Xmm(4)) &&
 init_ctr.OReg?     && init_ctr    == OReg(X86R12) &&
 ctr.OReg?          && ctr         == OReg(X86R13)
}

predicate BindRegsPhy1Curr(key_ptr : operand, exp_key_ptr : operand, iv_reg : operand, 
                           inp_ptr : operand, inp_end_ptr : operand,  
                           out_ptr : operand, iv_ctr : operand,
                           init_ctr : operand, ctr : operand,
                           curr_inp_ptr : operand, curr_out_ptr : operand) {
  BindRegsPhy1(key_ptr, exp_key_ptr, iv_reg, inp_ptr, inp_end_ptr, out_ptr, iv_ctr, init_ctr, ctr) && 
  curr_inp_ptr.OReg? && curr_inp_ptr  == OReg(X86R10) &&   
  curr_out_ptr.OReg? && curr_out_ptr == OReg(X86R11)
}

// Memory
predicate QuadwordSeqInMemory(qws : seq<Quadword>, mem: Heaplet, ptr : uint64) 
  requires mem.QuadwordHeaplet?
{
    forall b:int :: 0 <= b < |qws| ==> ptr + b*16 in mem.quads && mem.quads[ptr + b*16].v == qws[b]  
}

lemma lemma_BitwiseAdd64()
    ensures  forall x:uint64, y:uint64 :: x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
    ensures  forall x:uint64, y:uint64 :: x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
    ensures  forall x:uint64 :: BitwiseAdd64(x, 0) == x;
{
    reveal_BitwiseAdd64();
}

predicate CtrIncr(oldc : Quadword, newc : Quadword) {
// IV is low and unchanged, specification duplication.
  oldc.mid_lo == newc.mid_lo &&
  oldc.lo     == newc.lo && 

  newc.hi         == upper64(bswap64(BitwiseAdd64(bswap64(lowerUpper64(oldc.hi,oldc.mid_hi)), 1))) &&
  newc.mid_hi     == lower64(bswap64(BitwiseAdd64(bswap64(lowerUpper64(oldc.hi,oldc.mid_hi)), 1)))
}

predicate CtrIncrN(newc : Quadword, init_ctr : uint64, n : nat) 
 requires n < 1_0000_0000_0000_0000;
{
// I'm the init_ctr + n with wrapping.
  newc.hi      == upper64(bswap64(BitwiseAdd64(init_ctr, n))) &&
  newc.mid_hi  == lower64(bswap64(BitwiseAdd64(init_ctr, n)))
}


predicate AlgReq(g : G, key_ptr : uint64) {
  g.alg == AES_128 &&
  |g.key| == Nk(g.alg) && 
  SeqLength(g.key) == Nk(g.alg) &&
  (Nb() * (Nr(g.alg) + 1)) / 4 == Nr(g.alg) + 1 &&   // Easy to prove, but necessary precondition to Cipher
  (Nb() * (Nr(g.alg) + 1)) % 4 == 0 &&   // Easy to prove, but necessary precondition to Cipher
  key_ptr % 16 == 0
}

predicate HeapReq(g : G, mem : Heaplets, old_mem : Heaplets) {
// In the memory
  g.key_heap in mem &&  g.exp_key_heap in mem &&  g.inp_heap in mem &&  g.out_heap in mem &&
  g.key_heap in old_mem &&  g.exp_key_heap in old_mem &&  g.inp_heap in old_mem &&  g.out_heap in old_mem &&

// Disjointness.
  g.key_heap != g.exp_key_heap &&
  g.key_heap != g.inp_heap &&
  g.key_heap != g.out_heap &&
  g.exp_key_heap != g.inp_heap &&
  g.exp_key_heap != g.out_heap &&
  g.inp_heap != g.out_heap &&

// Types of heaplets in memory.
  mem[g.inp_heap].QuadwordHeaplet? &&
  mem[g.out_heap].QuadwordHeaplet? &&

// Heaplets don't change.
  mem[g.key_heap]    == old_mem[g.key_heap] &&
  mem[g.exp_key_heap] == old_mem[g.exp_key_heap] &&
  mem[g.inp_heap] == old_mem[g.inp_heap]
}

predicate KeyReq(g : G, exp_key_ptr : uint64, mem : Heaplets) {
  ValidSrcAddrs(mem, g.exp_key_heap, exp_key_ptr, 128, Secret, 11*16) &&   // Key is readable
  exp_key_ptr % 16 == 0 &&
  SeqLength(g.exp_key) == 44 
}

predicate ExpKeyReq(g : G, key_ptr : uint64, exp_key_ptr : uint64, mem : Heaplets) {
  AlgReq(g, key_ptr) &&
  KeyReq(g, exp_key_ptr, mem) &&
  (forall j :: 0 <= j <= 10 ==> mem[g.exp_key_heap].quads[exp_key_ptr + 16*j].v == 
         Quadword(g.exp_key[4*j], g.exp_key[4*j+1], g.exp_key[4*j+2], g.exp_key[4*j+3])) &&
    KeyExpansionPredicate(g.key, g.alg, g.exp_key)
}

predicate InpInMem(g : G, inp_ptr : uint64, inp_end_ptr : uint64, mem : Heaplets) {
  0 < SeqLength(g.inp) < 1_0000_0000_0000_0000 - 1 &&
  ValidSrcAddrs(mem, g.inp_heap, inp_ptr, 128, Secret, SeqLength(g.inp)*16) &&
  QuadwordSeqInMemory(g.inp, mem[g.inp_heap], inp_ptr)
}

predicate OutWriteable(inp : seq<Quadword>, out_heap : heaplet_id, 
                       out_ptr : uint64, mem : Heaplets) {
  ValidSrcAddrs(mem, out_heap, out_ptr, 128, Secret, SeqLength(inp)*16)
}

predicate InpOutInvariants(inp : seq<Quadword>, inp_ptr : uint64, inp_end_ptr : uint64, 
                               out_ptr : uint64) {
   inp_ptr + SeqLength(inp)*16 < 0x1_0000_0000_0000_0000 &&
   out_ptr + SeqLength(inp)*16 < 0x1_0000_0000_0000_0000 &&
   inp_end_ptr >= inp_ptr && 
   inp_end_ptr == inp_ptr + SeqLength(inp)*16 &&
   inp_end_ptr < 0x1_0000_0000_0000_0000 
}

// What is true before the setup.
predicate CTRInvInit(g : G,
    key_ptr : uint64, exp_key_ptr : uint64,
    inp_ptr : uint64, inp_end_ptr : uint64,
    out_ptr : uint64,
    iv_reg  : uint64,
    ctr     : uint64,
    mem : Heaplets, 
    old_mem : Heaplets)
{
        HeapReq(g, mem, old_mem) &&
        KeyReq(g, key_ptr, mem) &&
        ExpKeyReq(g, key_ptr, exp_key_ptr, mem) &&
        InpInMem(g, inp_ptr, inp_end_ptr, mem) &&
        OutWriteable(g.inp, g.out_heap, out_ptr, mem) &&
        InpOutInvariants(g.inp, inp_ptr, inp_end_ptr, out_ptr) &&
//        |g.inp| == |g.outp| &&
        0 <= |g.inp|  < 0x1_0000_0000_0000_0000 - 1 &&
//      0 <= |g.outp| < 0x1_0000_0000_0000_0000 - 1 &&
        mem == old_mem[g.out_heap := mem[g.out_heap]]
}

predicate IvReq(g : G, iv_reg : uint64, iv_ctr : Quadword) {
//  reveal_upper64();
//  reveal_lower64();
  iv_ctr.mid_lo  == upper64(iv_reg) &&
  iv_ctr.lo      == lower64(iv_reg)
}

predicate CTRInv(g : G,
    key_ptr : uint64, exp_key_ptr : uint64,
    inp_ptr : uint64, inp_end_ptr : uint64,
    out_ptr : uint64,
    iv_reg  : uint64,
    iv_ctr : Quadword,
    ctr    : uint64,
    mem    : Heaplets, 
    old_mem : Heaplets)
{
   CTRInvInit(g, key_ptr, exp_key_ptr, inp_ptr, inp_end_ptr, out_ptr, iv_reg, ctr, mem, old_mem) &&
   IvReq(g, iv_reg, iv_ctr)
}

predicate CtrInvBefore(iv_reg : uint64, iv_ctr : Quadword, init_ctr : uint64, ctr : uint64, blocktobecopied : nat) {
  blocktobecopied < 1_0000_0000_0000_0000 - 1 &&
  iv_ctr.mid_lo == upper64(iv_reg) &&
  iv_ctr.lo == lower64(iv_reg) &&

  ctr == BitwiseAdd64(init_ctr, blocktobecopied) &&
  iv_ctr.hi         == upper64(bswap64(ctr)) &&
  iv_ctr.mid_hi     == lower64(bswap64(ctr))
}

predicate CtrInvAfter(iv_reg : uint64, iv_ctr : Quadword, init_ctr : uint64, ctr: uint64, blocktobecopied : nat) 
{
  reveal_BitwiseAdd64();
  reveal_upper64();
  reveal_lower64();
  reveal_lowerUpper64();

  blocktobecopied < 1_0000_0000_0000_0000 &&
  iv_ctr.mid_lo == upper64(iv_reg) &&
  iv_ctr.lo == lower64(iv_reg) &&

  ctr == BitwiseAdd64(init_ctr, blocktobecopied) &&
  iv_ctr.hi         == upper64(bswap64(ctr)) &&
  iv_ctr.mid_hi     == lower64(bswap64(ctr))
}

predicate CopyInvAlways(g : G,
                  inp_ptr : uint64, inp_end_ptr : uint64, curr_inp_ptr : uint64,
                  out_ptr : uint64, curr_out_ptr : uint64,
                  blockscopied : int) 
{
//     |g.inp| == |g.outp| && 
     0 <= |g.inp|  < 1_0000_0000_0000_0000 - 1 && 
//     0 <= |g.outp| < 1_0000_0000_0000_0000 - 1 && 
     curr_inp_ptr == inp_ptr + blockscopied * 16 &&
     curr_out_ptr == out_ptr + blockscopied * 16 &&
     inp_end_ptr  == inp_ptr  + SeqLength(g.inp) * 16
}

predicate InputInOutputMem(g : G, out_ptr : uint64, iv_reg : uint64, init_ctr : uint64, ctr : uint64, 
                          iv_ctr : Quadword, key_ptr : uint64,
                           mem : Heaplets, blockscopied : int)
 requires 0 <= |g.inp|  < 1_0000_0000_0000_0000 - 1;
// requires 0 <= |g.outp| < 1_0000_0000_0000_0000 - 1;
 requires g.out_heap in mem;
 requires ValidSrcAddrs(mem, g.out_heap, out_ptr, 128, Secret, |g.inp|* 16)
 requires AlgReq(g, key_ptr);
// requires |g.inp| == |g.outp|;
{
  0 <= blockscopied <= |g.inp| &&
  forall j: nat :: 0 <= j < blockscopied ==>
  ((QuadwordXor(g.inp[j], AES_Encrypt(g.key, ctr_n(iv_reg, init_ctr, j), g.alg)) == mem[g.out_heap].quads[out_ptr + j * 16].v))
// Bryan does this last. 
// &&  
//  forall j: nat :: 0 <= j < blockscopied ==>
//   (g.outp[j] == mem[g.out_heap].quads[out_ptr + j*16].v)
}

predicate CopyInvBefore(g : G,
                       inp_ptr : uint64, inp_end_ptr : uint64, curr_inp_ptr : uint64,
                       out_ptr : uint64, curr_out_ptr : uint64,
                       iv_reg : uint64, init_ctr : uint64, iv_ctr : Quadword, ctr : uint64,
                       key_ptr : uint64,
                       mem : Heaplets,
                       blocktobecopied : int) 
 requires |g.inp| < 1_0000_0000_0000_0000;
 requires g.out_heap in mem;
 requires ValidSrcAddrs(mem, g.out_heap, out_ptr, 128, Secret, |g.inp|* 16);
 requires AlgReq(g, key_ptr);
{
     CopyInvAlways(g, inp_ptr, inp_end_ptr, curr_inp_ptr, out_ptr, curr_out_ptr, blocktobecopied) &&
     inp_ptr <= curr_inp_ptr <= inp_end_ptr &&
     0 <= blocktobecopied < |g.inp| &&
     InputInOutputMem(g, out_ptr, iv_reg, init_ctr, ctr, iv_ctr, key_ptr, mem, blocktobecopied)
}

predicate CopyInvAfter(g : G,
                       inp_ptr : uint64, inp_end_ptr : uint64, curr_inp_ptr : uint64,
                       out_ptr : uint64, curr_out_ptr : uint64, 
                       iv_reg : uint64, init_ctr : uint64, iv_ctr : Quadword, ctr : uint64,
                       key_ptr : uint64,
                       mem : Heaplets, old_mem : Heaplets,
                       blockscopied : int)
  requires |g.inp| < 1_0000_0000_0000_0000;
  requires 0 <= blockscopied <= |g.inp|;
  requires g.out_heap in mem;
  requires mem[g.out_heap].QuadwordHeaplet?;
  requires ValidSrcAddrs(mem, g.out_heap, out_ptr, 128, Secret, |g.inp|* 16)
  requires AlgReq(g, key_ptr);
//  requires |g.inp| == |g.outp|;
{
     CopyInvAlways(g, inp_ptr, inp_end_ptr, curr_inp_ptr, out_ptr, curr_out_ptr, blockscopied) &&
     inp_ptr <= curr_inp_ptr <= inp_end_ptr &&
     InputInOutputMem(g, out_ptr, iv_reg, init_ctr, ctr, iv_ctr, key_ptr, mem, blockscopied)
}

lemma lemma_CTR_Encrypt_length(inp : seq<Quadword>) 
   decreases |inp|;
   requires |inp| > 0;
   ensures forall key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64 ::  
    CTR_Encrypt_Req(inp, key, alg) &&
    |inp| < 0x1_0000_0000_0000_0000 - 1 ==>
    |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == |inp|;
{
    if |inp| == 1 {
      assert forall key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64, n : uint64 :: 
        CTR_Encrypt_Req(inp, key, alg) &&
        |inp| < 0x1_0000_0000_0000_0000 - 1 ==>
        |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == 1;
    } else {
      lemma_CTR_Encrypt_length(all_but_last(inp));
    }
}

lemma lemma_CTR_Encrypt_length'(inp : seq<Quadword>, key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64)
   decreases |inp|;
   requires |inp| > 0;
   requires |inp| < 0x1_0000_0000_0000_0000 - 1;
   requires CTR_Encrypt_Req(inp, key, alg);
   ensures |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == |inp|;
{
    if |inp| == 1 {
      assert |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == 1;
    } else {
       lemma_CTR_Encrypt_length'(all_but_last(inp), key, alg, iv, init_ctr);
    }
}

lemma{:timeLimitMultiplier 3} lemma_CTR_Encrypt_Is_QuadwordXor_AES(inp : seq<Quadword>, key : seq<uint32>, alg : Algorithm, iv : uint64, init_ctr : uint64)
  requires CTR_Encrypt_Req(inp, key, alg);
  requires 0 < |inp| < 0x1_0000_0000_0000_0000 - 1;
  ensures |CTR_Encrypt(inp, key, alg, iv, init_ctr)| == |inp|;
  ensures forall i : nat :: i < |inp| ==>
   CTR_Encrypt(inp, key, alg, iv, init_ctr)[i] == 
    QuadwordXor(inp[i], AES_Encrypt(key, ctr_n(iv, init_ctr, i), alg));
{
  lemma_CTR_Encrypt_length'(inp, key, alg, iv, init_ctr);
  if |inp| == 1 {
    assert CTR_Encrypt(inp, key, alg, iv, init_ctr)[0] == 
      QuadwordXor(inp[0], AES_Encrypt(key, ctr_n(iv, init_ctr, 0), alg));
  } else {
    lemma_CTR_Encrypt_Is_QuadwordXor_AES(all_but_last(inp), key, alg, iv, init_ctr);
  }
}

predicate CTR_Encrypt_Upto_Done(g : G, iv : uint64, init_ctr : uint64, out_ptr : uint64, mem : Heaplets, n : uint64)
 requires CTR_Encrypt_Req(g.inp, g.key, g.alg);
// requires |g.inp| == |g.outp|;
 requires n <= SeqLength(g.inp);
 requires OutWriteable(g.inp, g.out_heap, out_ptr, mem);
{
  lemma_CTR_Encrypt_length(g.inp);
  forall j : nat :: j < n ==>
   CTR_Encrypt(g.inp, g.key, g.alg, iv, init_ctr)[j] == mem[g.out_heap].quads[out_ptr + j * 16].v //&&
//  forall j : nat :: j < n ==>
//   g.outp[j] == mem[g.out_heap].quads[out_ptr + j * 16].v
}

lemma {:timeLimitMultiplier 3} lemma_CTR_Encrypt_Upto_Done(g : G, iv : uint64, init_ctr : uint64, out_ptr : uint64, mem: Heaplets, n : uint64)
  requires CTR_Encrypt_Req(g.inp, g.key, g.alg);
//  requires |g.inp| == |g.outp|;
  requires n < |g.inp|;
//  requires n < |g.outp|;
  requires |g.inp| < 0x1_0000_0000_0000_0000 - 1;
  requires OutWriteable(g.inp, g.out_heap, out_ptr, mem);
  requires CTR_Encrypt_Upto_Done(g, iv, init_ctr, out_ptr, mem, n);
  requires |CTR_Encrypt(g.inp, g.key, g.alg, iv, init_ctr)| > n;
//  ensures  |CTR_Encrypt(g.inp, g.key, g.alg, iv, init_ctr)| == |g.outp|;
  requires CTR_Encrypt(g.inp, g.key, g.alg, iv, init_ctr)[n] == 
              mem[g.out_heap].quads[out_ptr + n * 16].v;
//  requires g.outp[n] == mem[g.out_heap].quads[out_ptr + n * 16].v;
  ensures  CTR_Encrypt_Upto_Done(g, iv, init_ctr, out_ptr, mem, n + 1);
{
  lemma_CTR_Encrypt_length'(g.inp, g.key, g.alg, iv, init_ctr);
}

// End of Module
}
