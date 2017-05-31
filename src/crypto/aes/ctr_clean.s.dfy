include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

include "aes.s.dfy"
include "aes_helpers.i.dfy"

module CTRModuleClean {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened dafny_wrappers_i
import opened AESModule
import opened AESHelpersModule

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
predicate BindRegsPhy1(key_ptr : operand, exp_key_ptr : operand, iv_reg : operand, inp_ptr : operand, inp_end_ptr : operand,  out_ptr : operand, ctr_reg : operand, init_ctr : operand) {
 key_ptr.OReg?      && key_ptr     == OReg(X86Edi) &&
 exp_key_ptr.OReg?  && exp_key_ptr == OReg(X86R8) && 
 iv_reg.OReg?       && iv_reg      == OReg(X86Edx) && 
 inp_ptr.OReg?      && inp_ptr     == OReg(X86Ecx) && 
 inp_end_ptr.OReg?  && inp_end_ptr == OReg(X86Esi) &&
 out_ptr.OReg?      && out_ptr     == OReg(X86R9) &&
 ctr_reg.OReg?      && ctr_reg     == OReg(X86Xmm(4)) &&
 init_ctr.OReg?     && init_ctr    == OReg(X86R12) 
}

predicate BindRegsPhy1Curr(key_ptr : operand, exp_key_ptr : operand, iv_reg : operand, 
                           inp_ptr : operand, inp_end_ptr : operand,  
                           out_ptr : operand, ctr_reg : operand,
                           init_ctr : operand,
                           curr_inp_ptr : operand, curr_out_ptr : operand) {
  BindRegsPhy1(key_ptr, exp_key_ptr, iv_reg, inp_ptr, inp_end_ptr, out_ptr, ctr_reg, init_ctr) && 
  curr_inp_ptr.OReg? && curr_inp_ptr  == OReg(X86R10) &&   
  curr_out_ptr.OReg? && curr_out_ptr == OReg(X86R11)
}

// Memory
predicate Mem128ChangedOnlyIn(regptr : uint64, count : int, heap : heaplet_id, mem : Heaplets, oldmem: Heaplets)
{
    heap in mem &&
    mem == oldmem[heap := mem[heap]] &&
    mem[heap].QuadwordHeaplet? &&
    heap in oldmem &&
    oldmem[heap].QuadwordHeaplet? &&
    forall a :: (a < regptr || a >= regptr + count * 16) &&
     a in mem[heap].quads ==> a in oldmem[heap].quads &&
     mem[heap].quads[a] == oldmem[heap].quads[a]
}

predicate Mem64ChangedOnlyIn(regptr : uint64, count : int, heap : heaplet_id, mem : Heaplets, oldmem: Heaplets)
{
    heap in mem &&
    mem == oldmem[heap := mem[heap]] &&
    mem[heap].Heaplet64? &&
    heap in oldmem &&
    oldmem[heap].Heaplet64? &&
    forall a :: (a < regptr || a >= regptr + count * 8) &&
     a in mem[heap].mem64 ==> a in oldmem[heap].mem64 &&
     mem[heap].mem64[a] == oldmem[heap].mem64[a]
}

predicate QuadwordSeqInMemory(qws : seq<Quadword>, mem: Heaplet, ptr : uint64) 
  requires mem.QuadwordHeaplet?
{
    forall b:int :: 0 <= b < |qws| ==> ptr + b*16 in mem.quads && mem.quads[ptr + b*16].v == qws[b]  
}

// TODO obviate 
predicate CtrInMem(ctr : Quadword, regptr : uint64, heap : heaplet_id, mem : Heaplets) { 
  // That register's value points to a readable source addresss in that heap with public taint.
  ValidSrcAddr(mem, heap, regptr, 128, Public) &&
  mem[heap].QuadwordHeaplet? &&
  ctr == mem[heap].quads[regptr].v
}

lemma lemma_BitwiseAdd64()
    ensures  forall x:uint64, y:uint64 :: x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
    ensures  forall x:uint64, y:uint64 :: x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
    ensures  forall x:uint64 :: BitwiseAdd64(x, 0) == x;
{
    reveal_BitwiseAdd64();
}

predicate CtrIncr(oldc : Quadword, newc : Quadword) {
  oldc.hi     == newc.hi &&
  oldc.mid_hi == newc.mid_hi &&
  newc.mid_lo == upper64(BitwiseAdd64(lowerUpper64(oldc.lo,oldc.mid_lo), 1)) &&
  newc.lo     == lower64(BitwiseAdd64(lowerUpper64(oldc.lo,oldc.mid_lo), 1))
}

predicate CtrIncrN(newc : Quadword, init_ctr : uint64, n : nat) 
 requires n < 1_0000_0000_0000_0000;
{
// I'm the init_ctr + n with wrapping.
  newc.mid_lo == upper64(BitwiseAdd64(init_ctr, n)) &&
  newc.lo     == lower64(BitwiseAdd64(init_ctr, n))
}

lemma lemma_CtrIncrNTrans(old_ctr : Quadword, new_ctr: Quadword, init_ctr : uint64, n : nat)
  requires n + 1 < 1_0000_0000_0000_0000;
  requires CtrIncrN(old_ctr, init_ctr, n);
  requires CtrIncr (old_ctr,  new_ctr);
  ensures  CtrIncrN(new_ctr, init_ctr, n + 1);
{
  lemma_BitwiseAdd64();
  reveal_BitwiseAdd64();
  reveal_upper64();
  reveal_lower64();
  reveal_lowerUpper64();
}

predicate CtrInvBefore(iv_reg : uint64, ctr_reg : Quadword, init_ctr : uint64, blocktobecopied : nat) {
  blocktobecopied + 1 < 1_0000_0000_0000_0000 &&
  ctr_reg.hi == upper64(iv_reg) &&
  ctr_reg.mid_hi == lower64(iv_reg) &&
  ctr_reg.mid_lo == upper64(BitwiseAdd64(init_ctr, blocktobecopied)) &&
  ctr_reg.lo     == lower64(BitwiseAdd64(init_ctr, blocktobecopied))
}

predicate CtrInvAfter(iv_reg : uint64, ctr_reg : Quadword, init_ctr : uint64, blocktobecopied : nat) 
{
  reveal_BitwiseAdd64();
  reveal_upper64();
  reveal_lower64();
  reveal_lowerUpper64();

  blocktobecopied < 1_0000_0000_0000_0000 &&
  ctr_reg.hi == upper64(iv_reg) &&
  ctr_reg.mid_hi == lower64(iv_reg) &&
  ctr_reg.mid_lo == upper64(BitwiseAdd64(init_ctr, blocktobecopied)) &&
  ctr_reg.lo     == lower64(BitwiseAdd64(init_ctr, blocktobecopied))
}

predicate AlgReq(alg : Algorithm, key : seq<uint32>, key_ptr : uint64) {
  alg == AES_128 &&
  |key| == Nk(alg) && 
  SeqLength(key) == Nk(alg) &&
  (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1 &&   // Easy to prove, but necessary precondition to Cipher
  (Nb() * (Nr(alg) + 1)) % 4 == 0 &&   // Easy to prove, but necessary precondition to Cipher
  key_ptr % 16 == 0

}

predicate HeapReq(key_heap : heaplet_id, exp_key_heap : heaplet_id, inp_heap : heaplet_id, out_heap : heaplet_id, mem : Heaplets, old_mem : Heaplets) {
// In the memory
  key_heap in mem &&  exp_key_heap in mem &&  inp_heap in mem &&  out_heap in mem &&
  key_heap in old_mem &&  exp_key_heap in old_mem &&  inp_heap in old_mem &&  out_heap in old_mem &&

// Disjointness.
  key_heap != exp_key_heap &&
  key_heap != inp_heap &&
  key_heap != out_heap &&
  exp_key_heap != inp_heap &&
  exp_key_heap != out_heap &&
  inp_heap != out_heap &&

// Types of heaplets in memory.
  mem[inp_heap].QuadwordHeaplet? &&
  mem[out_heap].QuadwordHeaplet? &&

// Heaplets don't change.
  mem[key_heap]    == old_mem[key_heap] &&
  mem[exp_key_heap] == old_mem[exp_key_heap] &&
  mem[inp_heap] == old_mem[inp_heap]
}


predicate KeyReq(key : seq<uint32>, key_heap : heaplet_id, key_ptr : uint64, mem : Heaplets) {
  ValidSrcAddrs(mem, key_heap, key_ptr, 128, Secret, 11*16) &&   // Key is readable
  key_ptr % 16 == 0
}

predicate ExpKeyReq(key : seq<uint32>, key_heap : heaplet_id, key_ptr : uint64, exp_key : seq<uint32>, exp_key_heap : heaplet_id,
                             exp_key_ptr : uint64, mem : Heaplets, alg : Algorithm) {
  AlgReq(alg, key, key_ptr) &&
  KeyReq(key, key_heap, key_ptr, mem) && 
  SeqLength(exp_key) == 44 &&
   (forall j :: 0 <= j <= 10 ==> mem[key_heap].quads[key_ptr + 16*j].v == 
         Quadword(exp_key[4*j], exp_key[4*j+1], exp_key[4*j+2], exp_key[4*j+3])) &&
    KeyExpansionPredicate(key, alg, exp_key)
}

predicate InpInMem(inp : seq<Quadword>, inp_heap : heaplet_id, inp_ptr : uint64, 
                   inp_end : uint64, inp_end_ptr : uint64, mem : Heaplets) {
  // TODO - 1 weakens the length of sequence.                    
  0 < SeqLength(inp) < 1_0000_0000_0000_0000 - 1 &&
  ValidSrcAddrs(mem, inp_heap, inp_ptr, 128, Secret, SeqLength(inp)*16) &&
  QuadwordSeqInMemory(inp, mem[inp_heap], inp_ptr)
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

// On the call, what is true before the setup?
predicate CTRInvInit(g : G,
    key_ptr : uint64, exp_key_ptr : uint64,
    inp_ptr : uint64, inp_end_ptr : uint64,
    out_ptr : uint64,
    iv_reg  : uint64,
    mem : Heaplets, 
    old_mem : Heaplets)
{
        HeapReq(g.key_heap, g.exp_key_heap, g.inp_heap, g.out_heap, mem, old_mem) &&
        KeyReq(g.key, g.key_heap, key_ptr, mem) &&
        ExpKeyReq(g.key, g.key_heap, key_ptr, g.exp_key, g.exp_key_heap,
                            exp_key_ptr, mem, g.alg) &&
        InpInMem(g.inp, g.inp_heap, inp_ptr, inp_end_ptr, inp_end_ptr, mem) &&
        OutWriteable(g.inp, g.out_heap, out_ptr, mem) &&
        InpOutInvariants(g.inp, inp_ptr, inp_end_ptr, out_ptr) &&
        mem == old_mem[g.out_heap := mem[g.out_heap]]
}

predicate CTRInv(g : G,
    key_ptr : uint64, exp_key_ptr : uint64,
    inp_ptr : uint64, inp_end_ptr : uint64,
    out_ptr : uint64,
    iv_reg  : uint64,
    ctr_reg : Quadword,
    mem : Heaplets, 
    old_mem : Heaplets)
{
   CTRInvInit(g, key_ptr, exp_key_ptr, inp_ptr, inp_end_ptr, out_ptr, iv_reg, mem, old_mem)
}

predicate InputInOutputMem(inp : seq<Quadword>, out_ptr : uint64, out_heap : heaplet_id, 
                           ctr_reg : Quadword, mem : Heaplets, blockscopied : int)
 requires out_heap in mem;
 requires ValidSrcAddrs(mem, out_heap, out_ptr, 128, Secret, |inp|* 16)
{
  0 <= blockscopied <= |inp| //&&
//  forall j: nat :: 0 <= j < blockscopied ==>
//   QuadwordXor(inp[j], ctr_reg) == mem[out_heap].quads[out_ptr + j * 16].v
}

predicate CopyInvAlways(inp : seq<Quadword>,
                  inp_ptr : uint64, inp_end_ptr : uint64, curr_inp_ptr : uint64,
                  out_ptr : uint64, curr_out_ptr : uint64,
                  blockscopied : int) {
     curr_inp_ptr == inp_ptr + blockscopied * 16 &&
     curr_out_ptr == out_ptr + blockscopied * 16 &&
     inp_end_ptr  == inp_ptr  + SeqLength(inp) * 16
}

// End of Module
}
