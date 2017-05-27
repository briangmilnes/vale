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
               ghost iv       : uint64,
               ghost inp :seq<Quadword>,
               ghost inp_end  : uint64,
               ghost inp_heap : heaplet_id,
               ghost out_heap : heaplet_id,
               ghost alg: Algorithm,
               ghost init_ctr : uint64)

// We need to translate Quadwords to uint128 and versa vice.

function QuadwordToUint128(q : Quadword) : uint128
{
  q.hi      * 0x1_00000000_00000000_00000000 +
  q.mid_hi  * 0x1_00000000_00000000 +
  q.mid_lo  * 0x1_00000000 +
  q.lo
}

function QuadwordLow64ToUint64(q : Quadword) : uint64
{
  q.mid_lo  * 0x1_0000_0000 +
  q.lo
}

function Uint128ToQuadword(u : uint128) : Quadword
{
  var hi     := ((u / 0x1_00000000_00000000_00000000) % 0x1_00000000)  as uint32;
  var mid_hi := ((u / 0x1_00000000_00000000) % 0x1_00000000)           as uint32;
  var mid_lo := ((u / 0x1_00000000) % 0x1_00000000)                    as uint32;
  var lo     := (u % 0x1_00000000)                                     as uint32;
  Quadword(hi, mid_hi, mid_lo, lo)
}

// And similarly, without storing things for 64 bit.
function HighUint128(u : uint128) : uint64
{
 (((u / 0x1_00000000_00000000) % 0x1_00000000_00000000) as uint64)
}

function LowUint128(u : uint128) : uint64 
{
 ((u % 0x1_00000000_00000000) as uint64)
}

predicate is_reg_edi(r : operand) {
  r.OReg? && r == OReg(X86Edi)
}

// Bind the registers, passed as operators, to a physical register.
predicate BindRegsPhy1(key_ptr : operand, exp_key_ptr : operand, iv_reg : operand, inp_ptr : operand, inp_end_ptr : operand,  out_ptr : operand, ctr_reg : operand, init_ctr : operand) {
 key_ptr.OReg?      && key_ptr     == OReg(X86Edi) &&
 exp_key_ptr.OReg?  && exp_key_ptr == OReg(X86Esi) && 
 iv_reg.OReg?       && iv_reg      == OReg(X86Edx) && 
 inp_ptr.OReg?      && inp_ptr     == OReg(X86Ecx) && 
 inp_end_ptr.OReg?  && inp_end_ptr == OReg(X86R8) &&
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

predicate CtrInMem(ctr : Quadword, regptr : uint64, heap : heaplet_id, mem : Heaplets) { 
  // That register's value points to a readable source addresss in that heap with public taint.
  ValidSrcAddr(mem, heap, regptr, 128, Public) &&
  mem[heap].QuadwordHeaplet? &&
  ctr == mem[heap].quads[regptr].v
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

predicate ExpKeyInitReq(exp_key : seq<uint32>, exp_key_heap : heaplet_id,
                             exp_key_ptr : uint64, mem : Heaplets) {
  SeqLength(exp_key) == 44 &&
  ValidSrcAddrs(mem, exp_key_heap, exp_key_ptr, 1, Secret, 176)
}

predicate ExpKeyReq(key : seq<uint32>, key_heap : heaplet_id, key_ptr : uint64, exp_key : seq<uint32>, exp_key_heap : heaplet_id,
                             exp_key_ptr : uint64, mem : Heaplets, alg : Algorithm) {
  AlgReq(alg, key, key_ptr) &&
  KeyReq(key, key_heap, key_ptr, mem) && 
  ExpKeyInitReq(exp_key, exp_key_heap, exp_key_ptr, mem) && // Someday we may call this in assembly.
   (forall j :: 0 <= j <= 10 ==> mem[key_heap].quads[key_ptr + 16*j].v == 
         Quadword(exp_key[4*j], exp_key[4*j+1], exp_key[4*j+2], exp_key[4*j+3])) &&
    KeyExpansionPredicate(key, alg, exp_key)
}

predicate InpInMem(inp : seq<Quadword>, inp_heap : heaplet_id, inp_ptr : uint64, 
                   inp_end : uint64, inp_end_ptr : uint64, mem : Heaplets) {
  SeqLength(inp) > 0 &&
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

predicate CTRInv(g : G,
    key_ptr : uint64, exp_key_ptr : uint64,
    inp_ptr : uint64, inp_end_ptr : uint64,
    out_ptr : uint64,
    mem : Heaplets, 
    old_mem : Heaplets)
{
        HeapReq(g.key_heap, g.exp_key_heap, g.inp_heap, g.out_heap, mem, old_mem) &&
        KeyReq(g.key, g.key_heap, key_ptr, mem) &&
        ExpKeyReq(g.key, g.key_heap, key_ptr, g.exp_key, g.exp_key_heap,
                            exp_key_ptr, mem, g.alg) &&
        InpInMem(g.inp, g.inp_heap, inp_ptr, g.inp_end, inp_end_ptr, mem) &&
        OutWriteable(g.inp, g.out_heap, out_ptr, mem) &&
        InpOutInvariants(g.inp, inp_ptr, inp_end_ptr, out_ptr) &&
        mem == old_mem[g.out_heap := mem[g.out_heap]]
}


// Can't make the last requirement work due to a bug in Vale or Dafney.
//predicate ChangeOnly1Block(inp_ptr : uint64,   inp_heap : heaplet_id, 
//                           out_ptr : uint64,   out_heap : heaplet_id,
//                           mem     : Heaplets, old_mem  : Heaplets, iteration : nat) 
//// An awful lot of requirements to move a simple thing into dafny.
//   requires out_heap in mem;                           
//   requires mem[out_heap].QuadwordHeaplet?;
//   requires out_heap in old_mem;
//   requires old_mem[out_heap].QuadwordHeaplet?;
//   requires inp_heap in mem;
//   requires mem[inp_heap].QuadwordHeaplet?;
////   requires (inp_ptr+(iteration*16)) in mem[inp_heap];
//{
//     mem == old_mem[out_heap := mem[out_heap]] &&
//     mem[out_heap].quads == 
//     (old_mem[out_heap].quads)
//     [out_ptr+(iteration*16) := mem[inp_heap].quads[inp_ptr+(iteration*16)]]
//}                            

// Just for learning how to write the code/proofs.

predicate QuadwordSeqsInMemMatch
  (inp  : seq<Quadword>, in_mem  : Heaplet, inp_ptr : uint64,
   out : seq<Quadword>, out_mem : Heaplet, out_ptr : uint64,
   length : int)
  requires in_mem.QuadwordHeaplet?
  requires out_mem.QuadwordHeaplet?
{
  |inp| == |out| &&
  |inp| >= length &&
   forall b:int :: 0 <= b < length ==> 
     inp_ptr  + b*16 in in_mem.quads && 
     out_ptr + b*16 in out_mem.quads && 
     in_mem.quads[inp_ptr + b*16].v == out_mem.quads[out_ptr + b*16].v
}


// End of Module
}
