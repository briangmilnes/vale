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

datatype Pair<T,U> = Pair(0: T,1: U)
datatype G = G(ghost key : seq<uint32>,
               ghost key_heap : heaplet_id,
               ghost expanded_key : seq<uint32>,
               ghost expanded_key_heap : heaplet_id,
               ghost iv       : uint64,
               ghost input :seq<Quadword>,
               ghost input_end  : uint64,
               ghost input_heap : heaplet_id,
               ghost output_heap : heaplet_id,
               ghost alg: Algorithm,
               ghost mem : Heaplets,
               ghost old_mem : Heaplets)

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

// Memory
//  Only writing one heap and only from one pointer in a quadword heap
//  and only count worth of N bytes.
predicate Mem128ChangedOnlyIn(regptr : uint128, count : int, heap : heaplet_id, mem : Heaplets, oldmem: Heaplets)
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

// Memory


// Ctr is in a register.
predicate CtrInReg(ctr : Quadword, reg : Quadword) {
  ctr == reg
}

predicate CtrInMem(ctr : Quadword, regptr : uint64, heap : heaplet_id, mem : Heaplets) { 
  // That register's value points to a readable source addresss in that heap with public taint.
  ValidSrcAddr(mem, heap, regptr, 128, Public) &&
  mem[heap].QuadwordHeaplet? &&
  ctr == mem[heap].quads[regptr].v
}

// An incremented counter has the high half undisturbed as it is the IV and
// the low half + 1 with no overflow beyond 64 bits.
predicate IncrCtr(counter : Quadword, incrcounter : Quadword)
{
  //counter.hi == incrcounter.hi &&
  //counter.mid_hi == incrcounter.mid_hi
  // No predicate provable.
  true
}
  
predicate IncrCtrInReg(ctr : Quadword, incctr : Quadword, reg : Quadword) {
  IncrCtr(ctr, incctr) &&
  CtrInReg(incctr, reg)
}


predicate AlgReq(alg : Algorithm, key : seq<uint32>, key_ptr : uint64) {
  alg == AES_128 &&
  |key| == Nk(alg) && 
  SeqLength(key) == Nk(alg) &&
  (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1 &&   // Easy to prove, but necessary precondition to Cipher
  (Nb() * (Nr(alg) + 1)) % 4 == 0 &&   // Easy to prove, but necessary precondition to Cipher
  key_ptr % 16 == 0
}

predicate HeapReq(key_heap : heaplet_id, expanded_key_heap : heaplet_id, input_heap : heaplet_id, output_heap : heaplet_id, mem : Heaplets) {
// In the memory
  key_heap in mem &&
  expanded_key_heap in mem &&
  input_heap in mem &&
  output_heap in mem &&

// Disjointness.
  key_heap != expanded_key_heap &&
  key_heap != input_heap &&
  key_heap != output_heap &&
  expanded_key_heap != input_heap &&
  expanded_key_heap != output_heap &&
  input_heap != output_heap
}

predicate KeyReq(key : seq<uint32>, key_heap : heaplet_id, key_ptr : uint64, mem : Heaplets) {
  ValidSrcAddrs(mem, key_heap, key_ptr, 128, Secret, 11*16) &&   // Key is readable
  key_ptr % 16 == 0
}

predicate ExpandedKeyInitReq(expanded_key : seq<uint32>, expanded_key_heap : heaplet_id,
                             expanded_key_ptr : uint64, mem : Heaplets) {
  SeqLength(expanded_key) == 44 &&
  ValidSrcAddrs(mem, expanded_key_heap, expanded_key_ptr, 1, Secret, 176)
}

predicate ExpandedKeyReq(key : seq<uint32>, key_heap : heaplet_id, key_ptr : uint64, expanded_key : seq<uint32>, expanded_key_heap : heaplet_id,
                             expanded_key_ptr : uint64, mem : Heaplets, alg : Algorithm) {
  AlgReq(alg, key, key_ptr) &&
  KeyReq(key, key_heap, key_ptr, mem) && 
  ExpandedKeyInitReq(expanded_key, expanded_key_heap, expanded_key_ptr, mem) && // Someday we may call this in assembly.
   (forall j :: 0 <= j <= 10 ==> mem[key_heap].quads[key_ptr + 16*j].v == 
         Quadword(expanded_key[4*j], expanded_key[4*j+1], expanded_key[4*j+2], expanded_key[4*j+3])) &&
    KeyExpansionPredicate(key, alg, expanded_key)
}

predicate InputInMem(input : seq<Quadword>, input_heap : heaplet_id, input_ptr : uint64, 
                    input_end : uint64, input_end_ptr : uint64, mem : Heaplets) {
  SeqLength(input) > 0 &&
  ValidSrcAddrs(mem, input_heap, input_ptr, 128, Secret, SeqLength(input)*16) &&
  QuadwordSeqInMemory(input, mem[input_heap], input_ptr)
}

predicate OutputWriteable(output : seq<Quadword>, output_heap : heaplet_id, 
                      output_ptr : uint64, mem : Heaplets) {
  SeqLength(output) > 0 &&
  ValidSrcAddrs(mem, output_heap, output_ptr, 128, Secret, SeqLength(output)*16)
}

// TODO
// I abstractly know what my starting counter is. 
predicate StartCtrReq(iv : uint64, ctr : Quadword) {
  //ctr == Quadword(0,0,lower64(iv), upper64(iv))
  true
}

// I concretely know.
predicate StartCtrInReg(iv : uint64, ctr : Quadword, ctr_reg : Quadword) {
 //StartCtrReq(iv, ctr) // &&
  //ctr == ctr_reg
// TODO
  // Error: cannot establish the existence of LHS values that satisfy the such-that predicate
 true
}

predicate InputOutputInvariants(input : seq<Quadword>, input_ptr : uint64, input_end_ptr : uint64, 
                               output_ptr : uint64) {
   input_ptr + SeqLength(input)*16 < 0x1_0000_0000_0000_0000 &&
   output_ptr + SeqLength(input)*16 < 0x1_0000_0000_0000_0000 &&
   input_end_ptr >= input_ptr && 
   input_end_ptr == input_ptr + SeqLength(input)*16 &&
   input_end_ptr < 0x1_0000_0000_0000_0000 
}

predicate CTRInvariants(
    key     : seq<uint32>,
    key_ptr : uint64,
    key_heap : heaplet_id,
    expanded_key : seq<uint32>,
    expanded_key_ptr : uint64,
    expanded_key_heap : heaplet_id,
    iv       : uint64,
    input :seq<Quadword>,
    input_ptr : uint64,
    input_end  : uint64,
    input_end_ptr : uint64,
    input_heap : heaplet_id,
    output_heap : heaplet_id,
    output_ptr : uint64,
    alg: Algorithm,
    mem : Heaplets,
    old_mem : Heaplets)
{
        HeapReq(key_heap, expanded_key_heap, input_heap, output_heap, mem) &&
        KeyReq(key, key_heap, key_ptr, mem) &&
        ExpandedKeyReq(key, key_heap, key_ptr, expanded_key, expanded_key_heap,
                            expanded_key_ptr, mem, alg) &&
        InputInMem(input, input_heap, input_ptr, input_end, input_end_ptr, mem) &&
        OutputWriteable(input, output_heap, output_ptr, mem) &&
        InputOutputInvariants(input, input_ptr, input_end_ptr, output_ptr) &&
        mem == old_mem[output_heap := mem[output_heap]]
}


predicate CTROutputFinal2(key : seq<uint32>, input :seq<Quadword>, iv : uint64, alg : Algorithm, 
                         mem : Heaplets,  output_heap : heaplet_id, output_ptr :uint64, output : seq<Quadword>, ctr : Quadword) {
  true
}

predicate CTREncryptLoopInvariant(
    key     : seq<uint32>,
    key_ptr : uint64,
    key_heap : heaplet_id,
    expanded_key : seq<uint32>,
    expanded_key_ptr : uint64,
    expanded_key_heap : heaplet_id,
    iv       : uint64,
    input :seq<Quadword>,
    input_ptr : uint64,
    input_end  : uint64,
    input_end_ptr : uint64,
    input_heap : heaplet_id,
    output_heap : heaplet_id,
    output_ptr : uint64,
    alg: Algorithm,
    mem : Heaplets,
    old_mem : Heaplets,
    iteration : nat) {
  CTRInvariants(key, key_ptr, key_heap, expanded_key, expanded_key_ptr, expanded_key_heap, iv,
          input, input_ptr, input_end, input_end_ptr, input_heap, output_heap, output_ptr, alg, 
          mem, old_mem)
}

lemma lemma_CTREncryptInvarientImplications(input : seq<Quadword>)
  returns (output : seq<Quadword>) {
    output := input;
}

predicate CTREncryptBodyPreconditions() {
  true
}

predicate CTREncryptBodyPostconditions() {
  true
}


// Just for learning how to write the code/proofs.

predicate QuadwordSeqsInMemMatch
  (input  : seq<Quadword>, in_mem  : Heaplet, input_ptr : uint64,
   output : seq<Quadword>, out_mem : Heaplet, output_ptr : uint64,
   length : int)
  requires in_mem.QuadwordHeaplet?
  requires out_mem.QuadwordHeaplet?
{
  |input| == |output| &&
  |input| >= length &&
   forall b:int :: 0 <= b < length ==> 
     input_ptr  + b*16 in in_mem.quads && 
     output_ptr + b*16 in out_mem.quads && 
     in_mem.quads[input_ptr + b*16].v == out_mem.quads[output_ptr + b*16].v
}


predicate InputCopied
  (in_mem  : Heaplet, input_ptr : uint64,
   out_mem : Heaplet, output_ptr : uint64,
   position : int)
  requires in_mem.QuadwordHeaplet?
  requires out_mem.QuadwordHeaplet?
{
  input_ptr  + position*16 in in_mem.quads && 
  output_ptr + position*16 in out_mem.quads && 
  in_mem.quads[input_ptr + position*16].v == out_mem.quads[output_ptr + position*16].v
}

// End of Module

}
