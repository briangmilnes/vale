include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "aes.s.dfy"

// Bryan suggests that I use quadwords uniformally and
// convert into unit64 and back as needed. What would
//that look like?


module CTRModuleClean {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened AESModule

// I need a cleaner version of specifications in which a ghost is
// used for each concrete value and the output of each routine.
// The cryptographic types we are using are:
// key, expanded_key, block, block sequence and counter.
// They are either in memory or in a register.
// We specify the expanded key in bytes all else in quadwords.
// 

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

// Memory

// What does it mean to be pointed at by a register?
// ValidDstAddr really with the appropriate taint in memory.
predicate InMem(athing : uint128, regptr : uint128, heap : heaplet_id, taint : taint) 
{
  true
}

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

//IncrCtrInMem(ctr, incr ctr, reg ptr, heap, taint, mem).

// Key
//KeyInReg(key, reg);
//KeyInMem(key, reg ptr, heap, mem);

// Expanded Key
//ExpandedKey(key, alg, w);
//ExpandedKeyInMem(key, alg, w, reg ptr, heap, mem);

// Input
//InpInReg(input, reg, heap, taint, mem)
//InpInMem(input, reg ptr, heap, taint, mem) // 128 bits

// Output
//OutInReg(output, reg, heap, taint, mem)
//OutInMem(output, reg ptr, heap, taint, mem) // 128 bits

// Encr - Decryption 
//EncReg(input, input reg, output, output reg, key, key reg, exp key, exp key reg ptr, ctr, ctr reg, alg, taint, mem)
//DecReg(input, input reg, output, output reg, key, key reg, exp key, exp key reg ptr, ctr, ctr reg, alg, taint, mem)

// And an in memory sequence version.


// Concrete descriptions of memory.

// Memory

// What does it mean to be pointed at by a register?
//predicate InMem(regptr : uint64, heap : heaplet_id, size : int, taint : Taint, mem : Heaplets)
//{
//  ValidSrcAddr(mem, heap, regptr, size, taint)
//}

// What does it mean to be a value in a register?
//predicate InReg64(regptr : uint64, taint : Taint)
//{
//  true
//}
//
//predicate InReg128(regptr : uint64, taint : Taint)
//{
//  true
//}
//
//predicate CtrInReg(regptr : uint128, taint : Taint)
//{
// InReg128(regptr, taint)
//}
//
//predicate CtrInMem(regptr : uint128, taint : Taint)
//{
// InReg128(regptr, taint)
//}
//

// Memory is unchanged except in this heap and from this pointer/range.
//predicate SeqQuadwordsMatchesMemory(s:seq<Quadword>, mem:Heaplet, s_ptr:uint64)
//    requires mem.QuadwordHeaplet?
//{
//    forall b:int :: 0 <= b < |s| ==> s_ptr + b*16 in mem.quads 
//                                      && mem.quads[s_ptr + b*16].v == s[b]
//}

}