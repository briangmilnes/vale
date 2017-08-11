include "../../lib/util/types.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"

// So I don't have to compile as much, this is included in regions.dfy.
module regions64 {

import opened types_s
import opened x64_def_s
import opened x64_vale_i

// Sometimes you want to tell vale that an operater is a register when not using
// registers names. 
predicate IsOReg (r : operand) {r.OReg?}

// And that you have n distinct ones.
predicate DistinctORegs2(r1 : operand, r2 : operand) {
  r1.OReg? && r2.OReg? && r1 != r2
}

predicate DistinctORegs3(r1 : operand, r2 : operand, r3: operand) {
  r1.OReg? && r2.OReg? && r3.OReg?
  && r1 != r2 && r1 != r3 && r2 != r3
}

function addr64(base:int, i:int):int { base + 8 * i }

// This lemma has been useful while proving things but Vale seems to just prove this as needed now.
lemma lemma_addr64_off(off : int)
  ensures forall src : int :: addr64(src,off) == addr64(src + 8 * off, 0);
{
}

// A region concept.
predicate ValidSrcReg64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
{
  addr64(base, size) < 0x1_0000_0000_0000_0000 &&
  id in mem &&
  mem[id].Heaplet64? &&
  forall i : nat :: 0 <= i < size ==>
    addr64(base, i) in mem[id].mem64 && 
    mem[id].mem64[addr64(base, i)].t == taint
}

predicate ValidDstReg64(mem : Heaplets, id : heaplet_id, base : nat, size : nat)
{
  addr64(base, size) < 0x1_0000_0000_0000_0000 &&
  id in mem &&
  mem[id].Heaplet64? &&
  forall i : nat :: 0 <= i < size ==>
    addr64(base, i) in mem[id].mem64 
}

// Lemmas to double check things, but hopefully most proof will go through without them.

lemma lemma_ValidSrcReg64__ValidDstReg64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidSrcReg64(mem, id, base, size, taint);
  ensures  ValidDstReg64(mem, id, base, size);
{
}

lemma lemma_ValidSrcReg64_SubReg(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidSrcReg64(mem, id, base, size, taint);
  ensures  forall sz : nat :: sz < size ==> ValidSrcReg64(mem, id, base, sz, taint);
{
}

lemma lemma_ValidDstReg64_SubReg(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidDstReg64(mem, id, base, size);
  ensures  forall sz : nat :: sz < size ==> ValidDstReg64(mem, id, base, sz);
{
}


// A pointer within a region, ptr is an actual ptr not an offset.
predicate ValidSrcRegPtr64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
{
  ValidSrcReg64(mem, id, base, size, taint) &&
  0 <= off < size &&
  ptr == addr64(base, off)
}

predicate ValidDstRegPtr64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, ptr : nat, off : nat)
{
  ValidDstReg64(mem, id, base, size) &&
  0 <= off < size &&
  ptr == addr64(base, off)
}

lemma lemma_ValidSrcRegPtr64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
  requires ValidSrcRegPtr64(mem, id, base, size, taint, ptr, off);
  ensures addr64(ptr, 0) in mem[id].mem64
{
}

lemma lemma_ValidSrcRegPtr64__ValidDstRegPtr64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
  requires ValidSrcRegPtr64(mem, id, base, size, taint, ptr, off);
  ensures  ValidDstRegPtr64(mem, id, base, size, ptr, off);
{
}

// At each write of a loop from a base register, ptr is baseoffset away and then the instruction
// can dereference from the ptr.
predicate ValidSrcRegPtrs64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, baseoff : nat, ptroff : nat)
{
  ValidSrcReg64(mem, id, base, size, taint) &&
  0 <= baseoff + ptroff < size &&
  ptr == addr64(base, baseoff) &&
// I'm throwing in this equality in because it makes the proofs work.
  addr64(ptr,ptroff) == addr64(base, baseoff + ptroff) 
}

predicate ValidDstRegPtrs64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, ptr : nat, baseoff : nat, ptroff : nat)
{
  ValidDstReg64(mem, id, base, size) &&
  0 <= baseoff + ptroff < size && 
  ptr == addr64(base, baseoff) &&
// I'm throwing in this equality in because it makes the proofs work.
  addr64(ptr,ptroff) == addr64(base, baseoff + ptroff)
}

// Just showing that Vale can prove these without calling lemmas.
lemma lemma_ValidSrcRegPtrs64__ValidDstRegPtrs64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs64(mem, id, base, size, taint, ptr, off, adds);
  ensures  ValidDstRegPtrs64(mem, id, base, size, ptr, off, adds);
{
}

lemma lemma_ValidSrcRegsPtrs64__subrange(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs64(mem, id, base, size, taint, ptr, off, adds);
  ensures forall i : nat :: 0 <= i <= adds ==> ValidSrcRegPtrs64(mem, id, base, size, taint, ptr, off, i);
{
}

lemma lemma_ValidSrcRegsPtrs64__ValidSrcRegsPtr64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs64(mem, id, base, size, taint, ptr, off, adds);
  ensures forall i : nat :: 0 <= i <= adds ==> ValidSrcRegPtr64(mem, id, base, size, taint, addr64(ptr,i), off + i);
{
}

predicate OnlyWritesReg64(old_mem : Heaplets, mem : Heaplets, id : heaplet_id, base : nat, size : nat)
{
  id in mem &&
  mem[id].Heaplet64? &&
  id in old_mem &&
  old_mem[id].Heaplet64? &&
  // I did not add any address space.
  (forall i :: i < 0 || i >= size ==>
   addr64(base, i) in mem[id].mem64 ==> addr64(base, i) in old_mem[id].mem64) &&
  // I did not modify anything else but my target.
  (forall i :: i < 0 || i >= size ==>
      addr64(base, i) in mem[id].mem64 ==> 
       mem[id].mem64[addr64(base, i)] == old_mem[id].mem64[addr64(base, i)])
}


predicate OnlyHeapletChanged(old_mem : Heaplets, mem : Heaplets, id : heaplet_id) 
{
  id in mem &&
  mem[id].Heaplet64? &&
  id in old_mem &&
  old_mem[id].Heaplet64? &&
  mem == old_mem[id := mem[id]]
}

// In this region, I have written up to index elements.
predicate WritesReg64(mem : Heaplets, id : heaplet_id, base : nat, size : nat, 
                      wrote: nat, taint : taint, v : seq<uint64>)
 requires |v| == size;                    // Should this be in the prediate?
{
  wrote <= size &&
  ValidDstReg64(mem, id, base, size) && // Should this be a requires?
  forall i : nat :: 0 <= i < wrote ==>
    addr64(base, i) in mem[id].mem64 &&
    mem[id].mem64[addr64(base, i)].t == taint &&
    mem[id].mem64[addr64(base, i)].v == v[i]
}

// Loops with ValidXRegPtrsY require one deduction that Vale does not automatically prove for fixed n.

lemma lemma_regdiff_loop_ge(endptr : nat, iptr : nat, bytes : nat)
    requires  2 <= bytes <= 32;
    requires  endptr >= iptr;
    requires (endptr - iptr) % bytes == 0;
    ensures  (endptr - iptr) > 0 ==> (endptr - iptr) >= bytes;
{
}

// Bryan, what's the forall version of this?
lemma lemma_regdiff_loop_ge_uint64(endptr : nat, iptr : nat, uint64s : nat)
    requires  1 <= uint64s <= 4;
    requires  endptr >= iptr;
    requires (endptr - iptr) % (uint64s * 8) == 0;
    ensures  (endptr - iptr) > 0 ==> (endptr - iptr) >= (uint64s * 8);
{
  if (uint64s == 1) {
    lemma_regdiff_loop_ge(endptr,iptr, 8);
  } else if (uint64s == 2) {
    lemma_regdiff_loop_ge(endptr,iptr, 16);
  } else if (uint64s == 3) {
    lemma_regdiff_loop_ge(endptr,iptr, 24);
  } else {
    lemma_regdiff_loop_ge(endptr,iptr, 32);
  }
}

}




