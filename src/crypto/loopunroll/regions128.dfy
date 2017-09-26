include "../../lib/util/types.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"

// So I don't have to compile as much, this is included in regions.dfy.
module regions128 {

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

predicate DistinctORegs6(r1 : operand, r2 : operand, r3: operand, r4 : operand, r5 : operand, r6 : operand) {
  r1.OReg? && r2.OReg? && r3.OReg? && r4.OReg? && r5.OReg? && r6.OReg? &&
  r1 != r2 && r1 != r3 && r1 != r4 && r1 != r5 && r1 != r6 &&
  r2 != r3 && r2 != r4 && r2 != r5 && r2 != r6 &&
  r3 != r4 && r3 != r5 && r3 != r6 &&
  r4 != r5 && r4 != r6 &&
  r5 != r6
}

predicate DistinctORegs7(r1 : operand, r2 : operand, r3: operand, r4 : operand, r5 : operand, r6 : operand, r7 : operand) {
  r1.OReg? && r2.OReg? && r3.OReg? && r4.OReg? && r5.OReg? && r6.OReg? && r7.OReg? &&
  r1 != r2 && r1 != r3 && r1 != r4 && r1 != r5 && r1 != r6 && r1 != r7 &&
  r2 != r3 && r2 != r4 && r2 != r5 && r2 != r6 && r2 != r7 &&
  r3 != r4 && r3 != r5 && r3 != r6 && r3 != r7 &&
  r4 != r5 && r4 != r6 && r4 != r7 &&
  r5 != r6 && r5 != r7 &&
  r6 != r7
}

function addr128(base:int, i:int):int { base + 16 * i }

// This lemma has been useful while proving things but Vale seems to just prove this as needed now.
lemma lemma_addr128_off(off : int)
  ensures forall src : int :: addr128(src,off) == addr128(src + 16 * off, 0);
{
}

// A region concept.
predicate ValidSrcReg128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
{
  addr128(base, size) < 0x1_0000_0000_0000_0000 &&
  id in mem &&
  mem[id].QuadwordHeaplet? &&
  forall i : nat :: 0 <= i < size ==>
    addr128(base, i) in mem[id].quads && 
    mem[id].quads[addr128(base, i)].t == taint
}

predicate ValidDstReg128(mem : Heaplets, id : heaplet_id, base : nat, size : nat)
{
  addr128(base, size) < 0x1_0000_0000_0000_0000 &&
  id in mem &&
  mem[id].QuadwordHeaplet? &&
  forall i : nat :: 0 <= i < size ==>
    addr128(base, i) in mem[id].quads 
}

// Lemmas to double check things, but hopefully most proof will go through without them.

lemma lemma_ValidSrcReg128__ValidDstReg128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidSrcReg128(mem, id, base, size, taint);
  ensures  ValidDstReg128(mem, id, base, size);
{
}

lemma lemma_ValidSrcReg128_SubReg(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidSrcReg128(mem, id, base, size, taint);
  ensures  forall sz : nat :: sz < size ==> ValidSrcReg128(mem, id, base, sz, taint);
{
}

lemma lemma_ValidDstReg128_SubReg(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidDstReg128(mem, id, base, size);
  ensures  forall sz : nat :: sz < size ==> ValidDstReg128(mem, id, base, sz);
{
}

// A pointer within a region, ptr is an actual ptr not an offset.
predicate ValidSrcRegPtr128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
{
  ValidSrcReg128(mem, id, base, size, taint) &&
  0 <= off < size &&
  ptr == addr128(base, off)
}

predicate ValidDstRegPtr128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, ptr : nat, off : nat)
{
  ValidDstReg128(mem, id, base, size) &&
  0 <= off < size &&
  ptr == addr128(base, off)
}

lemma lemma_ValidSrcRegPtr128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
  requires ValidSrcRegPtr128(mem, id, base, size, taint, ptr, off);
  ensures addr128(ptr, 0) in mem[id].quads
{
}

lemma lemma_ValidSrcRegPtr128__ValidDstRegPtr128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
  requires ValidSrcRegPtr128(mem, id, base, size, taint, ptr, off);
  ensures  ValidDstRegPtr128(mem, id, base, size, ptr, off);
{
}

// At each write of a loop from a base register, ptr is baseoffset away and then the instruction
// can dereference from the ptr.
predicate ValidSrcRegPtrs128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, baseoff : nat, ptroff : nat)
{
  ValidSrcReg128(mem, id, base, size, taint) &&
  0 <= baseoff + ptroff < size &&
  ptr == addr128(base, baseoff) &&
// I'm throwing in this equality in because it makes the proofs work.
  addr128(ptr,ptroff) == addr128(base, baseoff + ptroff) 
}

predicate ValidDstRegPtrs128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, ptr : nat, baseoff : nat, ptroff : nat)
{
  ValidDstReg128(mem, id, base, size) &&
  0 <= baseoff + ptroff < size && 
  ptr == addr128(base, baseoff) &&
// I'm throwing in this equality in because it makes the proofs work.
  addr128(ptr,ptroff) == addr128(base, baseoff + ptroff)
}

// Just showing that Vale can prove these without calling lemmas.
lemma lemma_ValidSrcRegPtrs128__ValidDstRegPtrs128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs128(mem, id, base, size, taint, ptr, off, adds);
  ensures  ValidDstRegPtrs128(mem, id, base, size, ptr, off, adds);
{
}

lemma lemma_ValidSrcRegsPtrs128__subrange(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs128(mem, id, base, size, taint, ptr, off, adds);
  ensures forall i : nat :: 0 <= i <= adds ==> ValidSrcRegPtrs128(mem, id, base, size, taint, ptr, off, i);
{
}

lemma lemma_ValidSrcRegsPtrs128__ValidSrcRegsPtr128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs128(mem, id, base, size, taint, ptr, off, adds);
  ensures forall i : nat :: 0 <= i <= adds ==> ValidSrcRegPtr128(mem, id, base, size, taint, addr128(ptr,i), off + i);
{
}

predicate OnlyWritesReg128(old_mem : Heaplets, mem : Heaplets, id : heaplet_id, base : nat, size : nat)
{
  id in mem &&
  mem[id].QuadwordHeaplet? &&
  id in old_mem &&
  old_mem[id].QuadwordHeaplet? &&
  // I did not add any address space.
  (forall i :: i < 0 || i >= size ==>
   addr128(base, i) in mem[id].quads ==> addr128(base, i) in old_mem[id].quads) &&
  // I did not modify anything else but my target.
  (forall i :: i < 0 || i >= size ==>
      addr128(base, i) in mem[id].quads ==> 
       mem[id].quads[addr128(base, i)] == old_mem[id].quads[addr128(base, i)])
}


predicate OnlyQuadwordHeapletChanged(old_mem : Heaplets, mem : Heaplets, id : heaplet_id) 
{
  id in mem &&
  mem[id].QuadwordHeaplet? &&
  id in old_mem &&
  old_mem[id].QuadwordHeaplet? &&
  mem == old_mem[id := mem[id]]
}

// In this region, I have written up to index elements.
predicate WritesReg128(mem : Heaplets, id : heaplet_id, base : nat, size : nat, 
                      wrote: nat, taint : taint, v : seq<Quadword>)
 requires |v| == size;                    // Should this be in the prediate?
{
  wrote <= size &&
  ValidDstReg128(mem, id, base, size) && // Should this be a requires?
  forall i : nat :: 0 <= i < wrote ==>
    addr128(base, i) in mem[id].quads &&
    mem[id].quads[addr128(base, i)].t == taint &&
    mem[id].quads[addr128(base, i)].v == v[i]
}

// Loops with ValidXRegPtrsY require one deduction that Vale does not automatically prove for fixed n.

lemma lemma_regdiff_loop_ge(endptr : nat, iptr : nat, bytes : nat)
    requires  2 <= bytes <= 128;
    requires  endptr >= iptr;
    requires (endptr - iptr) % bytes == 0;
    ensures  (endptr - iptr) > 0 ==> (endptr - iptr) >= bytes;
{
}

lemma lemma_regdiff_loop_ge_uint128(endptr : nat, iptr : nat, uint128s : nat)
    requires  1 <= uint128s <= 4;
    requires  endptr >= iptr;
    requires (endptr - iptr) % (uint128s * 16) == 0;
    ensures  (endptr - iptr) > 0 ==> (endptr - iptr) >= (uint128s * 16);
{
  if (uint128s == 1) {
    lemma_regdiff_loop_ge(endptr,iptr, 16);
  } else if (uint128s == 2) {
    lemma_regdiff_loop_ge(endptr,iptr, 32);
  } else if (uint128s == 3) {
    lemma_regdiff_loop_ge(endptr,iptr, 48);
  } else {
    lemma_regdiff_loop_ge(endptr,iptr, 64);
  }
}

}




