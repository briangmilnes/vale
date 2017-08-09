include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x86/def.s.dfy"
include "../../arch/x86/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

// Just so I don't have to recompile much.
module regionsbasedfy {

import opened types_s
import opened x86_def_s
import opened x86_vale_i
import opened dafny_wrappers_i

lemma lemma_addr32_off(off : int)
  ensures forall src : int :: addr32(src,off) == addr32(src + 4 * off, 0);
{
}

function addr32(base:int, i:int):int { base + 4 * i }

// A region concept.
predicate ValidSrcReg32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
{
  addr32(base, size) < 0x1_0000_0000 &&
  id in mem &&
  mem[id].WordHeaplet? &&
  forall i : nat :: 0 <= i < size ==>
    addr32(base, i) in mem[id].words && 
    mem[id].words[addr32(base, i)].t == taint
}

predicate ValidDstReg32(mem : Heaplets, id : heaplet_id, base : nat, size : nat)
{
  addr32(base, size) < 0x1_0000_0000 &&
  id in mem &&
  mem[id].WordHeaplet? &&
  forall i : nat :: 0 <= i < size ==>
    addr32(base, i) in mem[id].words 
}

// Lemmas to double check things, but hopefully most proof will go through without them.

lemma lemma_ValidSrcReg32__ValidDstReg32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidSrcReg32(mem, id, base, size, taint);
  ensures  ValidDstReg32(mem, id, base, size);
{
}

lemma lemma_ValidSrcReg32_SubReg(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidSrcReg32(mem, id, base, size, taint);
  ensures  forall sz : nat :: sz < size ==> ValidSrcReg32(mem, id, base, sz, taint);
{
}

lemma lemma_ValidDstReg32_SubReg(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint)
  requires ValidDstReg32(mem, id, base, size);
  ensures  forall sz : nat :: sz < size ==> ValidDstReg32(mem, id, base, sz);
{
}


// A pointer within a region, ptr is an actual ptr not an offset.
predicate ValidSrcRegPtr32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
{
  ValidSrcReg32(mem, id, base, size, taint) &&
  0 <= off < size &&
  ptr == addr32(base, off)
}

predicate ValidDstRegPtr32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, ptr : nat, off : nat)
{
  ValidDstReg32(mem, id, base, size) &&
  0 <= off < size &&
  ptr == addr32(base, off)
}

lemma lemma_ValidSrcRegPtr32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
  requires ValidSrcRegPtr32(mem, id, base, size, taint, ptr, off);
  ensures addr32(ptr, 0) in mem[id].words
{
}

lemma lemma_ValidSrcRegPtr32__ValidDstRegPtr32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat)
  requires ValidSrcRegPtr32(mem, id, base, size, taint, ptr, off);
  ensures  ValidDstRegPtr32(mem, id, base, size, ptr, off);
{
}

// At each write of a loop from a base register, ptr is baseoffset away and then the instruction
// can dereference from the ptr.
predicate ValidSrcRegPtrs32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, baseoff : nat, ptroff : nat)
{
  ValidSrcReg32(mem, id, base, size, taint) &&
  0 <= baseoff + ptroff < size &&
  ptr == addr32(base, baseoff) &&
// I'm throwing in this equality in because it makes the proofs work.
  addr32(ptr,ptroff) == addr32(base, baseoff + ptroff) 
}

predicate ValidDstRegPtrs32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, ptr : nat, baseoff : nat, ptroff : nat)
{
  ValidDstReg32(mem, id, base, size) &&
  0 <= baseoff + ptroff < size && 
  ptr == addr32(base, baseoff) &&
// I'm throwing in this equality in because it makes the proofs work.
  addr32(ptr,ptroff) == addr32(base, baseoff + ptroff)
}

// Just showing that Vale can prove these without calling lemmas.
lemma lemma_ValidSrcRegPtrs32__ValidDstRegPtrs32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs32(mem, id, base, size, taint, ptr, off, adds);
  ensures  ValidDstRegPtrs32(mem, id, base, size, ptr, off, adds);
{
}

lemma lemma_ValidSrcRegsPtrs32__subrange(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs32(mem, id, base, size, taint, ptr, off, adds);
  ensures forall i : nat :: 0 <= i <= adds ==> ValidSrcRegPtrs32(mem, id, base, size, taint, ptr, off, i);
{
}

lemma lemma_ValidSrcRegsPtrs32__ValidSrcRegsPtr32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, taint : taint, ptr : nat, off : nat, adds : nat)
  requires ValidSrcRegPtrs32(mem, id, base, size, taint, ptr, off, adds);
  ensures forall i : nat :: 0 <= i <= adds ==> ValidSrcRegPtr32(mem, id, base, size, taint, addr32(ptr,i), off + i);
{
}

predicate OnlyWritesReg32(old_mem : Heaplets, mem : Heaplets, id : heaplet_id, base : nat, size : nat)
{
  id in mem &&
  mem[id].WordHeaplet? &&
  id in old_mem &&
  old_mem[id].WordHeaplet? &&
  // I did not add any address space.
  (forall i :: i < 0 || i >= size ==>
   addr32(base, i) in mem[id].words ==> addr32(base, i) in old_mem[id].words) &&
  // I did not modify anything else but my target.
  (forall i :: i < 0 || i >= size ==>
      addr32(base, i) in mem[id].words ==> 
       mem[id].words[addr32(base, i)] == old_mem[id].words[addr32(base, i)])
}


predicate OnlyHeapletChanged(old_mem : Heaplets, mem : Heaplets, id : heaplet_id) 
{
  id in mem &&
  mem[id].WordHeaplet? &&
  id in old_mem &&
  old_mem[id].WordHeaplet? &&
  mem == old_mem[id := mem[id]]
}

// In this region, I have written up to index elements.
predicate WritesReg32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, 
                      index: nat, taint : taint, v : seq<uint32>)
 requires |v| == size;                    // Should this be in the prediate?
{
  index <= size &&
  ValidDstReg32(mem, id, base, size) && // Should this be a requires?
  forall i : nat :: 0 <= i < index ==>
    addr32(base, i) in mem[id].words &&
    mem[id].words[addr32(base, i)].t == taint &&
    mem[id].words[addr32(base, i)].v == v[i]
}

// Below here should go in an application.
predicate IsOReg (r : operand) {r.OReg?}

function Copy32(mem : Heaplets, id: heaplet_id, base : nat, size: int, i : nat) : uint32
 requires 0 <= i < size;
 requires ValidDstReg32(mem, id, base, size);
{
  mem[id].words[(addr32(base, i))].v
}

// Generate the whole sequence with this function that knows what the values are.

function Copy32Seq(mem : Heaplets, id: heaplet_id, base : nat, size : nat, count : nat) : seq<uint32>
 requires ValidDstReg32(mem, id, base, size);
 requires 0 <= count <= size;
 ensures |Copy32Seq(mem, id, base, size, count)| == count;
// Doing this here at the function definition is CRITICAL.
 ensures forall i : nat :: 0 <= i < count ==>
         Copy32Seq(mem, id, base, size, count)[i] == Copy32(mem, id, base, size, i);
{
  if (count == 0) then
    []
  else 
    Copy32Seq(mem, id, base, size, count - 1) + [Copy32(mem, id, base, size, count - 1)]
}

// Loops with ValidXRegPtrsY require one deduction that Vale does not automatically prove for fixed n.

lemma lemma_regdiff_loop_ge(endptr : nat, iptr : nat, bytes : nat)
    requires  2 <= bytes <= 16;
    requires  endptr >= iptr;
    requires (endptr - iptr) % bytes == 0;
    ensures  (endptr - iptr) > 0 ==> (endptr - iptr) >= bytes;
{
}

// Bryan, what's the forall version of this?
lemma lemma_regdiff_loop_ge_uint32(endptr : nat, iptr : nat, uint32s : nat)
    requires  1 <= uint32s <= 4;
    requires  endptr >= iptr;
    requires (endptr - iptr) % (uint32s * 4) == 0;
    ensures  (endptr - iptr) > 0 ==> (endptr - iptr) >= (uint32s * 4);
{
  if (uint32s == 1) {
    lemma_regdiff_loop_ge(endptr,iptr, 4);
  } else if (uint32s == 2) {
    lemma_regdiff_loop_ge(endptr,iptr, 8);
  } else if (uint32s == 3) {
    lemma_regdiff_loop_ge(endptr,iptr, 12);
  } else {
    lemma_regdiff_loop_ge(endptr,iptr, 16);
  }
}

}




