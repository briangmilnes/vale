/*

	Rebuild specifications with the concept of a Region and a pointer within a region.

*/


include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x86/def.s.dfy"
include "../../arch/x86/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

include "regions.base.dfy"

module regionsdfy {

import opened types_s
import opened x86_def_s
import opened x86_vale_i
import opened dafny_wrappers_i
import opened regionsbasedfy

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

predicate WritesRegPtrs32(mem : Heaplets, id : heaplet_id, base : nat, size : nat, 
                          taint : taint, 
                         ptr : nat, off : nat, count : nat, v : seq<uint32>)
 requires |v| == size;
 requires off + count <= size;
{
  ValidDstRegPtr32(mem, id, base, size, ptr, off) && 
   forall i : nat :: 0 <= i < count ==>
    addr32(ptr, i) in mem[id].words &&
    mem[id].words[addr32(ptr, i)].t == taint &&
    mem[id].words[addr32(ptr, i)].v == v[off+i]
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

lemma lemma_addr32_src(src : int)
  ensures forall off : int :: addr32(src,off) == addr32(src + 4 * 1, off - 1);
{
}

/*
lemma lemma_add32()
  ensures forall src : int :: forall off : int :: addr32(src,off) == addr32(src + 4 * off, off - 1);
{
  forall src : int 
    ensures  forall off : int :: addr32(src,off) == addr32(src + 4 * off, off - 1);
 {
  forall off : nat 
    ensures addr32(src,off) == addr32(src + 4 * off, off - 1);
  {
    assert addr32(src, off) == src + 4 * off;
    assert addr32(src + 4 * off, off - 1) == (src + 4 * off) + 4 * (off - 1);
    assert (src + 4 * off) + 4 * (off - 1) == 
  }
 }
}
*/
}
