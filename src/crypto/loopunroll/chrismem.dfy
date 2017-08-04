include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x86/def.s.dfy"
include "../../arch/x86/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

include "chrismem.base.dfy"

module chrismemdfy {

import opened types_s
import opened x86_def_s
import opened x86_vale_i
import opened dafny_wrappers_i
import opened chrismembasedfy
 

// Put Chris MemFoo into predicates, use ' just to be clear.

predicate ValidSrcAddrs32'(mem : Heaplets, id : heaplet_id, base : int, size : nat, taint : taint)
{
  base + size * 4 < 0x1_0000_0000 &&
  id in mem &&
  mem[id].WordHeaplet? &&
  forall i :: 0 <= i < size ==>
    addr32(base, i) in mem[id].words && 
    mem[id].words[addr32(base, i)].t == taint
}

// Thinking about base, offset and size.
//function addr32'(base:int, off : int, i : int ):int { base + 4 * off + 4 * i }
//
//predicate ValidSrcAddrs32'(mem : Heaplets, id : heaplet_id, base : int, off : int, size : nat, taint : taint)
//{
//  base + size * 4 < 0x1_0000_0000 &&
//  id in mem &&
//  mem[id].WordHeaplet? &&
//  forall i :: 0 <= i < size ==>
//    addr32'(base, off, i) in mem[id].words && 
//    mem[id].words[addr32(base, i)].t == taint
//}

predicate ValidDstAddrs32'(mem : Heaplets, id : heaplet_id, base : int, size : nat)
{
  base + size * 4 < 0x1_0000_0000 &&
  id in mem &&
  mem[id].WordHeaplet? &&
  forall i :: 0 <= i < size ==>
    addr32(base, i) in mem[id].words 
}

predicate OnlyWritesAddrs32(old_mem : Heaplets, mem : Heaplets, id : heaplet_id, base : int, size : nat)
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


predicate WritesAddrs32(mem : Heaplets, id : heaplet_id,
                        base : int, size : nat, taint : taint, v : seq<uint32>)
 requires |v| == size;                    // Should this be in the prediate?
{
  ValidDstAddrs32'(mem, id, base, size) && // Should this be a requires?
  forall i :: 0 <= i < size ==>
    addr32(base, i) in mem[id].words &&
    mem[id].words[addr32(base, i)].t == taint &&
    mem[id].words[addr32(base, i)].v == v[i]
}

// Below here should go in an application.
predicate IsOReg (r : operand) {r.OReg?}

function Copy32(mem : Heaplets, id: heaplet_id, base : int, size: int, i : nat) : uint32
 requires 0 <= i < size;
 requires ValidDstAddrs32'(mem, id, base, size);
{
  mem[id].words[(addr32(base, i))].v
}

// Question: should this have taint?
// For an address range of base and size, generate the prefix subsequence of count elements.
function Copy32Seq(mem : Heaplets, id: heaplet_id, base : int, size : nat, count : nat, taint : taint) : seq<uint32>
 requires ValidSrcAddrs32'(mem, id, base, size, taint);
 requires 0 <= count <= size;
 ensures |Copy32Seq(mem, id, base, size, count, taint)| == count; 
// Doing this here at the function definition is CRITICAL.
 ensures forall i : nat :: 0 <= i < count ==> 
         Copy32Seq(mem, id, base, size, count, taint)[i] == Copy32(mem, id, base, size, i);
{
  if (count == 0) then
    []
  else 
    Copy32Seq(mem, id, base, size, count - 1, taint) + [Copy32(mem, id, base, size, count - 1)]
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
