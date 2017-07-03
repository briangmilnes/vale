include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

module LoopUnrollModule {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i

lemma lemma_BitwiseAdd64()
    ensures  forall x:uint64, y:uint64 :: x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
    ensures  forall x:uint64, y:uint64 :: x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
    ensures  forall x:uint64 :: BitwiseAdd64(x, 0) == x;
{
    reveal_BitwiseAdd64();
}

predicate ValidDstAddr64(h:Heaplets, id:heaplet_id, addr:int)
{
  id in h  && h[id].Heaplet64?   && addr in h[id].mem64
}

predicate ValidSrcAddr64(h:Heaplets, id:heaplet_id, addr:int, taint:taint) 
{
 id in h  && h[id].Heaplet64?   && addr in h[id].mem64 && h[id].mem64[addr].t == taint
}

lemma lemma_ValidDstAddr64(mem:Heaplets, id:heaplet_id, addr : uint64)
      requires ValidDstAddr64(mem, id, addr);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures addr in mem[id].mem64;
{
}

lemma lemma_ValidSrcAddr64(mem:Heaplets, id:heaplet_id, addr : uint64, t:taint)
      requires ValidSrcAddr64(mem, id, addr, t); 
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures addr in mem[id].mem64;
      ensures addr in mem[id].mem64;
      ensures mem[id].mem64[addr].t == t;
      ensures ValidDstAddr64(mem, id, addr);
{
}

predicate Mem64ChangedOnlyAtWith(mem: Heaplets, old_mem : Heaplets, id : heaplet_id, 
             addr : uint64, off : uint64, value : uint64, t : taint)
    requires ValidSrcAddr64(old_mem, id, addr + off, Public); 
{
  mem == old_mem[id := old_mem[id].(mem64 := old_mem[id].mem64[addr + off := Heaplet64Entry(value, t)])]
} 

}
