include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

module addrlogic {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i

// Unaligned 
predicate ValidDstUnAddr64(h:Heaplets, id:heaplet_id, addr:int)
{
  id in h  && 
  h[id].Heaplet64? && 
  addr in h[id].mem64
}

predicate ValidSrcUnAddr64(h:Heaplets, id:heaplet_id, addr:int, taint:taint) 
{
  id in h  && 
  h[id].Heaplet64? && 
  addr in h[id].mem64 &&
  h[id].mem64[addr].t == taint
}

lemma lemma_ValidDstUnAddr64(mem:Heaplets, id:heaplet_id, addr : uint64)
      requires ValidDstUnAddr64(mem, id, addr);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures addr in mem[id].mem64;
{
}

lemma lemma_ValidSrcUnAddr64(mem:Heaplets, id:heaplet_id, addr : uint64, t:taint)
      requires ValidSrcUnAddr64(mem, id, addr, t); 
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures addr in mem[id].mem64;
      ensures mem[id].mem64[addr].t == t;
      ensures ValidDstUnAddr64(mem, id, addr);
{
}

predicate ValidDstUnAddrs64(mem:Heaplets, id:heaplet_id, addr:int, count : nat)
 requires count > 0;
 requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
{
  id in mem &&
  mem[id].Heaplet64? &&
  forall i: nat :: 0 < i <= count  ==> addr + (i - 1) * 8 in mem[id].mem64 &&
  forall i : nat :: 0 < i <= count ==> ValidDstUnAddr64(mem, id, addr + (i - 1) * 8)
}

predicate ValidSrcUnAddrs64(mem:Heaplets, id:heaplet_id, addr:int, taint:taint, count : nat) 
 requires count > 0;
 requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
{
  id in mem &&
  mem[id].Heaplet64? &&
  forall i: nat :: 0 < i <= count  ==> addr + (i - 1) * 8 in mem[id].mem64 &&
  forall i : nat :: 0 < i <= count ==> ValidSrcUnAddr64(mem, id, addr + (i - 1) * 8, taint)
}

lemma lemma_ValidDstUnAddrs64(mem:Heaplets, id:heaplet_id, addr : uint64, count : nat)
      requires count > 0;
      requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
      requires ValidDstUnAddrs64(mem, id, addr, count);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures forall i : nat :: 0 < i <= count ==> addr + (i - 1) * 8  in mem[id].mem64;
      ensures forall i : nat :: 0 < i <= count ==> ValidDstUnAddr64(mem, id, addr + (i - 1) * 8);
{}

lemma lemma_ValidSrcUnAddrs64(mem:Heaplets, id:heaplet_id, addr : uint64, taint : taint, count : int)
      requires count > 0;
      requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
      requires ValidSrcUnAddrs64(mem, id, addr, taint, count);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures forall i : nat :: 0 < i <= count ==> addr + (i - 1) * 8  in mem[id].mem64;
      ensures forall i: nat ::  0 < i < count ==> ValidSrcUnAddr64(mem, id, addr + (i - 1) * 8, taint);
      ensures forall i : nat :: 0 < i <= count ==> ValidDstUnAddr64(mem, id, addr + (i - 1) * 8);
      ensures ValidDstUnAddrs64(mem, id, addr, count);
{}

// Aligned

predicate ValidDstAlAddr64(h:Heaplets, id:heaplet_id, addr:int)
{
  id in h  && 
  h[id].Heaplet64? && 
  addr in h[id].mem64 &&
  addr % 8 == 0
}

predicate ValidSrcAlAddr64(h:Heaplets, id:heaplet_id, addr:int, taint:taint) 
{
  id in h  && 
  h[id].Heaplet64? && 
  addr in h[id].mem64 &&
  h[id].mem64[addr].t == taint &&
  addr % 8 == 0
}

lemma lemma_ValidDstAlAddr64(mem:Heaplets, id:heaplet_id, addr : uint64)
      requires ValidDstAlAddr64(mem, id, addr);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures addr in mem[id].mem64;
      ensures addr % 8 == 0;
      ensures ValidDstUnAddr64(mem, id, addr);
{
}

lemma lemma_ValidSrcAlAddr64(mem:Heaplets, id:heaplet_id, addr : uint64, t:taint)
      requires ValidSrcAlAddr64(mem, id, addr, t); 
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures addr in mem[id].mem64;
      ensures addr % 8 == 0;
      ensures mem[id].mem64[addr].t == t;
      ensures ValidSrcUnAddr64(mem, id, addr, t); 
      ensures ValidDstAlAddr64(mem, id, addr);
      ensures ValidDstUnAddr64(mem, id, addr);
{
}

predicate ValidDstAlAddrs64(mem:Heaplets, id:heaplet_id, addr:int, count : nat)
 requires count > 0;
 requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
{
  id in mem &&
  mem[id].Heaplet64? &&
  addr % 8 == 0 &&
  forall i : nat :: 0 < i <= count ==> (addr + (i - 1) * 8) % 8 == 0 &&
  forall i : nat :: 0 < i <= count ==> addr + (i - 1) * 8 in mem[id].mem64 &&
  forall i : nat :: 0 < i <= count ==> ValidDstAlAddr64(mem, id, addr + (i - 1) * 8)
}

predicate ValidSrcAlAddrs64(mem:Heaplets, id:heaplet_id, addr:int, taint:taint, count : nat) 
 requires count > 0;
 requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
{
  id in mem &&
  mem[id].Heaplet64? &&
  addr % 8 == 0 &&
  forall i : nat :: 0 < i <= count ==> (addr + (i - 1) * 8) % 8 == 0 &&
  forall i : nat :: 0 < i <= count ==> addr + (i - 1) * 8 in mem[id].mem64 &&
  forall i : nat :: 0 < i <= count ==> ValidSrcAlAddr64(mem, id, addr + (i - 1) * 8, taint) &&
  forall i : nat :: 0 < i <= count ==> 
   (ValidSrcAlAddr64(mem, id, addr + (i - 1) * 8, taint) ==>
   mem[id].mem64[addr + (i - 1) * 8].t == taint)
}

lemma lemma_ValidDstAlAddrs64(mem:Heaplets, id:heaplet_id, addr : uint64, count : nat)
      requires count > 0;
      requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
      requires ValidDstAlAddrs64(mem, id, addr, count);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures forall i : nat :: 0 < i <= count ==> addr + (i - 1) * 8  in mem[id].mem64;
      ensures forall i : nat :: 0 < i <= count ==> ValidDstAlAddr64(mem, id, addr + (i - 1) * 8);
      ensures forall i : nat :: 0 < i <= count ==> ValidDstUnAddr64(mem, id, addr + (i - 1) * 8);
{}

lemma lemma_ValidSrcAlAddrs64(mem:Heaplets, id:heaplet_id, addr : uint64, taint : taint, count : int)
      requires count > 0;
      requires addr + (count - 1) * 8 < 0x1_0000_0000_0000_0000;
      requires ValidSrcAlAddrs64(mem, id, addr, taint, count);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures ValidDstAlAddrs64(mem, id, addr, count);
      ensures ValidDstUnAddrs64(mem, id, addr, count);
      ensures forall i : nat :: 0 < i <= count ==> addr + (i - 1) * 8  in mem[id].mem64;
      ensures forall i : nat :: 0 < i <= count ==> ValidSrcAlAddr64(mem, id, addr + (i - 1) * 8, taint);
      ensures forall i : nat :: 0 < i <= count ==> ValidSrcUnAddr64(mem, id, addr + (i - 1) * 8, taint);
      ensures forall i : nat :: 0 < i <= count ==> 
                (ValidSrcAlAddr64(mem, id, addr + (i - 1) * 8, taint) ==>
                 mem[id].mem64[addr + (i - 1) * 8].t == taint)
      ensures forall i : nat :: 0 < i <= count ==> ValidDstAlAddr64(mem, id, addr + (i - 1) * 8);
{
}

// OnlyUpdates


predicate OnlyUpdatesAddr64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, addr : uint64, taint:taint, v:uint64)
    requires ValidDstUnAddr64(old_mem, id, addr);
{
  mem == old_mem[id := old_mem[id].(mem64 := old_mem[id].mem64[addr := Heaplet64Entry(v, taint)])]
}

predicate RestUntouched64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, addr : uint64) 
  requires ValidDstUnAddr64(old_mem, id, addr);
{  
  // I don't delelete any heaplet.
  (forall nid : heaplet_id :: nid in old_mem ==> nid in mem) && 
  // I don't modify any other heaplet.
  (forall nid : heaplet_id :: nid in old_mem && nid != id ==> nid in mem && mem[nid] == old_mem[nid]) &&
  // mem[id] is still a Healplet64
  id in mem && mem[id].Heaplet64? &&
  // I only adjusted this one address in old_mem[id].
  (forall naddr : uint64 :: naddr != addr && naddr in old_mem[id].mem64 ==> 
    naddr in mem[id].mem64 && mem[id].mem64[naddr] == old_mem[id].mem64[naddr])
}



}
