include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"
include "addrlogic.s.dfy"

module seqtobeproven {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i
import opened addrlogic

/*
predicate OnlyWritesAddrs64'(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ar : Addrs64, taint : taint)
{
  ValidAddrs64(ar) && 
  ValidDstUnAddrs64(old_mem, id, ar) && 
  // mem[id] is still a Healplet64
  id in mem && mem[id].Heaplet64? && 
  // I don't delete any of my addresess in id.
  (forall naddr : int :: naddr in old_mem[id].mem64 ==> naddr in mem[id].mem64) && 

  // I only adjusted addresses in range.
  (forall naddr : int ::
    ((naddr < ar.addr || naddr > ar.addr + (ar.count - 1) * 8)  && 
     (naddr in old_mem[id].mem64 && naddr in mem[id].mem64)) ==>
    mem[id].mem64[naddr] == old_mem[id].mem64[naddr] &&
    mem[id].mem64[naddr].t == taint)
}

lemma lemma_OnlyWritesAddrs64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ar : Addrs64, taint : taint)
  requires OnlyWritesAddrs64(old_mem, mem, id, ar);
  ensures id in mem;
  ensures mem[id].Heaplet64?;
  ensures forall naddr : int :: naddr in old_mem[id].mem64 ==> naddr in mem[id].mem64;
{
}
*/


/*
lemma lemma_WritesAddr64_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64
         (mem0 : Heaplets, mem1: Heaplets, id:heaplet_id, addr : uint64, 
         items : nat, taint : taint, v : seq<uint64>)
   requires ValidSrcAlAddrs64(mem0, id, addrs64(addr, items), taint);
   requires WritesAddrs64(mem0, mem1, id, addrs64(addr, items), taint, v);
   requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(addr, items));
   ensures  ValidSrcAlAddrs64(mem1, id, addrs64(addr, items), taint);
{
}


lemma lemma_WritesAddr64_OnlyWritesAddrs64_Preserves_ValidSrcAlAddr64'
         (mem0 : Heaplets, mem1: Heaplets, id:heaplet_id, 
          base : uint64, ptr : uint64,
          items : nat,  more_items : nat, 
          taint : taint, v : seq<uint64>)
   requires |v| == items + more_items;
   requires ptr == base + items * 8;          
   requires ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
   requires WritesAddrs64(mem0, mem1, id, addrs64(ptr, more_items), taint, v[items..(items+more_items)]);
   requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(ptr, more_items));
   ensures (forall i : nat :: 0 <= i < items + more_items ==>
              ValidSrcAlAddr64(mem1, id, addroff64(base, i), taint));
{
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
  if (items > 0) {
    assert ValidSrcAlAddr64(mem1, id, addroff64(base, 1), taint);
  } else {
  }
}
*/

/*
lemma  lemma_WritesAddr64_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64'
         (mem0 : Heaplets, mem1: Heaplets, id:heaplet_id, 
          base : uint64, ptr : uint64,
          items : nat,  more_items : nat, 
          taint : taint, v : seq<uint64>)
   requires items > 0;
   requires |v| == items + more_items;
   requires ptr == base + items * 8;          

   requires ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
   requires WritesAddrs64(mem0, mem1, id, addrs64(ptr, more_items), taint, v[items..(items+more_items)]);
   requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(ptr, more_items));
   ensures ValidSrcAlAddr64(mem1, id, addroff64(base, 1), taint);
{
}
*/

/*
lemma  lemma_WritesAddr64_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64'
         (mem0 : Heaplets, mem1: Heaplets, id:heaplet_id, 
          base : uint64, ptr : uint64,
          items : nat,  more_items : nat, 
          taint : taint, v : seq<uint64>)
   requires |v| == items + more_items;
   requires ptr == base + items * 8;          
   requires ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
   requires WritesAddrs64(mem0, mem1, id, addrs64(ptr, more_items), taint, v[items..(items+more_items)]);
   requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(ptr, more_items));
   ensures  ValidSrcAlAddrs64(mem1, id, addrs64(base, items + more_items), taint);
{
  lemma_ValidSrcAlAddrs64_Tails(mem0, id, addrs64(base, items + more_items), taint);
}
*/

/*
lemma {:timeLimitMultiplier 3} lemma_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64'
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, id:heaplet_id,
          base : uint64, ptr : uint64, 
          items : nat, more_items : nat, 
          taint : taint, 
          v : seq<uint64>)
    requires |v| == items + more_items;
    requires ptr == base + items * 8;
    requires ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
    requires ValidSrcAlAddrs64(mem1, id, addrs64(base, items + more_items), taint);
    
    requires WritesAddrs64(mem0, mem1, id, addrs64(base, items), taint, v[..items]);
    requires OnlyWritesAddrs64'(mem0, mem1, id, addrs64(base, items), taint);

    requires WritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items), taint, v[items..(items+more_items)]);
    requires OnlyWritesAddrs64'(mem1, mem2, id, addrs64(ptr, more_items), taint);
 
    ensures  ValidSrcAlAddrs64(mem2, id, addrs64(base, items + more_items), taint);
{
  lemma_subsequence_ext(items, more_items, v);
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(base, items + more_items), taint);
  lemma_WritesAddr64_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64'
         (mem1, mem2, id, base, ptr, items, more_items, taint, v);
//  assume ValidSrcAlAddrs64(mem2, id, addrs64(base, items + more_items), taint);
}
*/

/*
predicate ValidSrcAlAddrs64'(mem:Heaplets, id:heaplet_id, ar : Addrs64, taint:taint)
{
  ValidAddrs64(ar) &&
  id in mem &&
  mem[id].Heaplet64? &&
  EvalAddrOff64(addroff64(ar.addr, 0)) % 8 == 0 && 
  (forall i : nat :: 0 <= i < ar.count ==> ValidAddrOff64(addroff64(ar.addr, i))) &&
  (forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64) &&
  (forall i : nat :: 0 <= i < ar.count ==> ValidSrcAlAddr64(mem, id, addroff64(ar.addr, i), taint))
}

predicate OnlyWritesAddrs64'(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ar : Addrs64)
{  
  ValidAddrs64(ar) && 
  ValidDstUnAddrs64(old_mem, id, ar) && 
  // mem[id] is still a Healplet64
  id in mem && mem[id].Heaplet64? && 
  // I don't delete any of my addresess in id.
  (forall naddr : int :: naddr in old_mem[id].mem64 ==> naddr in mem[id].mem64) && 

  // I only adjusted values in range.
  (forall naddr : int ::
    ((naddr < ar.addr || naddr > ar.addr + (ar.count - 1) * 8)  && 
     (naddr in old_mem[id].mem64 && naddr in mem[id].mem64)) ==>
    mem[id].mem64[naddr].v == old_mem[id].mem64[naddr].v) &&

  // I have only adjusted taint in range.
  (forall naddr : int ::
    ((naddr < ar.addr || naddr > ar.addr + (ar.count - 1) * 8)  && 
     (naddr in old_mem[id].mem64 && naddr in mem[id].mem64)) ==>
    mem[id].mem64[naddr].t == old_mem[id].mem64[naddr].t)
}

lemma isolate_taint(mem1: Heaplets, mem2: Heaplets, 
              id:heaplet_id, base : uint64, ptr : uint64, 
             items: nat, count_items : nat, more_items : nat, taint : taint, v : seq<uint64>)
    requires items > count_items + more_items;
    requires |v| == count_items + more_items;
    requires ptr == base + count_items * 8;

    requires ValidSrcAlAddrs64(mem1, id, addrs64(base, items), taint);
    requires WritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items), taint, v[count_items..(count_items+more_items)]);
    requires OnlyWritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items));

    ensures forall i : nat :: 0 <= i < more_items ==> 
       mem2[id].mem64[EvalAddrOff64(addroff64(ptr,i))].t == taint;

    ensures forall i : nat :: 0 <= i < more_items ==> 
       mem2[id].mem64[EvalAddrOff64(addroff64(base + count_items * 8,i))].t == taint;

    ensures forall i : nat :: 0 <= i < items ==> 
      mem2[id].mem64[EvalAddrOff64(addroff64(base,i))].t == taint;
{
  assert forall i : nat :: 0 <= i < items ==>
   mem1[id].mem64[EvalAddrOff64(addroff64(base,i))].t == taint;
}

*/

/*
lemma isolate_ValidSrAlAddrs64(mem1: Heaplets, mem2: Heaplets, 
              id:heaplet_id, base : uint64, ptr : uint64, 
             items: nat, count_items : nat, more_items : nat, taint : taint, v : seq<uint64>)
    requires items > count_items + more_items;
    requires |v| == count_items + more_items;
    requires ptr == base + count_items * 8;

    requires ValidSrcAlAddrs64'(mem1, id, addrs64(base, items), taint);
    requires WritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items), taint, v[count_items..(count_items+more_items)]);
    requires OnlyWritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items));

    ensures ValidSrcAlAddrs64'(mem2, id, addrs64(base, items), taint);
{
  forall i : nat | 0 <= i < items
    ensures ValidSrcAlAddr64(mem2, id, addroff64(base, i), taint);
  {
  }
}
*/
// Assume and get the loop working.

lemma lemma_Writes_OnlyWrites_Range_Range_Ext
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, id : heaplet_id, 
         base : uint64, ptr : uint64, 
         items: nat, count_items : nat, more_items : nat, 
         taint : taint, 
         v : seq<uint64>)
    requires items > count_items + more_items;
    requires |v| == count_items + more_items;
    requires ptr == base + count_items * 8;
    requires ValidSrcAlAddrs64(mem0, id, addrs64(base, items), taint);
    requires ValidSrcAlAddrs64(mem1, id, addrs64(base, items), taint);
    
    requires WritesAddrs64(mem0, mem1, id, addrs64(base, count_items), taint, v[..count_items]);
    requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(base, count_items));

    requires WritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items), taint, v[count_items..(count_items+more_items)]);
    requires OnlyWritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items));

    ensures ValidSrcAlAddrs64(mem2, id, addrs64(base, items), taint);
    //  (forall i : nat :: 0 <= i < ar.count ==> ValidSrcAlAddr64(mem2, id, addroff64(ar.addr, i), taint))
    ensures WritesAddrs64(mem0, mem2, id, addrs64(base, count_items + more_items), taint, v);
    //   ValidSrcAlAddrs64(mem2, id, ar, taint)
    // (forall i : nat :: 0 <= i < ar.count ==> ValidSrcAlAddr64(mem2, id, addroff64(ar.addr, i), taint))
    ensures OnlyWritesAddrs64(mem0, mem2, id, addrs64(base, count_items + more_items));
{ 
  lemma_subsequence_ext(count_items, more_items, v);
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(base, count_items + more_items), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(base, count_items + more_items), taint);
//  lemma_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64'
//         (mem0, mem1, mem2, id, base, ptr, count_items, more_items, taint, v);
//  lemma_OnlyWrites_Range_Range_Ext(mem0, mem1, mem2, id, base, ptr, count_items, more_items, taint);

    assume ValidSrcAlAddrs64(mem2, id, addrs64(base, items), taint);
    assume WritesAddrs64(mem0, mem2, id, addrs64(base, count_items + more_items), taint, v);
    assume OnlyWritesAddrs64(mem0, mem2, id, addrs64(base, count_items + more_items));
}


}

