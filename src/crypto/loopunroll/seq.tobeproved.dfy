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

lemma lemma_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64
         (mem0 : Heaplets, mem1: Heaplets, id:heaplet_id, addr : uint64, count_items : nat, 
         items : nat, taint : taint, v : seq<uint64>)
   requires count_items <= items;
   requires ValidSrcAlAddrs64(mem0, id, addrs64(addr, items), taint);
   requires WritesAddrs64(mem0, mem1, id, addrs64(addr, count_items), taint, v);
   requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(addr, count_items));
   ensures  ValidSrcAlAddrs64(mem1, id, addrs64(addr, items), taint);
{
}

lemma lemma_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64'
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
    requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(base, items));

    requires WritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items), taint, v[items..(items+more_items)]);
    requires OnlyWritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items));
 
    ensures  ValidSrcAlAddrs64(mem2, id, addrs64(base, items + more_items), taint);
{
  lemma_subsequence_ext(items, more_items, v);
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(base, items + more_items), taint);
  assume ValidSrcAlAddrs64(mem2, id, addrs64(base, items + more_items), taint);
}

lemma {:timeLimitMultiplier 3} lemma_OnlyWrites_Range_Range_Ext
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, id : heaplet_id, 
         base : uint64, ptr : uint64, items : nat, more_items : nat, taint : taint)
    requires ptr == base + items * 8;
    requires ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
    requires ValidSrcAlAddrs64(mem1, id, addrs64(base, items + more_items), taint);
    requires ValidSrcAlAddrs64(mem2, id, addrs64(base, items + more_items), taint);

    requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(base, items));
    requires OnlyWritesAddrs64(mem1, mem2, id, addrs64(ptr, more_items));

    ensures  OnlyWritesAddrs64(mem0, mem2, id, addrs64(base, items + more_items));
{
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(base, items + more_items), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(base, items + more_items), taint);
  lemma_ValidSrcAlAddrs64(mem2, id, addrs64(base, items + more_items), taint);
}    

lemma {:timeLimitMultiplier 3} lemma_Writes_OnlyWrites_Range_Range_Ext
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, 
          id:heaplet_id, base : uint64, ptr : uint64, 
          items: nat, count_items : nat, more_items : nat, taint : taint, v : seq<uint64>)
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
    ensures WritesAddrs64(mem0, mem2, id, addrs64(base, count_items + more_items), taint, v);
    ensures OnlyWritesAddrs64(mem0, mem2, id, addrs64(base, count_items + more_items));
{ 
  lemma_subsequence_ext(count_items, more_items, v);
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(base, count_items + more_items), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(base, count_items + more_items), taint);
  lemma_OnlyWritesAddrs64_Preserves_ValidSrcAlAddrs64'
         (mem0, mem1, mem2, id, base, ptr, count_items, more_items, taint, v);
  lemma_OnlyWrites_Range_Range_Ext(mem0, mem1, mem2, id, base, ptr, count_items, more_items, taint);
}

}

