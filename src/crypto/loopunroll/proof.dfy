include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"
include "addrlogic.s.dfy"

module proof {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i
import opened addrlogic

lemma lemma_OnlyAddrs64ModifiedExt(mem0 : Heaplets, mem1 : Heaplets, mem2: Heaplets, id:heaplet_id, 
                                   addr : uint64, count : nat) 
  requires OnlyAddrs64Modified(mem0, mem1, id, addrs64(addr, count));
  requires OnlyAddr64Modified (mem1, mem2, id, addroff64(addr, count + 1));
  ensures  OnlyAddrs64Modified(mem0, mem2, id, addrs64(addr, count + 1));
{
  assert id in mem0 && id in mem1 && id in mem2;
  assert ValidDstUnAddrs64(mem0, id, addrs64(addr, count));
  assert ValidDstUnAddr64(mem1, id, addroff64(addr, count + 1));

  assume ValidDstUnAddrs64(mem0, id, addrs64(addr, count + 1));
  assume (forall naddr : int ::
   (naddr in mem0[id].mem64 && naddr in mem2[id].mem64 && 
    (naddr < addr || naddr > addr + count * 8)) ==>
     mem2[id].mem64[naddr] == mem0[id].mem64[naddr]);
}


}
