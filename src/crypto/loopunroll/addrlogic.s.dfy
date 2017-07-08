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


// Try allowing zero address ranges.
// Bundle up what is a valid address to allow us to control triggering better.

datatype AddrOff64 = addroff64(addr : uint64, offset : nat)

predicate ValidAddrOff64(ao : AddrOff64) 
{
   ao.addr + ao.offset * 8 < 0x1_0000_0000_0000_0000
}

function EvalAddrOff64(ao : AddrOff64) : uint64
  requires ValidAddrOff64(ao)
  ensures EvalAddrOff64(ao) < 0x1_0000_0000_0000_0000;
{
  (ao.addr + ao.offset * 8) % 0x1_0000_0000_0000_0000
}

// Bundle up what is an address range to let us trigger better.

datatype Addrs64 = addrs64(addr : uint64, count : nat)

predicate ValidAddrs64(ar : Addrs64) 
{
  ar.addr + ar.count * 8 < 0x1_0000_0000_0000_0000
}

// Unaligned 

predicate ValidDstUnAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64)
{
  ValidAddrOff64(ao) && 
  id in mem  && 
  mem[id].Heaplet64? && 
  EvalAddrOff64(ao) in mem[id].mem64
}

predicate ValidSrcUnAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64, taint:taint) 
{
  ValidAddrOff64(ao) &&
  id in mem  && 
  mem[id].Heaplet64? && 
  EvalAddrOff64(ao) in mem[id].mem64 &&
  mem[id].mem64[EvalAddrOff64(ao)].t == taint
}

lemma lemma_ValidDstUnAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64)
      requires ValidAddrOff64(ao);
      requires ValidDstUnAddr64(mem, id, ao);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures EvalAddrOff64(ao) in mem[id].mem64;
{
}

lemma lemma_ValidSrcUnAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64, t:taint)
      requires ValidAddrOff64(ao);
      requires ValidSrcUnAddr64(mem, id, ao, t); 
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures EvalAddrOff64(ao) in mem[id].mem64;
      ensures mem[id].mem64[EvalAddrOff64(ao)].t == t;
      ensures ValidDstUnAddr64(mem, id, ao);
{
}


// Unaligned 

predicate ValidDstUnAddrs64(mem:Heaplets, id:heaplet_id, ar : Addrs64) 
{
  ValidAddrs64(ar) &&
  id in mem &&
  mem[id].Heaplet64? &&
  (forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64) &&
  (forall i : nat :: 0 <= i < ar.count ==> ValidDstUnAddr64(mem, id, addroff64(ar.addr, i)))
}

predicate ValidSrcUnAddrs64(mem:Heaplets, id:heaplet_id, ar : Addrs64, taint:taint)
{
  ValidAddrs64(ar) && 
  id in mem &&
  mem[id].Heaplet64? &&
  (forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64) &&
  (forall i : nat :: 0 <= i < ar.count ==> ValidSrcUnAddr64(mem, id, addroff64(ar.addr, i), taint))
}

lemma lemma_ValidDstUnAddrs64(mem:Heaplets, id:heaplet_id, ar : Addrs64) 
      requires ValidAddrs64(ar);
      requires ValidDstUnAddrs64(mem, id, ar);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64;
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidDstUnAddr64(mem, id, addroff64(ar.addr, i));
{}

lemma lemma_ValidSrcUnAddrs64(mem:Heaplets, id:heaplet_id, ar: Addrs64, taint : taint)
      requires ValidAddrs64(ar);
      requires ValidSrcUnAddrs64(mem, id, ar, taint);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64;
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidDstUnAddr64(mem, id, addroff64(ar.addr, i));
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidSrcUnAddr64(mem, id, addroff64(ar.addr, i), taint);
{}

// Aligned

predicate ValidDstAlAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64)
{
  ValidAddrOff64(ao) &&
  id in mem  && 
  mem[id].Heaplet64? && 
  EvalAddrOff64(ao) in mem[id].mem64 &&
  EvalAddrOff64(ao) % 8 == 0
}

predicate ValidSrcAlAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64, taint:taint) 
{
  ValidAddrOff64(ao) &&
  id in mem  && 
  mem[id].Heaplet64? && 
  EvalAddrOff64(ao) in mem[id].mem64 &&
  EvalAddrOff64(ao) % 8 == 0 && 
  mem[id].mem64[EvalAddrOff64(ao)].t == taint
}

lemma lemma_ValidDstAlAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64)
      requires ValidAddrOff64(ao);
      requires ValidDstAlAddr64(mem, id, ao);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures EvalAddrOff64(ao) in mem[id].mem64;
      ensures EvalAddrOff64(ao) % 8 == 0;
      ensures ValidDstAddr(mem, id, EvalAddrOff64(ao), 64); // Map to the old stuff for instructions.
      // Map to the old stuff for instructions.
      ensures ao.addr + ao.offset * 8 in mem[id].mem64;
      ensures ValidDstAddr(mem, id, ao.addr + ao.offset * 8, 64); // Map to the old stuff for instructions.
{
}

lemma lemma_ValidSrcAlAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64, t:taint)
      requires ValidAddrOff64(ao);
      requires ValidSrcAlAddr64(mem, id, ao, t); 
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures EvalAddrOff64(ao) in mem[id].mem64;
      ensures mem[id].mem64[EvalAddrOff64(ao)].t == t;
      ensures EvalAddrOff64(ao) % 8 == 0;
      ensures ValidDstAlAddr64(mem, id, ao);
      // Map to the old stuff for instructions.
      ensures ao.addr + ao.offset * 8 in mem[id].mem64;
      ensures ValidSrcAddr(mem, id, ao.addr + ao.offset * 8, 64, t); // Map to the old stuff for instructions.
{
}

predicate ValidDstAlAddrs64(mem:Heaplets, id:heaplet_id, ar : Addrs64) 
{
  ValidAddrs64(ar) &&
  id in mem &&
  mem[id].Heaplet64? &&
  EvalAddrOff64(addroff64(ar.addr, 0)) % 8 == 0 && 
  (forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64) &&
  (forall i : nat :: 0 <= i < ar.count ==> ValidDstAlAddr64(mem, id, addroff64(ar.addr, i)))
}

predicate ValidSrcAlAddrs64(mem:Heaplets, id:heaplet_id, ar : Addrs64, taint:taint)
{
  ValidAddrs64(ar) &&
  id in mem &&
  mem[id].Heaplet64? &&
  EvalAddrOff64(addroff64(ar.addr, 0)) % 8 == 0 && 
  (forall i : nat :: 0 <= i < ar.count ==> ValidAddrOff64(addroff64(ar.addr, i))) &&
  (forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64) &&
  (forall i : nat :: 0 <= i < ar.count ==> ValidSrcAlAddr64(mem, id, addroff64(ar.addr, i), taint))
}

predicate AddrOffInAddrs64(a : AddrOff64, ar : Addrs64) {
  ar.addr <= a.addr + a.offset * 8 <= ar.addr + ar.count * 8
}

lemma lemma_ValidDstAlAddrs64(mem:Heaplets, id:heaplet_id, ar : Addrs64) 
      requires ValidAddrs64(ar);
      requires ValidDstAlAddrs64(mem, id, ar);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64;
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidDstAlAddr64(mem, id, addroff64(ar.addr, i));
{}

lemma lemma_ValidSrcAlAddrs64(mem:Heaplets, id:heaplet_id, ar: Addrs64, taint : taint)
      requires ValidAddrs64(ar);
      requires ValidSrcAlAddrs64(mem, id, ar, taint);
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidAddrOff64(addroff64(ar.addr, i));
      ensures forall i : nat :: 0 <= i < ar.count ==> EvalAddrOff64(addroff64(ar.addr, i)) in mem[id].mem64;
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidDstAlAddr64(mem, id, addroff64(ar.addr, i));
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidSrcAlAddr64(mem, id, addroff64(ar.addr, i), taint);
{}

// OnlyUpdates

predicate OnlyUpdatesAddr64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ao : AddrOff64, taint:taint, v:uint64)
{
  ValidAddrOff64(ao) && 
  ValidDstUnAddr64(old_mem, id, ao) &&
  mem == old_mem[id := old_mem[id].(mem64 := old_mem[id].mem64[EvalAddrOff64(ao) := Heaplet64Entry(v, taint)])]
}

predicate UpdatesAddr64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ao : AddrOff64, t:taint, v:uint64)
{
  ValidAddrOff64(ao) && 
  ValidDstUnAddr64(old_mem, id, ao) &&
  ValidDstUnAddr64(mem, id, ao) &&   
  mem[id].mem64[EvalAddrOff64(ao)].v == v && 
  mem[id].mem64[EvalAddrOff64(ao)].t == t
}

predicate OnlyAddr64Modified(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ao : AddrOff64)
{  
  ValidAddrOff64(ao) &&
  ValidDstUnAddr64(old_mem, id, ao) &&
  // I don't delelete any heaplet.
  (forall nid : heaplet_id :: nid in old_mem ==> nid in mem) && 
  // I don't modify any other heaplet.
  (forall nid : heaplet_id :: nid in old_mem && nid != id ==> nid in mem && mem[nid] == old_mem[nid]) &&
  // mem[id] is still a Healplet64
  id in mem && mem[id].Heaplet64? &&
  // I only adjusted this one address in old_mem[id].
  (forall naddr : uint64 :: naddr != EvalAddrOff64(ao) && naddr in old_mem[id].mem64 ==> 
    naddr in mem[id].mem64 && mem[id].mem64[naddr] == old_mem[id].mem64[naddr])
}

predicate UpdatesAlAddrs64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, 
                            ar : Addrs64, taint:taint, v: seq<uint64>)
 requires ValidAddrs64(ar)
 requires ValidSrcAlAddrs64(mem, id, ar, taint);
 requires forall i : nat :: 0 <= i < ar.count ==> ValidAddrOff64(addroff64(ar.addr, i));
 requires |v| == ar.count;
{
  // TODO try & instead of two foralls.
  (forall i : nat :: 0 <= i < ar.count ==>  mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].t == taint) &&
  (forall i : nat :: 0 <= i < ar.count ==> v[i] == mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v)
}

predicate OnlyAddrs64Modified(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ar : Addrs64)
{  
  ValidAddrs64(ar) && 
  ValidDstUnAddrs64(old_mem, id, ar) && 
  // I don't delelete any heaplet.
  (forall nid : heaplet_id :: nid in old_mem ==> nid in mem) && 
  // I don't modify any other heaplet.
  (forall nid : heaplet_id :: nid in old_mem && nid != id ==> nid in mem && mem[nid] == old_mem[nid]) &&
  // mem[id] is still a Healplet64
  id in mem && mem[id].Heaplet64? && 
  // I don't delete any of my addresess in id.
  (forall naddr : uint64 :: naddr in old_mem[id].mem64 ==> naddr in mem[id].mem64) && 
  // I only adjusted addresses in range.
  (forall naddr : uint64 ::
   (naddr in old_mem[id].mem64 && naddr in mem[id].mem64 && 
    (naddr < ar.addr || naddr > ar.addr + (ar.count - 1) * 8)) ==>
    mem[id].mem64[naddr] == old_mem[id].mem64[naddr])
}
  
// Temporary
predicate inHeaplets(id : heaplet_id, mem : Heaplets) {
   id in mem
}         

predicate inMem64(id : uint64, mem: map<int, Heaplet64Entry>) {
   id in mem
}         

predicate Heaplet64p(heaplet : Heaplet) {
  heaplet.Heaplet64?
}         

}
