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
      ensures ValidDstUnAddr64(mem, id, ao);
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

// Useable but dangerous in that one can not then roll up to blocks for proof.
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
  ValidDstUnAddr64(mem, id, ao) &&
  id in mem && mem[id].Heaplet64? && 
  // I didn't drop any addresses.
  (forall naddr : int :: naddr in old_mem[id].mem64 ==> naddr in mem[id].mem64) && 
  // I only adjusted this one address in old_mem[id].
  (forall naddr : int :: 
    (naddr != EvalAddrOff64(ao) && naddr in old_mem[id].mem64 && naddr in mem[id].mem64) ==>
    mem[id].mem64[naddr] == old_mem[id].mem64[naddr])
}


// Why was I using requires here?
predicate UpdatesAlAddrs64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, 
                            ar : Addrs64, taint:taint, v: seq<uint64>)
{
  ValidAddrs64(ar) &&
  ValidDstUnAddrs64(old_mem, id, ar) &&
  ValidSrcAlAddrs64(mem, id, ar, taint) &&
  (forall i : nat :: 0 <= i < ar.count ==> ValidAddrOff64(addroff64(ar.addr, i))) &&
  (|v| == ar.count ) &&
  // mem[id] is still a Healplet64
  id in mem && mem[id].Heaplet64? &&
  // Restart here, try a combined predicate based on address range not count.
  (forall i : nat :: 
     (0 <= i < ar.count ==> 
      (mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].t == taint &&
      v[i] == mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v)))

// Putting the mod in here seems to fail.
//  (forall naddr : nat :: 
//    ((ar.addr <= naddr <= ar.addr + (ar.count - 1) * 8) && 
//     (naddr in old_mem[id].mem64 && naddr in mem[id].mem64)) ==>
//      mem[id].mem64[naddr].t == taint &&
//      v[(naddr - ar.addr) % 8] == mem[id].mem64[naddr].v)
}

predicate OnlyAddrs64Modified(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ar : Addrs64)
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
    mem[id].mem64[naddr] == old_mem[id].mem64[naddr])
 // Let's try it by count. Bad 2 minutes proof time.
//  (forall i : int :: 
//   ((i < 0 || i >= ar.count) && 
//          (ar.addr + i * 8) in old_mem[id].mem64 && (ar.addr + i * 8) in mem[id].mem64) ==>
//     mem[id].mem64[ar.addr + i * 8] == old_mem[id].mem64[ar.addr + i * 8])
}

lemma {:timeLimitMultiplier 3} lemma_OnlyAddrs64Modified_Extension
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, 
          id:heaplet_id, addr : uint64, off : nat, taint : taint)
    requires ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint)
    requires ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
    requires ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);

    requires OnlyAddrs64Modified(mem0, mem1, id, addrs64(addr, off));
    requires OnlyAddr64Modified(mem1, mem2, id, addroff64(addr, off));

    ensures  OnlyAddrs64Modified(mem0, mem2, id, addrs64(addr, off + 1));
{ 
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);
}    

lemma {:timeLimitMultiplier 1} lemma_UpdatesAlAddrs64_OnlyAddrs64Modified_Extension
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, 
          id:heaplet_id, addr : uint64, off : nat, taint : taint,
                         v : seq<uint64>)
    requires |v| == off + 1;           
    requires ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint)
    requires ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
    requires ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);

    requires UpdatesAlAddrs64(mem0, mem1, id, addrs64(addr, off), taint, v[..off]);
    requires OnlyAddrs64Modified(mem0, mem1, id, addrs64(addr, off));

    requires UpdatesAddr64(mem1, mem2, id, addroff64(addr, off), taint, v[off]);
    requires OnlyAddr64Modified(mem1, mem2, id, addroff64(addr, off));

    ensures  UpdatesAlAddrs64(mem0, mem2, id, addrs64(addr, off + 1), taint, v);
    ensures  OnlyAddrs64Modified(mem0, mem2, id, addrs64(addr, off + 1));
{ 
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);
  lemma_OnlyAddrs64Modified_Extension(mem0, mem1, mem2, id, addr, off, taint);
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
