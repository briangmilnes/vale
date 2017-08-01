/*

    Addrlogic64.s.dfy 
    Brian G. Milnes, 22 July 2017
   

 	  i.		Abstract

   As of July 2017 looping in Vale is using a simple set of address space predicates but
   does not have a general set of lemmas, so we are reproving looping properties.

   This is a new simple separation logic for linear only datastructures that encapsulates
  all of the logic one needs to prove looping that reads and writes linearly. 
  Including unrolled loops.

  We bundle up address+offset access and address range access into data structures to
  allow us to better control triggering of quantifiers in lemmas.

  The goal is that for any specification of address space, there is a single lemma
  that elaborates its entailments that proves quickly.

  And that for every property of a loop which is working on this address space, there
  is a lemma that combines these address spaces.

  At least in CTR, I did not clearly specify and prove that we are not writing other
  addresses (in the heaplets I modify). So this separation logic specifies changed
  cells using address+offset or address range on both writes and did-not-write specifications.

  When writing loops one needs four lemmas: 
   1) OnlyWrites with a range and an added address + offset that proves a new OnlyWrites on
       the unioned range.
   2) OnlyWrites and Writes on a range and anddress + offset that proves both on the unioned
      range.
   3) OnlyWrites with two ranges that proves a new OnlyWrites on the on the unioned range.
   4) OnlyWrites and Writes on two ranges that proves them again on the unioned range.

*/
/*

 	  i.		Abstract

   
    i.		Abstract
    1.	  Includes/Module
		2.		AddrOff64 and Addrs64
		3.		Unaligned Addr64
		4.		Aligned Addr64
    5.		Unaligned Addrs64
    6.		Aligned Addrs64
		7.		Writes OnlyWrites Addr64
		8.		Writes OnlyWrites Addrs64
		9.		Tails
   
TODO

 1) Can I make range testing that improves triggering?
 2) Should I build the simple algebra?
    Including adjacent and union?

*/

/*

		1.	 	Includes/Module

*/

include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

module addrlogicproven {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i

/*

		2.		AddrOff64 and Addrs64

*/

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

// A shift lemma allowing one to move any part of the offset into the address.
lemma lemma_ValidAddrOff64_Shift(ao : AddrOff64)
   requires ValidAddrOff64(ao)
   ensures forall i : nat :: 0 <= i < ao.offset ==>
      EvalAddrOff64(ao) == EvalAddrOff64(addroff64(ao.addr + i * 8, ao.offset - i));
   ensures forall i : nat :: 0 <= i < ao.offset ==> 
      ValidAddrOff64(addroff64(ao.addr + i * 8, ao.offset - i));
{}


// Bundle up what is an address range to let us trigger better.

datatype Addrs64 = addrs64(addr : uint64, count : nat)

predicate ValidAddrs64(ar : Addrs64) 
{
  ar.addr + ar.count * 8 < 0x1_0000_0000_0000_0000
}

/*

		3.		Unaligned Addr64

*/

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
      ensures EvalAddrOff64(ao) == EvalAddrOff64(addroff64(ao.addr + ao.offset * 8, 0));
      ensures EvalAddrOff64(ao) in mem[id].mem64;
      ensures ValidDstUnAddr64(mem, id, addroff64(ao.addr + ao.offset * 8, 0));
{
}

lemma lemma_ValidSrcUnAddr64(mem:Heaplets, id:heaplet_id, ao : AddrOff64, t:taint)
      requires ValidAddrOff64(ao);
      requires ValidSrcUnAddr64(mem, id, ao, t); 
      ensures id in mem;
      ensures mem[id].Heaplet64?;
      ensures EvalAddrOff64(ao) == EvalAddrOff64(addroff64(ao.addr + ao.offset * 8, 0));
      ensures EvalAddrOff64(ao) in mem[id].mem64;
      ensures mem[id].mem64[EvalAddrOff64(ao)].t == t;
      ensures ValidDstUnAddr64(mem, id, ao);
      ensures ValidDstUnAddr64(mem, id, addroff64(ao.addr + ao.offset * 8, 0));
      ensures ValidSrcUnAddr64(mem, id, addroff64(ao.addr + ao.offset * 8, 0), t);
{
}

/*

		4.		Unaligned Addr64

*/

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

/*

		5.		Aligned Addr64

*/

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
      ensures ValidDstAlAddr64(mem, id, addroff64(ao.addr + ao.offset * 8, 0));
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
      ensures ValidSrcAlAddr64(mem, id, addroff64(ao.addr + ao.offset * 8, 0), t);
      // Map to the old stuff for instructions.
      ensures ao.addr + ao.offset * 8 in mem[id].mem64;
      ensures ValidSrcAddr(mem, id, ao.addr + ao.offset * 8, 64, t); // Map to the old stuff for instructions.
{
}


/*

		6.		Aligned Addrs64

*/

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

/*

		7.		Writes OnlyWrites Addr64

*/

// The crux of the problem with this verses the older style is that does not write predicates
// are implicit in these Dafny function operations below. But it is much harder to get these
// to prove in many cases, so I've gone to quantified statements.

// Useable but dangerous in that one can not then roll up to blocks for proof.
//predicate OnlyWritesAddr64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ao : AddrOff64, taint:taint, v:uint64)
//{
//  ValidAddrOff64(ao) && 
//  ValidDstUnAddr64(old_mem, id, ao) &&
//  mem == old_mem[id := old_mem[id].(mem64 := old_mem[id].mem64[EvalAddrOff64(ao) := Heaplet64Entry(v, taint)])]
//}

predicate WritesAddr64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ao : AddrOff64, t:taint, v:uint64)
{
  ValidAddrOff64(ao) && 
  ValidDstUnAddr64(old_mem, id, ao) &&
  ValidDstUnAddr64(mem, id, ao) &&   
  mem[id].mem64[EvalAddrOff64(ao)].v == v && 
  mem[id].mem64[EvalAddrOff64(ao)].t == t
}

lemma lemma_WritesAddr64(mem1: Heaplets, mem2: Heaplets, 
          id:heaplet_id, addr : uint64, items : nat, more_items : nat, taint : taint, v : seq<uint64>)
   
   requires WritesAddrs64(mem1, mem2, id, addrs64(addr, items), taint, v);
   ensures forall i : nat :: i < |v| ==>
     WritesAddrs64(mem1, mem2, id, addrs64(addr, i), taint, v[..i]);
{
}

predicate OnlyWritesAddr64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ao : AddrOff64)
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


/*

		8.	Writes OnlyWrites Addrs64

*/

// Another problem is that I'm using both count and address range quantifiers,
// but it works. Indeed CBC did the same. A single style might improve proof
// time.

predicate WritesAddrs64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, 
                            ar : Addrs64, taint:taint, v: seq<uint64>)
{
  ValidAddrs64(ar) &&
  ValidDstUnAddrs64(old_mem, id, ar) &&
  ValidSrcAlAddrs64(mem, id, ar, taint) &&
  (forall i : nat :: 0 <= i < ar.count ==> ValidAddrOff64(addroff64(ar.addr, i))) &&
  (|v| == ar.count ) &&
  // mem[id] is still a Healplet64
  id in mem && mem[id].Heaplet64? &&
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

predicate OnlyWritesAddrs64(old_mem : Heaplets, mem : Heaplets, id:heaplet_id, ar : Addrs64)
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

/*

		9.		Extension Lemmas

*/

// These two work nicely when one has a loop over a procedure that writes a single address.

lemma {:timeLimitMultiplier 3} lemma_OnlyWrites_Range_Addr_Ext
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, 
          id:heaplet_id, addr : uint64, off : nat, taint : taint)
    requires ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint)
    requires ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
    requires ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);

    requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(addr, off));
    requires OnlyWritesAddr64(mem1, mem2, id, addroff64(addr, off));

    ensures  OnlyWritesAddrs64(mem0, mem2, id, addrs64(addr, off + 1));
{ 
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);
}    

lemma {:timeLimitMultiplier 3} lemma_Writes_OnlyWrites_Range_Addr_Ext
         (mem0 : Heaplets, mem1: Heaplets, mem2: Heaplets, 
          id:heaplet_id, addr : uint64, off : nat, taint : taint, v : seq<uint64>)
    requires |v| == off + 1;
    requires ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint)
    requires ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
    requires ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);

    requires WritesAddrs64(mem0, mem1, id, addrs64(addr, off), taint, v[..off]);
    requires OnlyWritesAddrs64(mem0, mem1, id, addrs64(addr, off));

    requires WritesAddr64(mem1, mem2, id, addroff64(addr, off), taint, v[off]);
    requires OnlyWritesAddr64(mem1, mem2, id, addroff64(addr, off));

    ensures  WritesAddrs64(mem0, mem2, id, addrs64(addr, off + 1), taint, v);
    ensures  OnlyWritesAddrs64(mem0, mem2, id, addrs64(addr, off + 1));
{ 
  lemma_ValidSrcAlAddrs64(mem0, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem1, id, addrs64(addr, off + 1), taint);
  lemma_ValidSrcAlAddrs64(mem2, id, addrs64(addr, off + 1), taint);
  lemma_OnlyWrites_Range_Addr_Ext(mem0, mem1, mem2, id, addr, off, taint);
} 


// These two work nicely when one has a loop over a loop.


lemma lemma_subsequence_ext(items : nat, more_items : nat, v : seq<uint64>)
    requires |v| == items + more_items;
    ensures v == v[..items] + v[items..(items + more_items)];
{
}

lemma lemma_ValidAddrs64_Tail(ar : Addrs64)
      requires ValidAddrs64(ar);
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidAddrs64(addrs64(ar.addr + i * 8, ar.count - i));

      ensures forall i : nat :: 0 <= i < ar.count ==>
              forall j : nat :: 0 <= j <= i ==>
               EvalAddrOff64(addroff64(ar.addr, i)) == EvalAddrOff64(addroff64(ar.addr + j * 8, i - j));
{}

lemma {:timeLimitMultiplier 3} lemma_OnlyWrites_Range_Range_Ext
         (mem0 : Heaplets, mem1 : Heaplets, mem2: Heaplets, id : heaplet_id, 
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


/*
		9.	Tails

    When working with an address range, I can change the pointer and have a valid address.
*/

lemma lemma_ValidSrcAlAddrs64_Fixed_Tail_Off(mem:Heaplets, id:heaplet_id, ar: Addrs64, tail : nat, 
                               off : nat, taint : taint)
      requires ValidAddrs64(ar);
      requires ValidSrcAlAddrs64(mem, id, ar, taint);
      requires 0 <= tail < ar.count;
      requires 0 <= off < (ar.count - tail);
      ensures ValidSrcAlAddr64(mem, id, addroff64(ar.addr + tail * 8, off), taint);
{
  lemma_ValidSrcAlAddrs64(mem, id, ar, taint);
  if (tail == 0) {
  } else {
   assert EvalAddrOff64(addroff64(ar.addr + tail * 8, off)) == 
    EvalAddrOff64(addroff64(ar.addr, off + tail));
   lemma_ValidSrcAlAddrs64_Fixed_Tail_Off(mem, id, ar, tail - 1, off, taint);
  }
}

lemma lemma_ValidSrcAlAddrs64_Fixed_Tail(mem:Heaplets, id:heaplet_id, ar: Addrs64, tail : nat, taint : taint)
      requires ValidAddrs64(ar);
      requires ValidSrcAlAddrs64(mem, id, ar, taint);
      requires 0 <= tail < ar.count;
      ensures forall off : nat :: 0 <= off < (ar.count - tail) ==>
        ValidSrcAlAddr64(mem, id, addroff64(ar.addr + tail * 8, off), taint);
{
  lemma_ValidSrcAlAddrs64(mem, id, ar, taint);
  forall off : nat | 0 <= off < (ar.count - tail) 
   ensures ValidSrcAlAddr64(mem, id, addroff64(ar.addr + tail * 8, off), taint);
   {
      lemma_ValidSrcAlAddrs64_Fixed_Tail_Off(mem, id, ar, tail, off, taint);
   } 
}

// This lemma when in a verbatim fails to trigger. -bgm 

lemma lemma_ValidSrcAlAddrs64_Tails(mem:Heaplets, id:heaplet_id, ar: Addrs64, taint : taint)
      requires ValidAddrs64(ar);
      requires ValidSrcAlAddrs64(mem, id, ar, taint);
      ensures 
       forall tail :: 0 <= tail < ar.count ==>
        forall off : nat :: 0 <= off < (ar.count - tail) ==>
         ValidSrcAlAddr64(mem, id, addroff64(ar.addr + tail * 8, off), taint);
{
  forall tail : nat | 0 <= tail < ar.count
   ensures forall off : nat :: 0 <= off < (ar.count - tail) ==>
         ValidSrcAlAddr64(mem, id, addroff64(ar.addr + tail * 8, off), taint);
 {
   lemma_ValidSrcAlAddrs64_Fixed_Tail(mem, id, ar, tail, taint);
 }
} 

}
