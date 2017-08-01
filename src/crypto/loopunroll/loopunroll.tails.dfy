include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"
include "addrlogic.s.dfy"

module tails {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i
import opened addrlogic

lemma lemma_ValidAddrs64_Tail(ar : Addrs64)
      requires ValidAddrs64(ar);
      ensures forall i : nat :: 0 <= i < ar.count ==> ValidAddrs64(addrs64(ar.addr + i * 8, ar.count - i));

      ensures forall i : nat :: 0 <= i < ar.count ==>
              forall j : nat :: 0 <= j <= i ==>
               EvalAddrOff64(addroff64(ar.addr, i)) == EvalAddrOff64(addroff64(ar.addr + j * 8, i - j));
{}

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
