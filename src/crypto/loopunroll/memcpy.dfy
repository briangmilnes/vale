include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"
include "addrlogic.s.dfy"

module memcpy {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i
import opened addrlogic

lemma lemma_BitwiseAdd64()
    ensures  forall x:uint64, y:uint64 :: x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
//    ensures  forall x:uint64, y:uint64 :: x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
//    ensures  forall x:uint64 :: BitwiseAdd64(x, 0) == x;
{
    reveal_BitwiseAdd64();
}

// Without chaining.

function Copy8(mem : Heaplets, id: heaplet_id, ar : Addrs64, i : nat) : uint64
 requires 0 <= i < ar.count;
 requires ValidDstAlAddrs64(mem, id, ar);
{
  lemma_ValidDstAlAddrs64(mem, id, ar);
  mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v
}

lemma lemma_Copy8_is_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
 requires 0 < ar.count;
 requires ValidDstAlAddrs64(mem, id, ar);
 ensures Copy8(mem, id, ar, 0) == mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, 0))].v;
{
}

lemma lemma_Copy8_is(mem : Heaplets, id: heaplet_id, ar : Addrs64, i : nat)
 requires 0 <= i < ar.count;
 requires ValidDstAlAddrs64(mem, id, ar);
 ensures Copy8(mem, id, ar, i) == 
               mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v;
{
}

predicate Copy8_SubSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64, v : seq<uint64>) 
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires |v| <= ar.count;
{
  forall i : nat :: 0 <= i < |v| ==> Copy8(mem, id, ar, i) == v[i]
}

predicate Copy8_FullSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64, v : seq<uint64>) 
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires |v| == ar.count;
{
  forall i : nat :: 0 <= i < ar.count ==> Copy8(mem, id, ar, i) == v[i]
}

function Copy8Seq(mem : Heaplets, id: heaplet_id, ar : Addrs64, count : nat) : seq<uint64>
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires 0 <= count <= ar.count;
 ensures |Copy8Seq(mem, id, ar, count)| == count; 
// Doing this here at the function definition is CRITICAL.
 ensures forall i : nat :: 0 <= i < count ==> 
         Copy8Seq(mem, id, ar, count)[i] == Copy8(mem, id, ar, i);
{
  if (count == 0) then
    []
  else 
    Copy8Seq(mem, id, ar, count - 1) + [Copy8(mem, id, ar, count - 1)]
}

lemma lemma_Copy8Seq_check_SubSeq_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures Copy8_SubSeq(mem, id, ar, []);
{
}

lemma lemma_Copy8Seq_check_SubSeq_fixed(mem : Heaplets, id: heaplet_id, ar : Addrs64, count : nat)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires 0 <= count <= ar.count;
  ensures Copy8_SubSeq(mem, id, ar, Copy8Seq(mem, id, ar, count));
{
  if (count == 0) {
  } else {
    lemma_Copy8Seq_check_SubSeq_fixed(mem, id, ar, count - 1);
  }
}

lemma lemma_Copy8Seq_check_FullSeq_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires ar.count == 0;
  ensures Copy8_FullSeq(mem, id, ar, Copy8Seq(mem, id, ar, ar.count));
{
}

lemma lemma_Copy8Seq_check_FullSeq_one(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires ar.count == 1;
  ensures Copy8_FullSeq(mem, id, ar, Copy8Seq(mem, id, ar, ar.count));
{
}

lemma lemma_Copy8Seq_check_SubSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures forall count : nat :: 0 <= count <= ar.count ==> 
    Copy8_SubSeq(mem, id, ar, Copy8Seq(mem, id, ar, count));
{
}

lemma lemma_Copy8Seq_check_FullSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures Copy8_FullSeq(mem, id, ar, Copy8Seq(mem, id, ar, ar.count));
  decreases ar.count;
{
}

}
