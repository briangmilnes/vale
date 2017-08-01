include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"
include "addrlogic.s.dfy"

module seqproven {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i
import opened addrlogic

// Without chaining.

function Add8(mem : Heaplets, id: heaplet_id, ar : Addrs64, i : nat) : uint64
 requires 0 <= i < ar.count;
 requires ValidDstAlAddrs64(mem, id, ar);
{
  lemma_ValidDstAlAddrs64(mem, id, ar);
  BitwiseAdd64(mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v, 8)
}

lemma lemma_Add8_is_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
 requires 0 < ar.count;
 requires ValidDstAlAddrs64(mem, id, ar);
 ensures Add8(mem, id, ar, 0) == 
    BitwiseAdd64(mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, 0))].v, 8)
{
}

lemma lemma_Add8_is(mem : Heaplets, id: heaplet_id, ar : Addrs64, i : nat)
 requires 0 <= i < ar.count;
 requires ValidDstAlAddrs64(mem, id, ar);
 ensures Add8(mem, id, ar, i) == 
    BitwiseAdd64(mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v, 8)
{
}

predicate Add8_SubSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64, v : seq<uint64>) 
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires |v| <= ar.count;
{
  forall i : nat :: 0 <= i < |v| ==> Add8(mem, id, ar, i) == v[i]
}

predicate Add8_FullSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64, v : seq<uint64>) 
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires |v| == ar.count;
{
  forall i : nat :: 0 <= i < ar.count ==> Add8(mem, id, ar, i) == v[i]
}

function Add8Seq(mem : Heaplets, id: heaplet_id, ar : Addrs64, count : nat) : seq<uint64>
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires 0 <= count <= ar.count;
 ensures |Add8Seq(mem, id, ar, count)| == count; 
// Doing this here at the function definition is CRITICAL.
 ensures forall i : nat :: 0 <= i < count ==> 
         Add8Seq(mem, id, ar, count)[i] == Add8(mem, id, ar, i);
{
  if (count == 0) then
    []
  else 
    Add8Seq(mem, id, ar, count - 1) + [Add8(mem, id, ar, count - 1)]
}

lemma lemma_Add8Seq_check_SubSeq_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures Add8_SubSeq(mem, id, ar, []);
{
}

lemma lemma_Add8Seq_check_SubSeq_fixed(mem : Heaplets, id: heaplet_id, ar : Addrs64, count : nat)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires 0 <= count <= ar.count;
  ensures Add8_SubSeq(mem, id, ar, Add8Seq(mem, id, ar, count));
{
  if (count == 0) {
  } else {
    lemma_Add8Seq_check_SubSeq_fixed(mem, id, ar, count - 1);
  }
}

lemma lemma_Add8Seq_check_FullSeq_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires ar.count == 0;
  ensures Add8_FullSeq(mem, id, ar, Add8Seq(mem, id, ar, ar.count));
{
}

lemma lemma_Add8Seq_check_FullSeq_one(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires ar.count == 1;
  ensures Add8_FullSeq(mem, id, ar, Add8Seq(mem, id, ar, ar.count));
{
}

lemma lemma_Add8Seq_check_SubSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures forall count : nat :: 0 <= count <= ar.count ==> 
    Add8_SubSeq(mem, id, ar, Add8Seq(mem, id, ar, count));
{
}

lemma lemma_Add8Seq_check_FullSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures Add8_FullSeq(mem, id, ar, Add8Seq(mem, id, ar, ar.count));
  decreases ar.count;
{
}

// With chaining.

function Sum(mem : Heaplets, id: heaplet_id, ar : Addrs64, i : nat) : uint64
 requires 0 <= i < ar.count;
 requires ValidDstAlAddrs64(mem, id, ar);
{
  lemma_ValidDstAlAddrs64(mem, id, ar);
  if (i == 0) then
    mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v
  else 
    BitwiseAdd64(mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v,
                 Sum(mem, id, ar, i - 1))
}

lemma Sum_is_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
 requires ValidDstAlAddrs64(mem, id, ar);
 requires 0 < ar.count;
 ensures Sum(mem, id, ar, 0) == mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, 0))].v;
{
}

lemma Sum_is(mem : Heaplets, id: heaplet_id, ar : Addrs64, i : nat)
 requires ValidDstAlAddrs64(mem, id, ar);
 requires 0 < i < ar.count;
 ensures Sum(mem, id, ar, i) == 
  BitwiseAdd64(mem[id].mem64[EvalAddrOff64(addroff64(ar.addr, i))].v,
    Sum(mem, id, ar, i - 1))
{
  if (i == 0) {
  } else {
  }
}

predicate Sum_SubSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64, v : seq<uint64>) 
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires |v| <= ar.count;
{
  forall i : nat :: 0 <= i < |v| ==> Sum(mem, id, ar, i) == v[i]
}


predicate Sum_FullSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64, v : seq<uint64>) 
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires |v| == ar.count;
{
  forall i : nat :: 0 <= i < ar.count ==> Sum(mem, id, ar, i) == v[i]
}

function SumSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64, count : nat) : seq<uint64>
 requires ValidDstAlAddrs64(mem, id, ar);  
 requires 0 <= count <= ar.count;
 ensures |SumSeq(mem, id, ar, count)| == count; 
// Doing this here at the function definition is CRITICAL.
 ensures forall i : nat :: 0 <= i < count ==> 
         SumSeq(mem, id, ar, count)[i] == Sum(mem, id, ar, i);
{
  if (count == 0) then
    []
  else 
    SumSeq(mem, id, ar, count - 1) + [Sum(mem, id, ar, count - 1)]
}

lemma lemma_SumSeq_check_SubSeq_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures Sum_SubSeq(mem, id, ar, []);
{
}

lemma lemma_SumSeq_check_SubSeq_fixed(mem : Heaplets, id: heaplet_id, ar : Addrs64, count : nat)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires 0 <= count <= ar.count;
  ensures Sum_SubSeq(mem, id, ar, SumSeq(mem, id, ar, count));
{
  if (count == 0) {
  } else {
    lemma_SumSeq_check_SubSeq_fixed(mem, id, ar, count - 1);
  }
}

lemma lemma_SumSeq_check_FullSeq_zero(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires ar.count == 0;
  ensures Sum_FullSeq(mem, id, ar, SumSeq(mem, id, ar, ar.count));
{
}

lemma lemma_SumSeq_check_FullSeq_one(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  requires ar.count == 1;
  ensures Sum_FullSeq(mem, id, ar, SumSeq(mem, id, ar, ar.count));
{
}

lemma lemma_SumSeq_check_SubSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures forall count : nat :: 0 <= count <= ar.count ==> 
    Sum_SubSeq(mem, id, ar, SumSeq(mem, id, ar, count));
{
}

lemma lemma_SumSeq_check_FullSeq(mem : Heaplets, id: heaplet_id, ar : Addrs64)
  requires ValidDstAlAddrs64(mem, id, ar);  
  ensures Sum_FullSeq(mem, id, ar, SumSeq(mem, id, ar, ar.count));
  decreases ar.count;
{
}

// Utility

lemma lemma_BitwiseAdd64()
    ensures  forall x:uint64, y:uint64 :: x + y < 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y
    ensures  forall x:uint64, y:uint64 :: x + y >= 0x1_0000_0000_0000_0000 ==> BitwiseAdd64(x, y) == x + y - 0x1_0000_0000_0000_0000
    ensures  forall x:uint64 :: BitwiseAdd64(x, 0) == x;
{
    reveal_BitwiseAdd64();
}


}
