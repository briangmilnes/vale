include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"

// What are reasonable experiments to tell if we can specify things
// in which datatype to prove properties of carryless multiply?

module bvvsuintvsquadword {

import opened x64_def_s
import opened types_s
import opened x64_vale_i

/*
lemma lemma_bv64_is_zero_or_64_shifts_gives_zero(b : bv64)
  ensures b == 0 || (b << 64) == 0;
{
}

lemma lemma_bv64_is_zero_or_upto_64_shifts_gives_zero(b : bv64)
  ensures b == 0 || exists i : nat :: i <= 64 ==> b << i == 0; 
{
  if (b == 0) {
  } else {
    lemma_bv64_is_zero_or_64_shifts_gives_zero(b);
    assert 64 <= 64;
  }
}
*/

// BV version proves.
function BV_CL_MUL_SHIFT'(i : nat, a : bv64, b : bv64, r : bv128) : bv128
  requires 0 <= i <= 64;
  decreases 64 - i;
{
 if (b << i) != 0 then
   if ((a & 1) != 0) then
     BV_CL_MUL_SHIFT'(i + 1, a >> 1, b, r ^ ((b << i) as bv128))
   else 
     BV_CL_MUL_SHIFT'(i + 1, a >> 1, b, r)
 else 
  r
}

function BV_CL_MUL_SHIFT(a : bv64, b : bv64) : bv128
{
 BV_CL_MUL_SHIFT'(0, a, b, 0 as bv128)
}


function bit64(v : bv64, i : nat) : bv1
  requires i < 64;
{
  ((v >> i) & 0x1) as bv1
}

/* 
//Prove
lemma lemma_bit64_check63()
  ensures bit64(0x8000_0000_0000_0000,63) == 0x1;
{}

lemma lemma_bit64_check0()
  ensures bit64(0x1,0) == 0x1;
{}

lemma lemma_bit64_check_zeros()
  ensures forall i : nat :: i < 64 ==> bit64(0x0,i) == 0x0;
{}

lemma lemma_bit64_check_ones_fixed(i : nat)
  requires i < 64;
  ensures  bit64(0xFFFF_FFFF_FFFF_FFFF,i) == 0x1;
{}
*/

/* Won't prove reasonably.
lemma {:timeLimitMultiplier 3} lemma_bit64_check_ones()
  ensures forall i : nat :: i < 64 ==> bit64(0xFFFF_FFFF_FFFF_FFFF,i) == 0x1;
{
  forall j : nat | j < 64
   ensures forall i : nat :: i < 64 ==> bit64(0xFFFF_FFFF_FFFF_FFFF,i) == 0x1;
 {
   lemma_bit64_check_ones_fixed(j);
 }
}
*/

function bit128(v : bv128, i : nat) : bv1
  requires i < 128;
{
  ((v >> i) & 0x1) as bv1
}

lemma lemma_bit128_check127()
  ensures bit128(0x8000_0000_0000_0000_0000_0000_0000_0000, 127) == 0x1;
{}

lemma lemma_bit128_check0()
  ensures bit128(0x1,0) == 0x1;
{}

lemma lemma_bit128_check_zeros()
  ensures forall i : nat :: i < 128 ==> bit128(0x0,i) == 0x0;
{}

/*
lemma {:timeLimitMultiplier 3} lemma_bit128_check_ones_fixed(i : nat)
  requires i < 128;
  ensures  bit128(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,i) == 0x1;
{}

lemma {:timeLimitMultiplier 3} lemma_bit128_check_ones()
  ensures forall i : nat :: i < 128 ==> bit128(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,i) == 0x1;
{
  forall j : nat | j < 128
   ensures forall i : nat :: i < 128 ==> bit128(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,i) == 0x1;
 {
   lemma_bit128_check_ones_fixed(j);
 }
}
*/

// From Gueron and Kounavis, 2014.
function bvclmullow(j : nat, i : nat, a : bv64, b : bv64) : bv1
  requires j <= i;
  requires i < 64;
  decreases i - j;
{
  if (j == i) then
    bit64(a,j) ^ bit64(b, i - j)
  else 
    bit64(a,j) ^ bit64(b, i - j) ^ bvclmullow(j + 1, i, a, b)
}

function bvclmulhigh(i :nat, j : nat, a : bv64, b : bv64) : bv1
  requires i - (64 - 1) <= j <= 64 - 1;
  requires 64 <= i <= 126;
  decreases 64 - 1 - j;
{
  if (j == 64 - 1) then
    bit64(a,j) ^ bit64(b, i - j)
  else 
    bit64(a, j) ^ bit64(b, i - j) ^ bvclmulhigh(i, j + 1, a, b)
}

predicate bvclmul(a : bv64, b : bv64, c : bv128)
{  
  forall i : nat :: i < 63       ==> bit128(c,i) == bvclmullow(0, i, a, b) &&
  forall i : nat :: 64 <= i <= 126 ==> bit128(c,i) == bvclmulhigh(i, i - 64 + 1, a, b) &&
  bit128(c,127) == 0
}

// No way this proves of course.
//lemma {:timeLimitMultiplier 10} BV_CL_MUL_SHIFT_IS_bvclmul_zero()
//  ensures bvclmul(0,0, BV_CL_MUL_SHIFT(0,0));
//{}


/* Not proving.
// uint version
function power(b:int, e:nat) : int
    decreases e;
{
    if (e==0) then
        1
    else
        b*power(b,e-1)
}

function uint64Shl(v : uint64, i : nat) : uint64
{
  (v * power(2,i)) % 0x1_0000_0000_0000_0000
}

function uint64Shr1(v : uint64) : uint64
{
  (v / 2)
}

function {:timeLimitMultiplier 6} UINT64_CL_MUL_SHIFT'(i : nat, a : uint64, b : uint64, r : bv128) : bv128
  requires 0 <= i <= 64;
  decreases 64 - i;
{
 if (uint64Shl(b, i)) != 0 then
   if ((a % 2) != 0) then
     UINT64_CL_MUL_SHIFT'(i + 1, uint64Shr1(a), b, r ^ ((uint64Shl(b,i)) as bv128))
   else 
     UINT64_CL_MUL_SHIFT'(i + 1, uint64Shr1(a), b, r)
 else 
  r
}

function UINT64_CL_MUL_SHIFT(a : uint64, b : uint64) : bv128
{
  UINT64_CL_MUL_SHIFT'(0, a, b, 0 as bv128)
}
*/


}
