include "../../../lib/util/types.s.dfy"
include "../../../lib/util/operations.s.dfy"
include "../../../lib/util/words_and_bytes.s.dfy"
include "../../../lib/collections/Seqs.s.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../lib/util/dafny_wrappers.i.dfy"

include "../gcm3.s.dfy"

include "../aes.s.dfy"
include "../aes_helpers.i.dfy"

module GCMHelpers {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened dafny_wrappers_i
import opened AESModule
import opened AESHelpersModule
import opened GCMModule

lemma lemma_BitwiseAdd32()
    ensures  forall x:uint32, y:uint32 :: x + y < 0x1_0000_0000 ==> BitwiseAdd32(x, y) == x + y
    ensures  forall x:uint32, y:uint32 :: x + y >= 0x1_0000_0000 ==> BitwiseAdd32(x, y) == x + y - 0x1_0000_0000;
    ensures  forall x:uint32 :: BitwiseAdd32(x, 0) == x;
{
    reveal_BitwiseAdd32();
}

// Testing bits, not known if it proves well yet.
predicate BitTest8(x : bv8, amount : int)
  requires 0 <= amount < 8;
{
   ((x >> amount) & 0x1) == 1
}

predicate BitTest16(x : bv16, amount : int)
  requires 0 <= amount < 16;
{
   ((x >> amount) & 0x1) == 1
}

predicate BitTest32(x : bv32, amount : int)
  requires 0 <= amount < 32;
{
   ((x >> amount) & 0x1) == 1
}

predicate BitTest64(x : bv64, amount : int)
  requires 0 <= amount < 64;
{
   ((x >> amount) & 0x1) == 1
}

predicate BitTest128(x : bv128, amount : int)
  requires 0 <= amount < 128;
{
   ((x >> amount) & 0x1) == 1
}

/* 
// Sanity checks.

// Does z3 shift off to the left correctly. Yes.
lemma is_shift_off_correct_64()
 ensures (0x8000_0000_0000_0000 as bv64) << 1 == 0;
 ensures (0x9000_0000_0000_0000 as bv64) << 1 != 0;
{}

lemma is_shift_on_zero_64()
 ensures forall b : bv64 :: (b << 1) & (0x1 as bv64) == 0;
 ensures forall b : bv64 :: (b << 1) % 2 == 0;
 ensures forall b : bv64 :: (b << 2) % (0x1 << 2) == 0;
 ensures forall b : bv64 :: (b << 64) == 0;
{}

*/

/*
// Proves in 45 s.
lemma lemma_ShiftsAdd(x: bv8, a: nat, b: nat)
  requires 0 <= a + b < 8
  ensures x << (a + b) == (x << a) << b;
{
  forall i : nat | a + i < 8
   ensures x << (a + i) == (x << a) << i
   {
    forall j : nat | j + i < 8
     ensures x << (j + i) == (x << j) << i
     {
     }
   }
}
*/

/*
// Proves in 1:27 s.
lemma {:timeLimitMultiplier 3} lemma_ShiftsAdd(x: bv16, a: nat, b: nat)
  requires 0 <= a + b < 16
  ensures x << (a + b) == (x << a) << b;
{
  forall i : nat | a + i < 16
   ensures x << (a + i) == (x << a) << i
   {
    forall j : nat | j + i < 16
     ensures x << (j + i) == (x << j) << i
     {
     }
   }
}
*/
/*
lemma {:timeLimitMultiplier 6} lemma_ShiftsAdd(x: bv32, a: nat, b: nat)
  requires 0 <= a + b < 32;
  ensures x << (a + b) == (x << a) << b;
{
  forall i : nat | a + i < 32
   ensures x << (a + i) == (x << a) << i
   {
    forall j : nat | j + i < 32
     ensures x << (j + i) == (x << j) << i
     {
     }
   }
}
*/

/*
lemma lemma_left_shift_zero()
 ensures forall b : bv64 :: b == b << 0;
{}

lemma left_shift_to_math_fix(b : bv64, i : nat)
  requires i <= 64;
  ensures b << i == (((b as int) * power(2,i)) % 0x1_0000_0000_0000_0000) as bv64;
{
  if (i == 0) {
    lemma_left_shift_zero();
    assert b << i == b;
    assert power(2,0) == 1;
    assert (b as int) * 1 == b as int;
    assert (b as int) < 0x1_0000_0000_0000_0000;
    assert (b as int) % 0x1_0000_0000_0000_0000 == (b as int);
  }
  else { 
    left_shift_to_math_fix(b, i - 1);
  }
}

lemma left_shift_cummulative_fix(b : bv64, i : nat, j : nat)
 requires i + j <= 64;
 ensures b << (i + j) == (b << i) << j;
{
  if (i == 0) { } 
  else {
   left_shift_cummulative_fix(b, i - 1, j);
 }
}
*/

/*
lemma left_shift_cummulative()
 ensures forall b : bv64 :: forall i : nat :: forall j : nat :: 
 i + j <= 64 ==> b << (i + j) == (b << i) << j;
{ forall k : 

}
*/

/*
method CL_MUL_SHIFT(a : bv64, b : bv64) returns (r : bv128)
{
  var a' := a;
  var b' := b;
  var i := 0;
  r := 0;
  assume b == 0 || exists i : nat :: i <= 8 ==> b << i == 0;
  while b' != 0
   decreases 64 - i;
  {
     if ((a' & 1) != 0) {
      r := r ^ (b' as bv128);
     }
    a' := a' >> 1;
    b' := b' << 1;
    i := i + 1;
    assume b' == b << i;
 }
}
*/

/*
function CL_MUL_SHIFT'(a : bv64, b : bv64, r : bv128) : bv128
{
 if b != 0 then
   if ((a & 1) != 0) then
     CL_MUL_SHIFT'(a >> 1, b << 1, r ^ (b as bv128))
   else 
     CL_MUL_SHIFT'(a >> 1, b << 1, r)
 else 
  r
}
*/

/*

method CL_MUL(src1 : bv128, src2 : bv128, imm8 : bv8) returns (dest : bv128) 
{
  var temp1 : bv64;
  var temp2 : bv128;

  if (imm8[0] == 0) {
    temp1 := src1 % 0x1_0000_0000_0000_0000;
  } else {
    temp1 := src1 / 0x1_0000_0000_0000_0000;
  }

  if (imm8[4] == 0) {
    temp2 := src2 % 0x1_0000_0000_0000_0000;
  } else {
    temp2 := src2 / 0x1_0000_0000_0000_0000;
  }

  var i := 0;
  var tempb : bv128;
  while (i <= 63) {
   tempb[i] := (temp1[0] & temp2[i]);
   var j := 1; 
   while (j <= i) {
    tempb[i] := tempb [i] ^ (temp1[j] & temp2[i - j]);
    j := j + 1;
   }    
   dest[i] := tempb[i];
   i := i + 1;
  }      

  i := 64; 
  while (i <= 126) {
     tempb[i] := 0;
     j := i - 63; 
     while (j >= 63) {
       tempb[i] := tempb[i] ^ (temp1[j] & temp2[i - j]);
       j := j + 1;
     }
     dest[i] := tempb[i];
     i := i + 1;
  } 
  dest[127] := 0;
}
*/

}
