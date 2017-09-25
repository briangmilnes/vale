include "../../../lib/util/types.s.dfy"
include "../../../lib/util/operations.s.dfy"
include "../../../lib/util/words_and_bytes.s.dfy"
include "../../../lib/collections/Seqs.s.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../lib/util/dafny_wrappers.i.dfy"

module ShiftHelpers {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened dafny_wrappers_i

/*
// 20s for 16, 32, 64.
lemma lemma_bv8_zero_left_shift_is_zero()
  ensures forall i : nat :: i <= 8 ==> ((0 as bv8) << i) == 0;
{}

lemma lemma_bv8_is_zero_or_8_shifts_gives_zero(b : bv8)
  ensures b == 0 || (b << 8) == 0;
{
}

lemma bv8_is_zero_or_upto_8_shifts_gives_zero(b : bv8)
  ensures b == 0 || exists i : nat :: i <= 8 ==> (b << i) == 0;
{
  lemma_bv8_zero_left_shift_is_zero();
  if (b == 0) {
  } else {
    // Won't prove.
  }
}

*/

/*
lemma lemma_bv8_is_zero_or_upto_8_shifts_gives_zero(b : bv8)
  ensures b == 0 || exists i : nat :: i <= 8 ==> b << i == 0; 
{
  if (b == 0) {
  } else {
   assume exists i : nat :: i <= 8 ==> b << i == 0; 
  }
}

lemma lemma_bv16_is_zero_or_upto_16_shifts_gives_zero(b : bv16)
  ensures b == 0 || exists i : nat :: i <= 16 ==> b << i == 0; 
{
  if (b == 0) {
  } else {
   assume exists i : nat :: i <= 16 ==> b << i == 0; 
  }
}

lemma lemma_bv32_is_zero_or_upto_32_shifts_gives_zero(b : bv32)
  ensures b == 0 || exists i : nat :: i <= 32 ==> b << i == 0; 
{
  if (b == 0) {
  } else {
   assume exists i : nat :: i <= 32 ==> b << i == 0; 
  }
}

lemma lemma_bv64_is_zero_or_upto_64_shifts_gives_zero(b : bv64)
  ensures b == 0 || exists i : nat :: i <= 64 ==> b << i == 0; 
{
  if (b == 0) {
  } else {
   assume exists i : nat :: i <= 64 ==> b << i == 0; 
  }
}


*/
// Proves for 32/32.
// 32/32 fails invariant b' != 0 ==> b' == b << i;
/*
method {:timeLimitMultiplier 3} CL_MUL_SHIFT(a : bv32, b : bv32) returns (r : bv32)
{
  var a' := a;
  var b' := b;
  var i := 0;
  r := 0;
  lemma_bv32_is_zero_or_upto_32_shifts_gives_zero(b);
  while b' != 0
   invariant i == 32 ==> b' == 0;
   invariant b' != 0 ==> 0 <= i <= 32;
   invariant b' != 0 ==> b' == b << i;
   decreases 32 - i;
  {
     if ((a' & 1) != 0) {
      r := r ^ (b' as bv32);
     }
    a' := a' >> 1;
    b' := b' << 1;
    i := i + 1;
 }
}
*/

// Works for 16/32.
// Needs to work up to 64/128.
/*
method {:timeLimitMultiplier 10} CL_MUL_SHIFT(a : bv32, b : bv32) returns (r : bv64)
{
  var i := 0;
  var a' := a;
  var b' := b << i;
  r := 0;
  lemma_bv32_is_zero_or_upto_32_shifts_gives_zero(b);
  while b' != 0
   invariant i == 32 ==> b << i == 0;
   invariant i == 32 ==> b' == 0;
   invariant b' != 0  ==> 0 <= i <= 32;
   invariant b' != 0  ==> b' == b << i;
   decreases 32 - i;
  {
     if ((a' & 1) != 0) {
      r := r ^ (b' as bv64);
     }
    i := i + 1;
    a' := a' >> 1;
    b' := b << i;
 }
}
*/

// Proves for 8, 16, 32, 64!
function CL_MUL_SHIFT''(i : nat, a : bv64, b : bv64, r : bv128) : bv128
  requires 0 <= i <= 64;
  decreases 64 - i;
{
// lemma_bv64_is_zero_or_upto_64_shifts_gives_zero(b);
 if (b << i) != 0 then
   if ((a & 1) != 0) then
     CL_MUL_SHIFT''(i + 1, a >> 1, b, r ^ ((b << i) as bv128))
   else 
     CL_MUL_SHIFT''(i + 1, a >> 1, b, r)
 else 
  r
}

function CL_MUL_SHIFT'(a : bv64, b : bv64) : bv128
{
 CL_MUL_SHIFT''(0, a, b, 0 as bv128)
}

lemma lemma_bv8_is_zero_or_8_shifts_gives_zero(b : bv8)
  ensures b == 0 || (b << 8) == 0;
{
}

lemma lemma_bv8_is_zero_or_upto_8_shifts_gives_zero(b : bv8)
  ensures b == 0 || exists i : nat :: i <= 8 ==> b << i == 0; 
{
  if (b == 0) {
  } else {
    lemma_bv8_is_zero_or_8_shifts_gives_zero(b);
// Fails
//    forall j : nat | j == 8
//      ensures exists i : nat :: i <= 8 ==> b << i == 0; 
//    {
//      assert b << j == 0;
//    }
// Fails
//    var j : nat :| j == 8;
//    assert b << j == 0;
// Fails
//      var j : nat :| j <= 8;
//      assert b << 8 == 0;
// Fails
//      var j : nat :| j <= 8;
//      assert b << j == 0;
//   assert b != 0;
   assert 8 <= 8;
  }
}


}
