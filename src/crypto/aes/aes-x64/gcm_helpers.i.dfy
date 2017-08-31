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

// It's not clear to me what is the best way to allow proof.
// 0b00010000 
function uint8Tobv8(b : uint8) : bv8 { b as bv8 }

/* Whoa, where are bit vectors specified?
predicate isbv8eq0(b : bv8) {
  b[0] == 0
}

method CL_MUL_SHIFT(a : bv64, b : bv64) returns (r : bv128)
{
   var a' := a;
   var b' := b;
   r := 0;
    while b' != 0
  {
     if ((a' & 1) != 0) {
          r := r ^ b';
     }
    a' := a' >> 1;
    b' := b' << 1;
 }
}

method CL_MUL(src1 : bv128, src2 : bv128, imm8 : bv8) returns (dest : bv128) 
{
  var temp1 : bv64;
  var temp2 : bv128;

  if (imm8[0] == 0) {
    temp1 := src1[63:0];
  } else {
    temp1 := src1[127:64];
  }

  if (imm8[4] == 0) {
    temp2 := src2[63:0];
  } else {
    temp2 := src2[127:64];
  }

  var dest : bv128;
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


// Find a new index that is open, 32 bit. 
// Assume the rest after that is clear, which may cause proof issues.
function FrameMax(f : Frame, upto : int) : int 
  decreases |f|;
{
  if !(upto in f) then upto else FrameMax(map i | i in f && i != upto :: f[i], upto + 1)
}

}
