include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

// This really shows that bitvectors are not going to work well for
// us as fundamental representation in Dafny. Dafny is missing a
// translation of bv[i..j] into Z3 extract for a start.
// Other simple lemmas of conversion don't prove for example
// at sizes of 16.

module bitvectorsasfoundation {

import opened x64_def_s
import opened types_s
import opened x64_vale_i
import opened dafny_wrappers_i

// Get a new type name for each bv just to be clear.

type fbv1 = bv1
type fbv2 = bv2
type fbv4 = bv4
type fbv8 = bv8
type fbv16 = bv16
type fbv32 = bv32
type fbv64 = bv64
type fbv128 = bv128
type fbv256 = bv256

// And the same for integers. 

type fnat1   = i:nat | 0 <= i <= 1
type fnat2   = i:nat | 0 <= i < 4
type fnat4   = i:nat | 0 <= i < 16
type fnat8   = i:nat | 0 <= i < 0x100
type fnat16  = i:nat | 0 <= i < 0x10000
type fnat32  = i:nat | 0 <= i < 0x1_0000_0000
type fnat64  = i:nat | 0 <= i < 0x1_0000_0000_0000_0000
type fnat128 = i:nat | 0 <= i < 0x1_00000000_00000000_00000000_00000000
type fnat256 = i:nat | 0 <= i < 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000

// Coertions between.
function fbv1Tofnat1     (v : fbv1)   : fnat1   {v as fnat1}
function fbv2Tofnat2     (v : fbv2)   : fnat2   {v as fnat2}
function fbv4Tofnat4     (v : fbv4)   : fnat4   {v as fnat4}
function fbv8Tofnat8     (v : fbv8)   : fnat8   {v as fnat8}
function fbv16Tofnat16   (v : fbv16)  : fnat16  {v as fnat16}
function fbv32Tofnat32   (v : fbv32)  : fnat32  {v as fnat32}
function fbv64Tofnat64   (v : fbv64)  : fnat64  {v as fnat64}
function fbv128Tofnat128 (v : fbv128) : fnat128 {v as fnat128}
function fbv256Tofnat256 (v : fbv256) : fnat256 {v as fnat256}

function fnat1Tofbv1     (i : fnat1)   : fbv1   {i as fbv1}
function fnat2Tofbv2     (i : fnat2)   : fbv2   {i as fbv2}
function fnat4Tofbv4     (i : fnat4)   : fbv4   {i as fbv4}
function fnat8Tofbv8     (i : fnat8)   : fbv8   {i as fbv8}
function fnat16Tofbv16   (i : fnat16)  : fbv16  {i as fbv16}
function fnat32Tofbv32   (i : fnat32)  : fbv32  {i as fbv32}
function fnat64Tofbv64   (i : fnat64)  : fbv64  {i as fbv64}
function fnat128Tofbv128 (i : fnat128) : fbv128 {i as fbv128}
function fnat256Tofbv256 (i : fnat256) : fbv256 {i as fbv256}

// Can we prove coertion is reversible?
/*
lemma f1_coertion()
   ensures forall v : bv1 :: fnat1Tofbv1(fbv1Tofnat1(v)) == v;
   ensures forall i : fnat1 :: fbv1Tofnat1(fnat1Tofbv1(i)) == i;
{}

lemma f2_coertion()
   ensures forall v : bv2 :: fnat2Tofbv2(fbv2Tofnat2(v)) == v;
   ensures forall i : fnat2 :: fbv2Tofnat2(fnat2Tofbv2(i)) == i;
{}

lemma f4_coertion()
   ensures forall v : bv4 :: fnat4Tofbv4(fbv4Tofnat4(v)) == v;
   ensures forall i : fnat4 :: fbv4Tofnat4(fnat4Tofbv4(i)) == i;
{}
*/

/*
// Butterfly effect here, perhaps I should split things into their own modules?
lemma f8_coertion()
  ensures forall v : bv8 :: fnat8Tofbv8(fbv8Tofnat8(v)) == v;
  ensures forall i : fnat8 :: fbv8Tofnat8(fnat8Tofbv8(i)) == i;
{}
*/

lemma f16_coertion(v : bv16)
   ensures fnat16Tofbv16(fbv16Tofnat16(v)) == v;
//   ensures forall i : fnat16 :: fbv16Tofnat16(fnat16Tofbv16(i)) == i;
{}

/*
lemma {:timeLimitMultiplier 3} f16_coertion()
   ensures forall v : bv16 :: fnat16Tofbv16(fbv16Tofnat16(v)) == v;
//   ensures forall i : fnat16 :: fbv16Tofnat16(fnat16Tofbv16(i)) == i;
{}
*/

/* Won't prove in 90s.
lemma f8_coertion()
   ensures forall v : bv8 :: fnat8Tofbv8(fbv8Tofnat8(v)) == v;
   ensures forall i : fnat8 :: fbv8Tofnat8(fnat8Tofbv8(i)) == i;
{}

lemma {:timeLimitMultiplier 3} f16_coertion()
   ensures forall v : bv16 :: fnat16Tofbv16(fbv16Tofnat16(v)) == v;
   ensures forall i : fnat16 :: fbv16Tofnat16(fnat16Tofbv16(i)) == i;
{}

lemma {:timeLimitMultiplier 3} f32_coertion()
   ensures forall v : bv32 :: fnat32Tofbv32(fbv32Tofnat32(v)) == v;
   ensures forall i : fnat32 :: fbv32Tofnat32(fnat32Tofbv32(i)) == i;
{}

lemma {:timeLimitMultiplier 3} f64_coertion()
   ensures forall v : bv64 :: fnat64Tofbv64(fbv64Tofnat64(v)) == v;
   ensures forall i : fnat64 :: fbv64Tofnat64(fnat64Tofbv64(i)) == i;
{}

lemma {:timeLimitMultiplier 3} f128_coertion()
   ensures forall v : bv128 :: fnat128Tofbv128(fbv128Tofnat128(v)) == v;
   ensures forall i : fnat128 :: fbv128Tofnat128(fnat128Tofbv128(i)) == i;
{}

lemma {:timeLimitMultiplier 3} f256_coertion()
   ensures forall v : bv256 :: fnat256Tofbv256(fbv256Tofnat256(v)) == v;
   ensures forall i : fnat256 :: fbv256Tofnat256(fnat256Tofbv256(i)) == i;
{}
*/
/*
// Can we bit test with shifts arbitrarily?

predicate fbv1Bit  (v : fbv1, i : nat)   requires i == 0;      { v & 0x1 == 1}
predicate fbv2Bit  (v : fbv2, i : nat)   requires 0 <= i < 2;   { (v >> i) & 0x1 == 1}
predicate fbv4Bit  (v : fbv4, i : nat)   requires 0 <= i < 4;   { (v >> i) & 0x1 == 1}
predicate fbv8Bit  (v : fbv8, i : nat)   requires 0 <= i < 8;   { (v >> i) & 0x1 == 1}
predicate fbv16Bit (v : fbv16, i : nat)  requires 0 <= i < 16;  { (v >> i) & 0x1 == 1}
predicate fbv32Bit (v : fbv32, i : nat)  requires 0 <= i < 32;  { (v >> i) & 0x1 == 1}
predicate fbv64Bit (v : fbv64, i : nat)  requires 0 <= i < 64;  { (v >> i) & 0x1 == 1}
predicate fbv128Bit(v : fbv128, i : nat) requires 0 <= i < 128; { (v >> i) & 0x1 == 1}
predicate fbv256Bit(v : fbv256, i : nat) requires 0 <= i < 256; { (v >> i) & 0x1 == 1}

// What do I want to prove here?

lemma fb1_Bit() 
  ensures forall i: nat :: i < 1 ==> fbv1Bit(0x1,i); 
  ensures forall i: nat :: i < 1 ==> !fbv4Bit(0x0,i); 
{}

lemma fb2_Bit() 
  ensures forall i: nat :: i < 2 ==> fbv2Bit(0x3,i);
  ensures forall i: nat :: i < 2 ==> !fbv2Bit(0x0,i); 
{}

lemma fb4_Bit() 
  ensures forall i: nat :: i < 4 ==> fbv4Bit(0xF,i); 
  ensures forall i: nat :: i < 4 ==> !fbv4Bit(0x0,i); 
{}

lemma fb8_Bit() 
  ensures forall i: nat :: i < 8 ==> fbv8Bit(0xFF,i); 
  ensures forall i: nat :: i < 8 ==> !fbv8Bit(0x0,i); 
{}

lemma fb16_Bit() 
  ensures forall i: nat :: i < 16 ==> fbv16Bit(0xFFFF,i); 
  ensures forall i: nat :: i < 16 ==> !fbv16Bit(0x0,i); 
{}
*/

/* Times out after 90s.
lemma {:timeLimitMultiplier 3} fb32_Bit() 
  ensures forall i: nat :: i < 32 ==> fbv32Bit(0xFFFFFFFF,i); 
  ensures forall i: nat :: i < 32 ==> !fbv32Bit(0x0,i); 
{}

lemma {:timeLimitMultiplier 3} fb64_Bit() 
  ensures forall i: nat :: i < 64 ==> fbv64Bit(0xFFFFFFFFFFFFFFFF,i); 
  ensures forall i: nat :: i < 64 ==> !fbv64Bit(0x0,i); 
{}

lemma {:timeLimitMultiplier 3} fb128_Bit() 
  ensures forall i: nat :: i < 128 ==> fbv128Bit(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,i); 
  ensures forall i: nat :: i < 128 ==> !fbv128Bit(0x0,i); 
{}

lemma {:timeLimitMultiplier 3} fb256_Bit() 
  ensures forall i: nat :: i < 256 ==> fbv256Bit(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,i); 
  ensures forall i: nat :: i < 256 ==> !fbv256Bit(0x0,i); 
{}
*/

// Can we slice arbitrarily? Do we use shifts or mod, remainder? 
/*
function fbv1Slice(v : fbv1, hi : nat, low: nat) : fvb1
  requires 0 < hi <= 1;
  requires low <= hi;
  requires 0 <= low <= 1;
{
  (v % low) / hi;
}
*/

// And recover type size?

}
