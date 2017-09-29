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

// Some bitmath.
lemma lemma_BitwiseAdd32()
    ensures  forall x:uint32, y:uint32 :: x + y < 0x1_0000_0000 ==> BitwiseAdd32(x, y) == x + y
    ensures  forall x:uint32, y:uint32 :: x + y >= 0x1_0000_0000 ==> BitwiseAdd32(x, y) == x + y - 0x1_0000_0000;
    ensures  forall x:uint32 :: BitwiseAdd32(x, 0) == x;
{
    reveal_BitwiseAdd32();
}

lemma lemma_CBAt_fixed(i : uint32,  ICB : Quadword)
  ensures CB(i, ICB) == Quadword(BitwiseAdd32(1,i), ICB.mid_lo, ICB.mid_hi, ICB.hi);
{
  lemma_BitwiseAdd32();
  if (i == 0) {
    assert CB(0,ICB) == Quadword(1, ICB.mid_lo, ICB.mid_hi, ICB.hi);
  } else {
    lemma_CBAt_fixed(i-1, ICB);
  }
}


lemma lemma_BitXorWithZeroLeft(x:bv32)
    ensures BitXor(0,x) == x;
{
    reveal_BitXor();
}

lemma lemma_BitwiseXorWithZeroLeft(x:uint32)
    ensures BitwiseXor(0, x) == x;
{
    reveal_WordToBits();
    reveal_BitsToWord();
    calc {
        BitwiseXor(0,x);
        BitsToWord(BitXor(WordToBits(0), WordToBits(x)));
           { lemma_WordToBitsPreservesZeroness(0); assert WordToBits(0) == 0; }
        BitsToWord(BitXor(0, WordToBits(x)));
          { lemma_BitXorWithZeroLeft(WordToBits(x)); assert BitXor(0, WordToBits(x)) == WordToBits(x);}
        BitsToWord(WordToBits(x));
          { lemma_WordToBitsToWord(x); assert BitsToWord(WordToBits(x)) == x; } 
        x;
    }
}   

lemma lemma_QuadwordXorZeros(x:Quadword, y : Quadword)
    ensures y.lo     == 0 ==> QuadwordXor(x, y).lo     == x.lo;
    ensures y.mid_lo == 0 ==> QuadwordXor(x, y).mid_lo == x.mid_lo;
    ensures y.mid_hi == 0 ==> QuadwordXor(x, y).mid_hi == x.mid_hi;
    ensures y.hi     == 0 ==> QuadwordXor(x, y).hi     == x.hi;

    ensures x.lo     == 0 ==> QuadwordXor(x, y).lo     == y.lo;
    ensures x.mid_lo == 0 ==> QuadwordXor(x, y).mid_lo == y.mid_lo;
    ensures x.mid_hi == 0 ==> QuadwordXor(x, y).mid_hi == y.mid_hi;
    ensures x.hi     == 0 ==> QuadwordXor(x, y).hi     == y.hi;
{
 lemma_BitwiseXorWithZero(x.lo);
 lemma_BitwiseXorWithZero(x.mid_lo);
 lemma_BitwiseXorWithZero(x.mid_hi);
 lemma_BitwiseXorWithZero(x.hi);

 lemma_BitwiseXorWithZeroLeft(y.lo);
 lemma_BitwiseXorWithZeroLeft(y.mid_lo);
 lemma_BitwiseXorWithZeroLeft(y.mid_hi);
 lemma_BitwiseXorWithZeroLeft(y.hi);
}

/*
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
*/

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


// Bundle up all of the requirements for our ghosts via static/dynamic requirements
// and into a single predicate.

// Static
predicate GCMAlgSpecStat(g : GCMSpec) {
  g.alg == AES_128 &&
  |g.key| == Nk(g.alg) && 
  SeqLength(g.key) == Nk(g.alg) &&
  (Nb() * (Nr(g.alg) + 1)) / 4 == Nr(g.alg) + 1 &&
  (Nb() * (Nr(g.alg) + 1)) % 4 == 0   
}

predicate GCMKeySpecStat(g : GCMSpec) {
  g.exp_key_addr % 16 == 0 &&
  SeqLength(g.exp_key) == 44 
}

predicate GCMExpKeySpecStat(g : GCMSpec) 
  requires |g.key| == Nk(g.alg);
{
  KeyExpansionPredicate(g.key, g.alg, g.exp_key)
}

predicate GCMIVSpecStat(g : GCMSpec)
{
  g.ivsize == 128 && 
  g.ICB.lo == 0
}

predicate GCMInputSpecStat(g : GCMSpec) {
  g.iaddr <= g.iendaddr && 
  (g.iendaddr - g.iaddr) / 16 == g.isize
}

predicate GCMOutputSpecStat(g : GCMSpec) {
  g.osize == g.isize
}

predicate GCMHeapSpecStat(g : GCMSpec) {
 g.exp_key_heap != g.iheap && g.exp_key_heap != g.oheap && g.exp_key_heap != g.ivheap && 
 g.iheap != g.oheap && g.iheap != g.ivheap &&  
 g.oheap != g.ivheap
}

predicate GCMSpecStat(g : GCMSpec) {
 GCMAlgSpecStat(g) &&
 GCMKeySpecStat(g) &&
 GCMExpKeySpecStat(g) &&
 GCMIVSpecStat(g) &&
 GCMInputSpecStat(g) &&
 GCMOutputSpecStat(g) &&
 GCMHeapSpecStat(g)
}

// Dynamic

predicate GCMExpKeySpecDyn(g : GCMSpec, exp_key_ptr : uint64, mem : Heaplets) {
  GCMKeySpecStat(g) && 
  exp_key_ptr == g.exp_key_addr &&
  exp_key_ptr % 16 == 0 && 
  ValidSrcAddrs(mem, g.exp_key_heap, g.exp_key_addr, 128, Secret, 11*16) &&
  (forall j :: 0 <= j <= 10 ==> mem[g.exp_key_heap].quads[g.exp_key_addr + 16*j].v == 
         Quadword(g.exp_key[4*j], g.exp_key[4*j+1], g.exp_key[4*j+2], g.exp_key[4*j+3]))
}

predicate GCMIVSpecDyn(g : GCMSpec, ivptr : uint64, mem : Heaplets) {
  GCMIVSpecStat(g) &&
  g.ivaddr == ivptr &&
  ValidSrcAddr(mem, g.ivheap, g.ivaddr, g.ivsize, Secret) &&
//  ICB is in memory there. 
  mem[g.ivheap].quads[g.ivaddr] == QuadwordHeapletEntry(g.ICB, Secret)
}

predicate GCMInputSpecDyn(g : GCMSpec, iptr : uint64, iendptr : uint64, mem : Heaplets) {
 ValidSrcReg128(mem, g.iheap, g.iaddr, g.isize, Secret) 
 // iendptr >= iptr - hard to prove the equality.
 // TODO do I want to specify that iptr is in range?
}

predicate GCMOutputSpecDyn(g : GCMSpec, iptr : uint64, iendptr : uint64, optr : uint64, mem : Heaplets) {
 ValidSrcReg128(mem, g.oheap, g.oaddr, g.osize, Public)
 // TODO do I want to specify that opr is in range?
}

// How do our ptrs change with offset into the calculation? 
predicate GCMPtrSpecDyn(g : GCMSpec, 
   iptr : uint64, iendptr : uint64, optr : uint64,  ctr: uint32, off : nat, 
   mem : Heaplets) {
    off == (iptr - g.iaddr) / 12 && 
    ctr == off + 1 && // When we write the zeroth addr we are at ctr 1.
    optr == g.oaddr + off
}

predicate GCMSpecDyn(g : GCMSpec, 
  exp_key_ptr : uint64, iptr : uint64, iendptr : uint64, optr : uint64, ivptr : uint64, ctr: uint32,
  off : nat, 
  mem : Heaplets) {
// All of the static specs.
  GCMSpecStat(g) && 
// All of the dynamic specs.
  GCMExpKeySpecDyn(g, exp_key_ptr, mem) && 
  GCMIVSpecDyn(g, ivptr, mem) &&
  GCMInputSpecDyn(g, iptr, iendptr, mem) &&
  GCMOutputSpecDyn(g, iptr, iendptr, optr, mem) &&
  GCMPtrSpecDyn(g, iptr, iendptr, optr, ctr, off, mem)
}


// When we start off what do we have?
predicate GCMSpecDynInit(g : GCMSpec, 
  exp_key_ptr : uint64, iptr : uint64, iendptr : uint64, optr : uint64, ivptr : uint64, ctr: uint32,
  off : nat, 
  mem : Heaplets) {
  GCMSpecDyn(g, exp_key_ptr, iptr, iendptr, optr, ivptr, ctr, off, mem) && 
  iptr    == g.iaddr &&
  iendptr == g.iendaddr &&
  optr    == g.oaddr &&
  iendptr >= iptr
}

// And when we need operands, we need to know they are distinct.
// Even if tmp is a 32 bit register it is part of a 64 bit register.
predicate GCMRegUnique(exp_key_ptr : operand, iptr : operand, iendptr : operand, optr : operand, ivptr : operand, ctr: operand, tmp : operand) {
  exp_key_ptr != iptr && exp_key_ptr != iendptr && exp_key_ptr != optr && exp_key_ptr != ivptr && exp_key_ptr != ctr && exp_key_ptr != tmp &&
  iptr != iendptr && iptr != optr && iptr != ivptr && iptr != ctr && iptr != tmp &&
  iendptr != optr && iendptr != ivptr && iendptr != ctr && iendptr != tmp &&
  optr != ivptr && optr != tmp && ctr != tmp && 
  ivptr != tmp && ivptr != ctr &&
  ctr != tmp
}

// Works nicely to get rid of some lemma issues on va_code.
type uint8nonzero   = i:int | 0 < i <= 0x100 witness 1 

/*
lemma Writes_AESGCTR_step(mem : Heaplets, g : GCMSpec, off : nat, add : nat) 
   requires WritesReg128(mem, g.oheap, g.oaddr, g.isize, off + add, Secret, 
                          AESGCTRSeq(mem, g, g.isize));
   assert InMap(addr128(g.oaddr, off + add), mem[g.oheap].quads);
   assert mem[g.oheap].quads[addr128(g.oaddr, off + add)].t == Public;
   assert mem[g.oheap].quads[addr128(g.oaddr, off + add)].v == tmp;
   assert mem[g.oheap].quads[addr128(g.oaddr, off + add)].v == AESGCTR(mem, g, i);

   ensures WritesReg128(mem, g.oheap, g.oaddr, g.isize, off + add + 1, Secret, 
                          AESGCTRSeq(mem, g, g.isize));
{
}
*/

}
