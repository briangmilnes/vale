/*

   This is an example of how to specify your input to output mapping and
 then give it to WritesRegionN each time. Specify the entirety of your 
 range but then only the number of uint64 written. This makes it easier
 for Vale to understand the equivalence of values without sequence math. 
   
*/

include "../../lib/util/types.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "regions128.dfy"

module copy128 {

import opened types_s
import opened x64_def_s
import opened x64_vale_i
import opened regions128

function Copy128(mem : Heaplets, id: heaplet_id, base : nat, size: int, i : nat) : Quadword
 requires 0 <= i < size;
 requires ValidDstReg128(mem, id, base, size);
{
  mem[id].quads[(addr128(base, i))].v
}

// Generate the whole sequence with this function that knows what the values are to
// obviate any subsequence proof problems.

function Copy128Seq(mem : Heaplets, id: heaplet_id, base : nat, size : nat, count : nat) : seq<Quadword>
 requires ValidDstReg128(mem, id, base, size);
 requires 0 <= count <= size;
 ensures |Copy128Seq(mem, id, base, size, count)| == count;
 // Doing this here at the function definition is CRITICAL as it proves and then is available
 // when you need it in the requirements as
 ensures forall i : nat :: 0 <= i < count ==>
         Copy128Seq(mem, id, base, size, count)[i] == Copy128(mem, id, base, size, i);
{
  if (count == 0) then
    []
  else 
    Copy128Seq(mem, id, base, size, count - 1) + [Copy128(mem, id, base, size, count - 1)]
}

}
