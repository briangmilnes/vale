/*

   This is an example of how to specify your input to output mapping and
 then give it to WritesRegionN each time. Specify the entirety of your 
 range but then only the number of uint64 written. This makes it easier
 for Vale to understand the equivalence of values without sequence math. 
   
*/

include "../../lib/util/types.s.dfy"
include "../../arch/x64/def.s.dfy"
include "../../arch/x64/vale.i.dfy"
include "regions64.dfy"


module copy64 {

import opened types_s
import opened x64_def_s
import opened x64_vale_i
import opened regions64

function Copy64(mem : Heaplets, id: heaplet_id, base : nat, size: int, i : nat) : uint64
 requires 0 <= i < size;
 requires ValidDstReg64(mem, id, base, size);
{
  mem[id].mem64[(addr64(base, i))].v
}

// Generate the whole sequence with this function that knows what the values are to
// obviate any subsequence proof problems.

function Copy64Seq(mem : Heaplets, id: heaplet_id, base : nat, size : nat, count : nat) : seq<uint64>
 requires ValidDstReg64(mem, id, base, size);
 requires 0 <= count <= size;
 ensures |Copy64Seq(mem, id, base, size, count)| == count;
 // Doing this here at the function definition is CRITICAL as it proves and then is available
 // when you need it in the requirements as
 ensures forall i : nat :: 0 <= i < count ==>
         Copy64Seq(mem, id, base, size, count)[i] == Copy64(mem, id, base, size, i);
{
  if (count == 0) then
    []
  else 
    Copy64Seq(mem, id, base, size, count - 1) + [Copy64(mem, id, base, size, count - 1)]
}

}
