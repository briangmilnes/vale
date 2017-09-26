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

lemma lemma_bv128_conversion(x : bv128)
  ensures (x as uint128) as bv128 == x;
{ if (x == 0) {
 }
  else {
    lemma_bv128_conversion(x >> 1);
  }
}

/*
lemma lemma_bv128_shr_zero(x : bv128)
  ensures x >> 0 == x;
{}

lemma {:timeLimitMultiplier 3} lemma_uint128_shr_zero(x : uint128)
  ensures ((x as bv128) >> 0) as uint128 == x;
{
  lemma_bv128_shr_zero(x as bv128);
}
*/

}
