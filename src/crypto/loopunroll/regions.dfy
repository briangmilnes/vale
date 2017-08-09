/*

	Rebuild specifications with the concept of a Region and a pointer within a region.

*/

include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x86/def.s.dfy"
include "../../arch/x86/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

include "regions.base.dfy"

module regionsdfy {

import opened types_s
import opened x86_def_s
import opened x86_vale_i
import opened dafny_wrappers_i
import opened regionsbasedfy

}
