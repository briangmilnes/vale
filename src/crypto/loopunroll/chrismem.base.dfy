include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "../../arch/x86/def.s.dfy"
include "../../arch/x86/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"

// Just so I don't have to recompile much.
module chrismembasedfy {

import opened types_s
import opened x86_def_s
import opened x86_vale_i
import opened dafny_wrappers_i

lemma lemma_addr32_off(off : int)
  ensures forall src : int :: addr32(src,off) == addr32(src + 4 * off, 0);
{
}

function addr32(base:int, i:int):int { base + 4 * i }

}

