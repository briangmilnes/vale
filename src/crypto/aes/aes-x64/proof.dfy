include "../../../lib/util/types.s.dfy"
include "../../../lib/util/operations.s.dfy"
include "../../../lib/util/words_and_bytes.s.dfy"
include "../../../lib/collections/Seqs.s.dfy"
include "../../../arch/x64/vale.i.dfy"
include "../../../arch/x64/vale64.i.dfy"
include "../../../lib/util/dafny_wrappers.i.dfy"
include "../ctr.s.dfy"
include "../aes.s.dfy"
include "../gcm3.s.dfy" 
include "gcm_helpers.i.dfy"

module proof {

import opened x64_vale_i
import opened x64_def_s
import opened types_s
import opened dafny_wrappers_i
import opened AESModule
import opened GCMModule
import opened GCMHelpers

}

