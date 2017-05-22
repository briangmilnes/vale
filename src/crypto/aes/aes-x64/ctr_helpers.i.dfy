include "../../../arch/x64/vale.i.dfy"
include "../../../lib/util/dafny_wrappers.i.dfy"
include "../cbc.s.dfy"
include "../aes.s.dfy"
include "../aes_helpers.i.dfy"

include "../ctr.s.dfy"

module CTR_Helpers {
import opened x64vale_CTR_temp = x64_vale_i
import opened parser_help_i_CTR_temp = dafny_wrappers_i 
import opened CBCModule_CTR_helpers_tmp = CBCModule
import opened AESModule_CTR_helpers_tmp = AESModule
import opened AESHelpersModule_CTR_helpers_tmp = AESHelpersModule

import opened CTRModule


}
