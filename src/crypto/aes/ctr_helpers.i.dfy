include "../../arch/x64/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"
include "ctr.s.dfy"

module CTR_Helpers {

import opened x64_vale_i
import opened CTRModule

// Abstract description of a one block encryption.

predicate CTR_Encrypt_One_Block_Final(key:seq<uint32>, input:Quadword, counter:Quadword, alg:Algorithm,
  mem:Heaplets, id:heaplet_id, output_ptr:int, output:Quadword)
    requires |key| == Nk(alg);
{
 output == CTR_Encrypt_One_Block(key, input, alg, counter) &&
 ValidSrcAddr(mem, id, output_ptr, 128, Secret) &&
 output == mem[id].quads[output_ptr].v
}

}
