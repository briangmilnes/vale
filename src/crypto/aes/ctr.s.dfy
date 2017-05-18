include "../../lib/util/types.s.dfy"
include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"
include "aes.s.dfy"

module CTRModule {

import opened types_s
import opened AESModule

function Uint32ToUint64(low: uint32, high: uint32) : uint64
{
  (high * 0x1_0000_0000 + low) as uint64
}

function Uint64ToUint32(n : uint64) : seq<uint32>
{
  [(n / 0x1_0000_0000) as uint32,
  (n % 0x1_0000_0000) as uint32]
}

function CTR_increment_counter(counter: Quadword) : Quadword
{
  var ctr := Uint32ToUint64(counter.mid_hi,counter.hi); // TODO 
  var split := Uint64ToUint32(ctr);
  Quadword(counter.lo,counter.mid_lo, split[0], split[1])
}

function CTR_Encrypt_One_Block(key:seq<uint32>, input:Quadword, alg:Algorithm, counter:Quadword) : Quadword
    requires |key| == Nk(alg);
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
{
      QuadwordXor(input, AES_Encrypt(key, counter, alg))
}

function CTR_Encrypt(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, counter:Quadword) : seq<Quadword>
    requires |key| == Nk(alg);
    requires |input| > 0;
    requires |input| < 0x1_0000_0000_0000_0000;
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
{
    if |input| == 1 then
      [QuadwordXor(input[0], AES_Encrypt(key, counter, alg))]
    else
      var first := [QuadwordXor(input[0], AES_Encrypt(key, counter, alg))];
      var next_counter := CTR_increment_counter(counter);
      first + CTR_Encrypt(key, all_but_first(input), alg, next_counter)
}

// We don't need a decrypt predicate as we are using encrypt again.
}
