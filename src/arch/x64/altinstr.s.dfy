//
// An attempt to specify instructions that are closer to Intel x64.
//
// We'll use only x86 and x64 features, no SIMD vector extensions and
// no mm registers. No segments, no relative addressing for jumps.
//
// Intel® 64 and IA-32 Architectures Software Developer Manuals, section 3.1.1.
//
//

include "../../lib/util/types.s.dfy"

module x64_def_s_alt {

import opened types_s

type int8   = i:int | -128 <= i <= 127
type int16  = i:int | -32768 <= i <= 32767
type int32  = i:int | -2147483648 <= i <= 2147483647
type int64  = i:int | -9223372036854775808 <= i <= 9223372036854775807	

datatype taint = Public | Secret

// These are actually all of the registers in an X64 except for the mm and the ymm.
datatype reg8   = AL | CL | DL | BL | AH | CH | DH | BH | BPL | SPL | DIL | SIL | R8L | R9L | R10L | R11L | R12L | R13L | R14L | R15L
datatype reg16  = X | CX | DX | BX | SP | BP | SI | DI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
datatype reg32  = EAX | ECX | EDX | EBX | ESP | EBP | ESI | EDI | R8D | R9D | R10D | R11D | R12D | R13D | R14D | R15D
datatype reg64  = RAX | RBX | RCX | RDX | RDI | RSI | RBP | RSP | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
datatype reg128 = xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7 | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
datatype reg    = reg8(r8: reg8) | reg16(r16: reg16) | reg32(r32 : reg32) | reg64(r64 : reg64) | reg128(r128 : reg128)

datatype imm    = imm8(n8:int8) | imm16(n16:int16) | imm32(n32:int32) | imm64(n64:int64)

datatype opt<T> = Some(reg:T) | None

type scaling = i : nat | i == 1 || i == 2 || i == 4 || i == 8 witness 1

datatype m8     = m8(r8: reg8)       | m8Ind(base: reg8, index: opt<reg8>, displ: uint8, scale : scaling)
datatype m16    = m16(r16: reg16)    | m16Ind(base: reg16, index: opt<reg16>, displ: uint16, scale : scaling)
datatype m32    = m32(r32: reg32)    | m32Ind(base: reg32, index: opt<reg32>, displ: uint32, scale : scaling)
datatype m64    = m64(r64: reg64)    | m64Ind(base: reg64, index: opt<reg64>, displ: uint64, scale : scaling)
datatype m128   = m128(r128: reg128) | m128Ind(base: reg128, index: opt<reg128>, displ: uint128, scale : scaling)
datatype m      = m8(m8: m8) | m16(m16: m16) | m32(m32 : m32) | m64(m64 : m64) | m128(m128 : m128)

// Testing creating these types, show's its a bit wordy. You have to index the non-unique constructors from
// the type.
function mkm8() : m8 { m8.m8(AL)}
function mkm() : m { m.m8(m8.m8(AL)) }

// Intel r/m notations but we can't use /.
datatype r_m8    = r8(r: reg8) | m8(m: m8)
datatype r_m16   = r16(r: reg16) | m16(m: m16)
datatype r_m32   = r32(r: reg32) | m32(m: m32)
datatype r_m64   = r64(r: reg64) | m64(m: m64)
datatype r_m     = r(r: reg) | m(m: m)

type xmm = reg128
datatype xmm_m32   = xmm32(xm: reg32) | m32(m: m32)
datatype xmm_m64   = xmm64(xm: reg64) | m64(m: m64)
datatype xmm_m128  = xmm128(xm: reg128) | m128(m: m128)
datatype xmm_m     = xmm_m32(xm32: xmm_m32) | xmmm64(xm64 : xmm_m64)
  
type stackoffset = i : nat | 0 <= i <= 7
datatype ST     = ST(o : stackoffset)

datatype ins = MOVDQU(dst : xmm_m128, src : xmm_m128)

// Intel allows these addressing modes:
//MOVDQU xmm1, xmm2/m128
//MOVDQU xmm2/m128, xmm1
// Which in our patterns are xmmm

// Then we could write things like:
//procedure{:instruction Ins(MOVDQU(dst, src))} MOVDQU(inout dst : xmm_m128, src : xmm_m128) 
// And in this case, one must be a register: 
//  requires
//     dst.xmm128? || src.xmm128?;
//
function mkMOVDQU() : ins {
  MOVDQU(xmm128(xmm0), xmm_m128.m128(m128Ind(xmm1,None,0,8)))
}

predicate ValidMOVDQU(dst : xmm_m128, src : xmm_m128) {
  dst.xmm128? || src.xmm128?
}

// If we don't want a really painful disjunction of possible addressing modes
// per instruction, for example, MOV has 19 addressing modes that we could model
// using this.
// We could name the procedures with their addressing mode.
//procedure MOVDQU_xmm_m128...

// In def.s.dfy:
//function operandObs(s:state, size:int, o:operand) : seq<observation> would be
// very similar. but
// function operandObs(s:state, size:int, o:operand) : seq<observation> would just
// walk the addressing modes.
//
// We'd need an eval_ for each addressing mode we want to support. 

// And we'd be guaranteeing to only be able to write valid instructions, unlike
// the current system.

// Finally we could build a parser and type inference engine that reads GCC/MASM
// code and builds our type safe notation. That way we can just import wholesale
// instruction sequences.

// With that we would only need to add the instructions in any code we were trying
// to import.

}
