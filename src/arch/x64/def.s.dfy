// Trusted specification for x86 semantics

include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../crypto/aes/aes.s.dfy"

module x64_def_s {

import opened operations_s
import opened AESModule

datatype taint = Public | Secret
datatype x86reg =
  X86Eax | X86Ebx | X86Ecx | X86Edx | X86Esi | X86Edi | X86Ebp
| X86R8 | X86R9 | X86R10 | X86R11 | X86R12 | X86R13 | X86R14 | X86R15
| X86Xmm(xmm:int)
datatype maddr = MConst(n:int) | MReg(reg:x86reg, offset:int) | MIndex(base:x86reg, scale:int, index:x86reg, index_offset:int)
datatype operand = OConst(n:uint64) | OReg(r:x86reg) | OStack(s:int) | OHeap(addr:maddr, taint:taint)
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt
datatype obool = OCmp(cmp:ocmp, o1:operand, o2:operand)

datatype ins =
  Rand(xRand:operand)
| Mov32(dstMov:operand, srcMov:operand)
| Mov64(dstMov64:operand, srcMov64:operand)
| MOVQ64XMM(dstMovq64:operand, srcMovqXMM: operand)
| MOVQXMM64(dstMovqXMM:operand, srcMovq64: operand)
| MOVHLPS(dstMovHLPS:operand, srcMovHLPS:operand)
| MOVLHPS(dstMovLHPS:operand, srcMovLHPS:operand)
| Add32(dstAdd:operand, srcAdd:operand)
| Add64(dstAdd64:operand, srcAdd64:operand)
| AddLea64(dstAddLea64:operand, src1AddLea64:operand, src2AddLea64:operand)
| Sub32(dstSub:operand, srcSub:operand)
| Sub64(dstSub64:operand, srcSub64:operand)
| Mul32(srcMul:operand)
| Mul64(srcMul64:operand)
| Div64(srcDiv64:operand)
| IMul64(dstIMul64:operand, srcIMul64:operand)
| AddCarry(dstAddCarry:operand, srcAddCarry:operand)
| AddCarry64(dstAddCarry64:operand, srcAddCarry64:operand)
| BSwap32(dstBSwap:operand)
| BSwap64(dst64BSwap:operand)
| Xor32(dstXor:operand, srcXor:operand)
| Xor64(dstXorq:operand, srcXorq:operand)
| And32(dstAnd:operand, srcAnd:operand)
| And64(dstAnd64:operand, srcAnd64:operand)
| Not32(dstNot:operand)
| GetCf(dstCf:operand) // corresponds to SETC instruction
| Rol32(dstRolConst:operand, amountRolConst:operand)
| Ror32(dstRorConst:operand, amountRorConst:operand)
| Shl32(dstShlConst:operand, amountShlConst:operand)
| Shl64(dstShlConst64:operand, amountShlConst64:operand)
| Shr32(dstShrConst:operand, amountShrConst:operand)
| Shr64(dstShrConst64:operand, amountShrConst64:operand)
| AESNI_enc(dstEnc:operand, srcEnc:operand)
| AESNI_enc_last(dstEncLast:operand, srcEncLast:operand)
| AESNI_dec(dstDec:operand, srcDec:operand)
| AESNI_dec_last(dstDecLast:operand, srcDecLast:operand)
| AESNI_imc(dstImc:operand, srcImc:operand)
| AESNI_keygen_assist(dstKeygenAssist:operand, srcKeygenAssist:operand, imm8KeygenAssist:operand)
| Pxor(dstPXor:operand, srcPXor:operand)
| Pshufd(dstPshufd:operand, srcPshufd:operand, permutationPshufd:operand)
| VPSLLDQ(dstVPSLLDQ:operand, srcVPSLLDQ:operand, countVPSLLDQ:operand)
// New instructions for aes-gcm.
| MOVDQU(dstMovdqu:operand, srcMovdqu:operand)
| MOVD_xmm_rmm32(dstMOVDxmmmrmm32:operand, srcMOVDxmmrmm32:operand)
| PCLMULQDQ(dstPCLMULQDQ : operand, srcPCLMULQDQ : operand, imm8: operand)
| VPCLMULQDQ(dstVPCLMULQDQ : operand, src1VPCLMULQDQ : operand, src2VPCLMULQDQ : operand, imm8: operand)
| VMOVDQA(dstVMOVDQA : operand, srcVMODQA : operand)
| VPSHUFD(dstVPSHUFD : operand, srcVPSHUFD : operand, imm8: operand)
| VPXOR  (dstVPXOR : operand, src1VPXOR : operand, src2VPXOR : operand)
| MOVDQA (dstMOVDQA : operand, srcMOVDQA : operand)
| POR    (dstPOR : operand, srcPOR : operand)
| PSLLD  (dstPSLLD:operand, imm8: operand)
| PSLLDQ (dstPSLLDQ:operand, imm8: operand)
| PSRLD  (dstPSRLD:operand, imm8: operand)
| PSRLDQ (dstPSRLDQ:operand, imm8: operand)
| PUSH   (srcPUSH: operand)  // r64
| POP    (dstPOP: operand)   // r64
| MOV_m64_imm32(dstLoc: operand, imm32 : operand)

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

datatype observation =
    BranchPredicate(pred:bool)
  | HeapAccess(addr:uint64)
  | HeapAccessOffset(base:uint64, index:uint64)

type Frame = map<int, uint32>
type Stack = seq<Frame>
datatype heapEntry = HeapEntry(v:uint8, t:taint)
type heap = map<int,heapEntry>
datatype state = state(regs:map<x86reg, uint64>, xmms:map<int, Quadword>, flags:uint32, stack:Stack, heap:heap, trace:seq<observation>, ok:bool)

predicate IsUInt32(i:int) { 0 <= i < 0x1_0000_0000 }

predicate ValidRegister(regs:map<x86reg, uint64>, r:x86reg)
{
    r in regs
}

function eval_reg(regs:map<x86reg, uint64>, r:x86reg) : uint64
{
    if !ValidRegister(regs, r) then 24
    else regs[r]
}

predicate ValidMemAddr(addr:maddr)
{
    match addr
        case MConst(n) => true
        case MReg(r, offset) => !r.X86Xmm?
        case MIndex(base, scale, index, offset) => !base.X86Xmm? && !index.X86Xmm?
}

function EvalMemAddr(regs:map<x86reg, uint64>, addr:maddr) : int
    requires ValidMemAddr(addr);
{
    match addr
        case MConst(n) => n
        case MReg(r, offset) => eval_reg(regs, r) + offset
        case MIndex(base, scale, index, offset) => 
             eval_reg(regs, base) + scale * eval_reg(regs, index) + offset
}

predicate ValidResolvedAddr(h:heap, resolved_addr:int)
{
    resolved_addr     in h
 && resolved_addr + 1 in h
 && resolved_addr + 2 in h
 && resolved_addr + 3 in h
}

predicate ValidHeapAddr(s:state, addr:maddr)
{
    ValidMemAddr(addr)
    && var resolved_addr := EvalMemAddr(s.regs, addr);
       ValidResolvedAddr(s.heap, resolved_addr) 
}

predicate ValidXmmRegisterIndex(index:int)
{
    0 <= index <= 7
}

predicate ValidXmm(xmms:map<int,Quadword>, r:x86reg)
    requires r.X86Xmm?;
{
    r.xmm in xmms && ValidXmmRegisterIndex(r.xmm)
}

predicate ValidOperand(s:state, size:int, o:operand)
{
    match o
        case OConst(n) => (size == 32 ==> IsUInt32(o.n))
        case OReg(r) =>
            if size == 32 || size == 64 then
                !r.X86Xmm? && ValidRegister(s.regs, r)
            else if size == 64 then
                !r.X86Xmm? && ValidRegister(s.regs, r)
            else if size == 128 then
                r.X86Xmm? && ValidXmm(s.xmms, r)
            else
                false
        case OStack(slot) => 
            if size == 32 then
                |s.stack| > 0 && slot in s.stack[0]
            else if size == 64 then
                |s.stack| > 0 && slot in s.stack[0] && slot + 1 in s.stack[0]
            else if size == 128 then
                Valid128BitStackOperand(s, o)
            else
                false
        case OHeap(addr, _) => 
            if size == 32 then
                ValidHeapAddr(s, addr)
            else if size == 64 then
                Valid64BitHeapOperand(s, o)
            else if size == 128 then
                Valid128BitHeapOperand(s, o)
            else false
}

function GetValueAtResolvedAddress(h:heap, resolved_addr:int) : uint32
    requires ValidResolvedAddr(h, resolved_addr);
{
    BytesToWord(h[resolved_addr+3].v,
                h[resolved_addr+2].v,
                h[resolved_addr+1].v, 
                h[resolved_addr].v)
}
function GetValueAtHeapAddress(s:state, addr:maddr) : uint32
    requires ValidHeapAddr(s, addr);
{
    var resolved_addr := EvalMemAddr(s.regs, addr);
    GetValueAtResolvedAddress(s.heap, resolved_addr)
}

predicate TaintMatch(s:state, size:int, o:operand)
    requires ValidOperand(s, size, o)
{
    o.OHeap? ==>
        (   ValidHeapAddr(s, o.addr)
         && var resolved_addr := EvalMemAddr(s.regs, o.addr);
            forall n: int :: 0 <= n < size/8 ==> s.heap[resolved_addr+n].t == o.taint)
}

predicate ValidImm8(s:state, o:operand)
{
       o.OConst?
    && 0 <= o.n < 256
}

predicate ValidShiftAmountOperand(s:state, o:operand)
{
       (   o.OConst?
        && 0 <= o.n < 32)
    || (   o == OReg(X86Ecx)
        && o.r in s.regs
        && IsUInt32(s.regs[o.r]))
}

predicate ValidShiftAmountOperand64(s:state, o:operand)
{
       (   o.OConst?
        && 0 <= o.n < 64)
    || (   o == OReg(X86Ecx)
        && o.r in s.regs
        && IsUInt32(s.regs[o.r]))
}

//TODO: Will contain taint match logic
predicate ValidSourceOperand(s:state, size:int, o:operand)
{
       ValidOperand(s, size, o)
    && (size == 32 && o.OReg? ==> IsUInt32(s.regs[o.r]))
    && TaintMatch(s, size, o)
}

predicate Valid32BitSourceOperand(s:state, o:operand)
{
     ValidSourceOperand(s, 32, o)
}

predicate Valid64BitSourceOperand(s:state, o:operand)
{
     ValidSourceOperand(s, 64, o)
}

predicate ValidDestinationOperand(s:state, size:int, o:operand)
{
      !o.OConst?
    && ValidOperand(s, size, o)
}

predicate Valid32BitDestinationOperand(s:state, o:operand)
{
    ValidDestinationOperand(s, 32, o)
}

predicate Valid64BitDestinationOperand(s:state, o:operand)
{
    ValidDestinationOperand(s, 64, o)
}

predicate method IsXmmOperand(o:operand)
{
    o.OReg? && o.r.X86Xmm?
}

predicate ValidXmmOperand(s:state, o:operand)
{
       IsXmmOperand(o)
    && ValidXmm(s.xmms, o.r)
}

predicate ValidXmmSourceOperand(s:state, o:operand)
{
       ValidSourceOperand(s, 128, o)
    && ValidXmmOperand(s, o)
}

predicate ValidXmmDestinationOperand(s:state, o:operand)
{
       ValidDestinationOperand(s, 128, o)
    && ValidXmmOperand(s, o)
}

predicate Valid128BitStackOperand(s:state, o:operand)
    requires o.OStack?;
{
      |s.stack| > 0
    && o.s in s.stack[0]
    && o.s+1 in s.stack[0]
    && o.s+2 in s.stack[0]
    && o.s+3 in s.stack[0]
}

predicate Valid64BitHeapOperand(s:state, o:operand)
    requires o.OHeap?;
{
    ValidMemAddr(o.addr)
  && var m0 := EvalMemAddr(s.regs, o.addr);
     var m1 := m0 + 4;
        ValidResolvedAddr(s.heap, m0)
     && ValidResolvedAddr(s.heap, m1)
}

predicate Valid128BitHeapOperand(s:state, o:operand)
    requires o.OHeap?;
{
    ValidMemAddr(o.addr)
  && var m0 := EvalMemAddr(s.regs, o.addr);
     var m1 := m0 + 4;
     var m2 := m0 + 8;
     var m3 := m0 + 12;
        ValidResolvedAddr(s.heap, m0)
     && ValidResolvedAddr(s.heap, m1)
     && ValidResolvedAddr(s.heap, m2)
     && ValidResolvedAddr(s.heap, m3)
}


function eval_op32(s:state, o:operand) : uint32
    requires !(o.OReg? && o.r.X86Xmm?);
{
    if !ValidSourceOperand(s, 32, o) then
        42
    else
        match o
            case OConst(n) => n
            case OReg(r) => s.regs[r]
            case OStack(slot) => s.stack[0][slot]
            case OHeap(addr, taint) => GetValueAtHeapAddress(s, addr)
}

function{:opaque} lower64(i:uint64):uint32 { i % 0x1_0000_0000 }
function{:opaque} upper64(i:uint64):uint32 { i / 0x1_0000_0000 }
function{:opaque} lowerUpper64(l:uint32, u:uint32):uint64 { l + 0x1_0000_0000 * u }

function lower64trans(i:uint64):uint32 { i % 0x1_0000_0000 }
function upper64trans(i:uint64):uint32 { i / 0x1_0000_0000 }
function lowerUpper64trans(l:uint32, u:uint32):uint64 { l + 0x1_0000_0000 * u }

// Ugly to have to do this typing but Dafny seems to treat the
// uint32s in the map display expression as ints.
function make64BitFrame(v : uint64) : Frame
    ensures 0 in make64BitFrame(v);
    ensures 1 in make64BitFrame(v);
    ensures make64BitFrame(v)[0] == lower64trans(v);
    ensures make64BitFrame(v)[1] == upper64trans(v);
{
  var low  : uint32  := lower64trans(v);
  var high : uint32  := upper64trans(v);
  var m    : map<int,uint32> := map[];
  m[0 := low][1 := high]
}

predicate evalPush(s : state, src : operand, v: uint64, r:state, obs:seq<observation>)
    requires src.OReg?;
    requires ValidRegister(s.regs, src.r);
    requires Valid64BitSourceOperand(s, src);
{
    r == s.(trace := s.trace + obs, stack := [make64BitFrame(v)] + s.stack)
}

// Bryan, Will this work to give me my entailments.
lemma lemma_evalPush(s : state, src : operand, v: uint64, r:state, obs:seq<observation>)
  requires src.OReg?;
  requires ValidRegister(s.regs, src.r);
  requires Valid64BitSourceOperand(s, src);
  requires evalPush(s,src,v,r,obs);
  ensures r.trace == s.trace + obs;
  ensures r.regs == s.regs;
  ensures r.stack == [make64BitFrame(v)] + s.stack;
  ensures |r.stack| == |s.stack| + 1;
  ensures |r.stack| > 0;
  ensures 0 in r.stack[0];
  ensures 1 in r.stack[0];
  ensures r.stack[0][0] == lower64trans(v);
  ensures r.stack[0][1] == upper64trans(v);
  ensures v == lowerUpper64trans(r.stack[0][0],r.stack[0][1]);
{}

predicate evalPop(s : state, src : operand, r:state, obs:seq<observation>)
    requires src.OReg?;
    requires ValidRegister(s.regs, src.r);
    requires Valid64BitDestinationOperand(s, src);
    // I am not valid if I pop the last frame of the stack.
    requires (|s.stack| > 1 && 0 in s.stack[0] && 1 in s.stack[0]);
    ensures |s.stack| > 0;
{
  var f : Frame := s.stack[0];
  match src
    case OReg(reg)    => r == s.(regs := s.regs[reg := lowerUpper64(f[0],f[1])],
      stack := s.stack[1..|s.stack|],
      trace := s.trace + obs)
    case OStack(slot)       => r == s.(ok := false) // not yet supported
    case OHeap(addr, taint) => r == s.(ok := false) // not yet supported
    case OConst(n)          => r == s.(ok := false) // not yet supported
}

function eval_op64(s:state, o:operand) : uint64
    requires !(o.OReg? && o.r.X86Xmm?)
{
    if !ValidSourceOperand(s, 64, o) then
        42
    else
        match o
            case OConst(n) => n
            case OReg(r) => s.regs[r]
            case OStack(slot) => lowerUpper64(s.stack[0][slot], s.stack[0][slot + 1])
            case OHeap(addr, taint) =>
                var resolved_addr := EvalMemAddr(s.regs, addr);
                lowerUpper64(GetValueAtResolvedAddress(s.heap, resolved_addr), GetValueAtResolvedAddress(s.heap, resolved_addr + 4))
}


function eval_op128(s:state, o:operand) : Quadword 

{
  match o
    case OConst(n)          => Quadword(0,0,0,42)
    case OStack(slot)       => Quadword(0,0,0,42)
    case OHeap(addr, taint) => Quadword(0,0,0,42)
    case OReg(r) =>
      if r.X86Xmm? && ValidXmm(s.xmms, r) then
      s.xmms[r.xmm]
      else Quadword(0,0,0,42)
}


function UpdateHeap32(h:heap, addr:int, v:uint32, t:taint) : heap
{
    var big_endian_bytes := WordToBytes(v);
    h[addr     := HeapEntry(big_endian_bytes[3], t)]
     [addr + 1 := HeapEntry(big_endian_bytes[2], t)]
     [addr + 2 := HeapEntry(big_endian_bytes[1], t)]
     [addr + 3 := HeapEntry(big_endian_bytes[0], t)]
}

function UpdateHeap64(h:heap, resolved_addr:int, v:uint64, t:taint) : heap
{
    UpdateHeap32(UpdateHeap32(h, resolved_addr, lower64(v), t), resolved_addr + 4, upper64(v), t)
}

predicate evalUpdateAndMaintainFlags(s:state, o:operand, v:uint32, r:state, obs:seq<observation>)
    requires Valid32BitDestinationOperand(s, o);
    requires !(o.OReg? && o.r.X86Xmm?);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v], trace := s.trace + obs)
        case OStack(slot) => r == s.(stack := [s.stack[0][slot := v]] + s.stack[1..], trace := s.trace + obs)
        case OHeap(addr, taint)  => r == s.(heap := UpdateHeap32(s.heap, EvalMemAddr(s.regs, o.addr), v, taint), trace := s.trace + obs)
}

predicate evalUpdateAndMaintainFlags64(s:state, o:operand, v:uint64, r:state, obs:seq<observation>)
    requires Valid64BitDestinationOperand(s, o);
    requires !(o.OReg? && o.r.X86Xmm?);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v], trace := s.trace + obs)
        case OStack(slot) => r == s.(stack := [s.stack[0][slot := lower64(v)][slot + 1 := upper64(v)]] + s.stack[1..], trace := s.trace + obs)
        case OHeap(addr, taint)  => r == s.(heap := UpdateHeap64(s.heap, EvalMemAddr(s.regs, addr), v, taint))
}

predicate evalUpdateAndHavocFlags(s:state, o:operand, v:uint32, r:state, obs:seq<observation>)
    requires Valid32BitDestinationOperand(s, o);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v], flags := r.flags, trace := s.trace + obs)
        case OStack(slot) => r == s.(stack := [s.stack[0][slot := v]] + s.stack[1..], flags := r.flags, trace := s.trace + obs)
        case OHeap(addr, taint)  => r == s.(heap := UpdateHeap32(s.heap, EvalMemAddr(s.regs, o.addr), v, taint), flags := r.flags, trace := s.trace + obs)
}

predicate evalUpdateAndHavocFlags64(s:state, o:operand, v:uint64, r:state, obs:seq<observation>)
    requires Valid64BitDestinationOperand(s, o);
{
    match o
        case OReg(reg)    => r == s.(regs := s.regs[reg := v], flags := r.flags, trace := s.trace + obs)
        case OStack(slot) => r == s.(ok := false) // not yet supported
        case OHeap(addr, taint)  => r == s.(ok := false) // not yet supported
}

predicate evalUpdateAndMaintainFlagsDiv(s:state, src: operand, div:uint64, mod: uint64, r:state, obs:seq<observation>)
    requires src.OReg?;
    requires ValidRegister(s.regs, src.r);
    requires Valid64BitSourceOperand(s, src);
{
    match src
        case OReg(reg)    => r == s.(regs := s.regs[X86Eax := div][X86Edx:= mod], trace := s.trace + obs)
        case OStack(slot)       => r == s.(ok := false) // not yet supported
        case OHeap(addr, taint) => r == s.(ok := false) // not yet supported
        case OConst(n)          => r == s.(ok := false) // not yet supported
}

predicate evalUpdateXmmsAndHavocFlags(s:state, o:operand, v:Quadword, r:state, obs:seq<observation>)
    requires ValidXmmOperand(s, o);
{
    r == s.(xmms := s.xmms[o.r.xmm := v], flags := r.flags, trace := s.trace + obs)
}

predicate evalUpdateXmmsAndMaintainFlags(s:state, o:operand, v:Quadword, r:state, obs:seq<observation>)
    requires ValidXmmOperand(s, o);
{
    r == s.(xmms := s.xmms[o.r.xmm := v], trace := s.trace + obs)
}

predicate Valid128BitOperand(s:state, o:operand)
{
    match o
        case OConst(c) => IsUInt32(c)
        case OReg(r) => r.X86Xmm? && r.xmm in s.xmms
        case OStack(arg) => Valid128BitStackOperand(s, o)
        case OHeap(addr, taint) => Valid128BitHeapOperand(s, o)
}

predicate Valid128BitSourceOperand(s:state, o:operand)
{
    ValidSourceOperand(s, 128, o)
}

predicate Valid128BitDestinationOperand(s:state, o:operand)
{
    ValidDestinationOperand(s, 128, o)
}

function Eval128BitOperand(s:state, o:operand) : Quadword
    requires Valid128BitOperand(s, o);
{
    match o
        case OConst(c) => Quadword(c, 0, 0, 0)
        case OReg(r) => s.xmms[r.xmm]
        case OStack(slot) => Quadword(eval_op32(s, OStack(slot)) ,
                                 eval_op32(s, OStack(slot+1)),
                                 eval_op32(s, OStack(slot+2)),
                                 eval_op32(s, OStack(slot+3)))
       case OHeap(addr, taint)  => var m0 := EvalMemAddr(s.regs, addr); Quadword(GetValueAtResolvedAddress(s.heap, m0), 
                                                                     GetValueAtResolvedAddress(s.heap, m0+4),
                                                                     GetValueAtResolvedAddress(s.heap, m0+8), 
                                                                     GetValueAtResolvedAddress(s.heap, m0+12))
}

function UpdateHeap128(h:heap, resolved_addr:int, v:Quadword, t:taint) : heap
{
    UpdateHeap32(
    UpdateHeap32(
    UpdateHeap32(
    UpdateHeap32(h, 
        resolved_addr,      v.lo, t),
        resolved_addr +  4, v.mid_lo, t),
        resolved_addr +  8, v.mid_hi, t),
        resolved_addr + 12, v.hi, t)

}

predicate evalUpdate128AndHavocFlags(s:state, o:operand, v:Quadword, r:state, obs:seq<observation>)
    requires Valid128BitDestinationOperand(s, o);
{
    match o
        case OReg(reg)    => r == s.(xmms := s.xmms[reg.xmm := v], flags := r.flags, trace := s.trace + obs)
        case OStack(slot) => r == s.(stack := s.stack[0 := s.stack[0][slot := v.lo][slot+1 := v.mid_lo][slot+2 := v.mid_hi][slot+3 := v.hi]],
                                     flags := r.flags,
                                     trace := s.trace + obs)
        case OHeap(addr, taint)  => var m0 := EvalMemAddr(s.regs, addr);
                             r == s.(heap := UpdateHeap128(s.heap, m0, v, taint),
                                     flags := r.flags,
                                     trace := s.trace + obs)
}

function evalCmp(c:ocmp, i1:uint64, i2:uint64):bool
{
    match c
        case OEq => i1 == i2
        case ONe => i1 != i2
        case OLe => i1 <= i2
        case OGe => i1 >= i2
        case OLt => i1 <  i2
        case OGt => i1 >  i2
}

function evalOBool(s:state, o:obool):bool
    requires ValidSourceOperand(s, 64, o.o1);
    requires ValidSourceOperand(s, 64, o.o2);
{
    evalCmp(o.cmp, eval_op64(s, o.o1), eval_op64(s, o.o2))
}

function clear_low_byte(n:uint32) : uint32
{
    (n / 256) * 256
}

function bswap32(x:uint32) : uint32 { 
   var bytes := WordToBytes(x);
    BytesToWord(bytes[3], bytes[2], bytes[1], bytes[0])
}

function bswap64(x:uint64) : uint64 { 
    var bytes := DoubleWordToBytes(x);
    BytesToDoubleWord(bytes[7], bytes[6], bytes[5], bytes[4], bytes[3], bytes[2], bytes[1], bytes[0])
}

function xor32(x:uint32, y:uint32) : uint32  { BitwiseXor(x, y) }

function xor64(x:uint64, y:uint64) : uint64  { BitwiseXor64(x, y) }

function and32(x:uint32, y:uint32) : uint32  { BitwiseAnd(x, y) }

function not32(x:uint32) : uint32 { BitwiseNot(x) }

function rol32(x:uint32, amount:uint32) : uint32 
    requires 0 <= amount < 32;
    { RotateLeft(x, amount) }

function ror32(x:uint32, amount:uint32) : uint32 
    requires 0 <= amount < 32;
    { RotateRight(x, amount) }

function shl32(x:uint32, amount:uint32) : uint32 
    requires 0 <= amount < 32;
    { LeftShift(x, amount) }

function shr32(x:uint32, amount:uint32) : uint32 
    requires 0 <= amount < 32;
    { RightShift(x, amount) }

// Is the carry flag (CF) set?
predicate{:axiom} Cf(flags:uint32)
// Is the Error Division (ED) flat set.
predicate{:axiom} Ed(flags:uint32)

// Is the stack not valid to pop.
predicate{:axiom} SS(flags:uint32)

predicate ValidInstruction(s:state, ins:ins)
{
    match ins
        case Rand(xRand) => Valid32BitDestinationOperand(s, xRand)
        case Mov32(dstMov, srcMov) => Valid32BitDestinationOperand(s, dstMov) && Valid32BitSourceOperand(s, srcMov)
        case Mov64(dstMov, srcMov) => Valid64BitDestinationOperand(s, dstMov) && Valid64BitSourceOperand(s, srcMov)
        case MOVQ64XMM(dst, src) => Valid64BitDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case MOVQXMM64(dst, src) => ValidXmmDestinationOperand(s, dst) && Valid64BitSourceOperand(s, src)
        case MOVHLPS(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case MOVLHPS(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)

        case Add32(dstAdd, srcAdd) => Valid32BitDestinationOperand(s, dstAdd) && Valid32BitSourceOperand(s, srcAdd) && Valid32BitSourceOperand(s, dstAdd)
        case Add64(dstAdd, srcAdd) => Valid64BitDestinationOperand(s, dstAdd) && Valid64BitSourceOperand(s, srcAdd) && Valid64BitSourceOperand(s, dstAdd)
        case AddLea64(dstAdd, srcAdd1, srcAdd2) => Valid64BitDestinationOperand(s, dstAdd) && Valid64BitSourceOperand(s, srcAdd1) && Valid64BitSourceOperand(s, srcAdd2) && Valid64BitSourceOperand(s, dstAdd)
        case Sub32(dstSub, srcSub) => Valid32BitDestinationOperand(s, dstSub) && Valid32BitSourceOperand(s, srcSub) && Valid32BitSourceOperand(s, dstSub)
        case Sub64(dstSub, srcSub) => Valid64BitDestinationOperand(s, dstSub) && Valid64BitSourceOperand(s, srcSub) && Valid64BitSourceOperand(s, dstSub)
        case Mul32(srcMul) => Valid32BitSourceOperand(s, srcMul) && Valid32BitSourceOperand(s, OReg(X86Eax)) && Valid32BitDestinationOperand(s, OReg(X86Eax)) && Valid32BitDestinationOperand(s, OReg(X86Edx))
        case Mul64(srcMul) => Valid64BitSourceOperand(s, srcMul) && Valid64BitSourceOperand(s, OReg(X86Eax)) && Valid64BitDestinationOperand(s, OReg(X86Eax)) && Valid64BitDestinationOperand(s, OReg(X86Edx))

        case Div64(srcMul) => srcMul.OReg? /*&& eval_op64(s,srcMul) != 0*/ && Valid64BitSourceOperand(s, srcMul) && Valid64BitDestinationOperand(s, OReg(X86Edx)) && Valid64BitDestinationOperand(s, OReg(X86Eax)) &&
                             Valid64BitSourceOperand(s, OReg(X86Edx)) && Valid64BitSourceOperand(s, OReg(X86Eax))

        case IMul64(dst, src) => Valid64BitDestinationOperand(s, dst) && Valid64BitSourceOperand(s, src) && Valid64BitSourceOperand(s, dst)
        case AddCarry(dstAddCarry, srcAddCarry) => Valid32BitDestinationOperand(s, dstAddCarry) && Valid32BitSourceOperand(s, srcAddCarry) && Valid32BitSourceOperand(s, dstAddCarry)
        case AddCarry64(dstAddCarry, srcAddCarry) => Valid64BitDestinationOperand(s, dstAddCarry) && Valid64BitSourceOperand(s, srcAddCarry) && Valid64BitSourceOperand(s, dstAddCarry)
        case BSwap32(dstBSwap) => Valid32BitDestinationOperand(s, dstBSwap) && dstBSwap.OReg?
        case BSwap64(dst64BSwap) => Valid64BitDestinationOperand(s, dst64BSwap) && dst64BSwap.OReg?
        case Xor32(dstXor, srcXor) => Valid32BitDestinationOperand(s, dstXor) && Valid32BitSourceOperand(s, srcXor) && Valid32BitSourceOperand(s, dstXor)
        case Xor64(dstXor, srcXor) => Valid64BitDestinationOperand(s, dstXor) && Valid64BitSourceOperand(s, srcXor) && Valid64BitSourceOperand(s, dstXor)
        case And32(dstAnd, srcAnd) => Valid32BitDestinationOperand(s, dstAnd) && Valid32BitSourceOperand(s, srcAnd) && Valid32BitSourceOperand(s, dstAnd)
        case And64(dstAnd, srcAnd) => Valid64BitDestinationOperand(s, dstAnd) && Valid64BitSourceOperand(s, srcAnd) && Valid64BitSourceOperand(s, dstAnd)
        case Not32(dstNot) => Valid32BitDestinationOperand(s, dstNot) && Valid32BitSourceOperand(s, dstNot)
        case GetCf(dstCf) => Valid32BitDestinationOperand(s, dstCf) && Valid32BitSourceOperand(s, dstCf)
        case Rol32(dstRolConst, amountRol) => Valid32BitDestinationOperand(s, dstRolConst) && ValidShiftAmountOperand(s, amountRol) && Valid32BitSourceOperand(s, dstRolConst)
        case Ror32(dstRorConst, amountRor) => Valid32BitDestinationOperand(s, dstRorConst) && ValidShiftAmountOperand(s, amountRor) && Valid32BitSourceOperand(s, dstRorConst)
        case Shl32(dstShlConst, amountShl) => Valid32BitDestinationOperand(s, dstShlConst) && ValidShiftAmountOperand(s, amountShl) && Valid32BitSourceOperand(s, dstShlConst)
        case Shl64(dstShrConst, amountShr) => Valid64BitDestinationOperand(s, dstShrConst) && ValidShiftAmountOperand64(s, amountShr) && Valid64BitSourceOperand(s, dstShrConst)
        case Shr32(dstShrConst, amountShr) => Valid32BitDestinationOperand(s, dstShrConst) && ValidShiftAmountOperand(s, amountShr) && Valid32BitSourceOperand(s, dstShrConst)
        case Shr64(dstShrConst, amountShr) => Valid64BitDestinationOperand(s, dstShrConst) && ValidShiftAmountOperand64(s, amountShr) && Valid64BitSourceOperand(s, dstShrConst)
        case AESNI_enc(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case AESNI_enc_last(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case AESNI_dec(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case AESNI_dec_last(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case AESNI_imc(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case AESNI_keygen_assist(dst, src, imm8) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src) && ValidImm8(s, imm8)
        case Pxor(dst, src) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case Pshufd(dst, src, permutation) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src) && ValidImm8(s, permutation)
        case VPSLLDQ(dst, src, count) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src) && ValidImm8(s, count) && eval_op32(s, count) == 4
        case MOVDQU(dst, src) => Valid128BitDestinationOperand(s, dst) && Valid128BitSourceOperand(s, src) && !src.OConst? && (IsXmmOperand(dst) || IsXmmOperand(src))
        case MOVD_xmm_rmm32(dst, src) => Valid128BitDestinationOperand(s, dst) && Valid32BitSourceOperand(s, src) && !src.OConst? && IsXmmOperand(dst)
        case PCLMULQDQ(dst, src, imm8) => Valid128BitDestinationOperand(s, dst) && Valid128BitSourceOperand(s, src) && !src.OConst? && (IsXmmOperand(dst) || IsXmmOperand(src)) && ValidImm8(s, imm8)
        case VPCLMULQDQ(dst, src1, src2, imm8) => Valid128BitDestinationOperand(s, dst) && Valid128BitSourceOperand(s, src1) && Valid128BitSourceOperand(s, src2) && 
          IsXmmOperand(dst) && IsXmmOperand(src1) && ValidImm8(s, imm8)
        case VMOVDQA(dst, src) => Valid128BitDestinationOperand(s, dst) && Valid128BitSourceOperand(s, src) && !src.OConst? && IsXmmOperand(dst)
        case VPSHUFD(dst, src, imm8) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src) && ValidImm8(s, imm8)
        case VPXOR(dst, src1, src2) => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src1) && ValidXmmSourceOperand(s, src2)
        case MOVDQA(dst, src)  => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)
        case POR(dst, src)     => ValidXmmDestinationOperand(s, dst) && ValidXmmSourceOperand(s, src)

        case PSLLD(dst, imm8)  => Valid64BitDestinationOperand(s, dst) && ValidImm8(s, imm8) && eval_op32(s,imm8) <= 64
        case PSLLDQ(dst, imm8) => ValidXmmDestinationOperand(s, dst) && ValidImm8(s, imm8) && eval_op32(s,imm8) <= 16

        case PSRLD(dst, imm8)  => Valid64BitDestinationOperand(s, dst) && ValidImm8(s, imm8) && eval_op32(s,imm8) <= 64
        case PSRLDQ(dst, imm8) => ValidXmmDestinationOperand(s, dst) && ValidImm8(s, imm8) && eval_op32(s,imm8) <= 16
        case PUSH(src)         => Valid64BitSourceOperand(s, src) && src.OReg?
        case POP(dst)          => Valid64BitDestinationOperand(s, dst) && dst.OReg? && |s.stack| > 1 && 0 in s.stack[0] && 1 in s.stack[0]
        case MOV_m64_imm32(dst, src) => Valid64BitDestinationOperand(s, dst) && Valid32BitSourceOperand(s, src)
}

lemma {:axiom} lemma_division_in_bounds(a:uint32, b:uint32)
    ensures 0 <= (a * b) / 0x1_0000_0000 < 0x1_0000_0000;

lemma {:axiom} lemma_division_in_bounds64(a:uint64, b:uint64)
    ensures 0 <= (a * b) / 0x1_0000_0000_0000_0000 < 0x1_0000_0000_0000_0000;

function operandObs(s:state, size:int, o:operand) : seq<observation>
    requires ValidOperand(s, size, o)
{
    match o
        case OConst(_) => []
        case OReg(_) => []
        case OStack(_) => [] // No need for StackSlotAccess because slot is deterministic based on code
        case OHeap(addr, _) =>
            match addr
                case MConst(n) => []
                case MReg(reg, _) => [ HeapAccess(eval_reg(s.regs, reg)) ]
                case MIndex(base, _, index, _) => [ HeapAccessOffset(eval_reg(s.regs, base), eval_reg(s.regs, index)) ]
}

function insObs(s:state, ins:ins):seq<observation>
    requires ValidInstruction(s, ins)
{
    match ins
        case Rand(x) => operandObs(s, 32, x)
        case Mov32(dst, src) => operandObs(s, 32, dst) + operandObs(s, 32, src)
        case Mov64(dst, src) => operandObs(s, 64, dst) + operandObs(s, 64, src)
        // Bryan pls check. 
        case MOVQ64XMM(dst, src)  => operandObs(s, 64, dst) + operandObs(s, 128, src)
        case MOVQXMM64(dst, src)  => operandObs(s, 128, dst) + operandObs(s, 64, src)

        case MOVHLPS(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case MOVLHPS(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case Add32(dst, src) => operandObs(s, 32, dst) + operandObs(s, 32, src)
        case Add64(dst, src) => operandObs(s, 64, dst) + operandObs(s, 64, src)
        case AddLea64(dst, src1, src2) => operandObs(s, 64, dst) + operandObs(s, 64, src1) + operandObs(s, 64, src2)
        case Sub32(dst, src) => operandObs(s, 32, dst) + operandObs(s, 32, src)
        case Sub64(dst, src) => operandObs(s, 64, dst) + operandObs(s, 64, src)
        case Mul32(src) => operandObs(s, 32, src) // TODO: eax, edx
        case Mul64(src) => operandObs(s, 64, src)
        case Div64(src) => operandObs(s, 64, src)  +  operandObs(s, 64, OReg(X86Eax))  + operandObs(s, 64, OReg(X86Edx))
        case IMul64(dst, src) => operandObs(s, 64, dst) + operandObs(s, 64, src)
        case AddCarry(dst, src) => operandObs(s, 32, dst) + operandObs(s, 32, src)
        case AddCarry64(dst, src) => operandObs(s, 64, dst) + operandObs(s, 64, src)
        case BSwap32(dst) => operandObs(s, 32, dst)
        case BSwap64(dst) => operandObs(s, 64, dst)
        case Xor32(dst, src) => operandObs(s, 32, dst) + operandObs(s, 32, src)
        case Xor64(dst, src) => operandObs(s, 64, dst) + operandObs(s, 64, src)
        case And32(dst, src) => operandObs(s, 32, dst) + operandObs(s, 32, src)
        case And64(dst, src) => operandObs(s, 64, dst) + operandObs(s, 64, src)
        case Not32(dst) => operandObs(s, 32, dst)
        case GetCf(dst) => operandObs(s, 32, dst)
        case Rol32(dst, amount) => operandObs(s, 32, dst) + operandObs(s, 32, amount)
        case Ror32(dst, amount) => operandObs(s, 32, dst) + operandObs(s, 32, amount)
        case Shl32(dst, amount) => operandObs(s, 32, dst) + operandObs(s, 32, amount)
        case Shl64(dst, amount) => operandObs(s, 64, dst) + operandObs(s, 64, amount)
        case Shr32(dst, amount) => operandObs(s, 32, dst) + operandObs(s, 32, amount)
        case Shr64(dst, amount) => operandObs(s, 64, dst) + operandObs(s, 64, amount)
        case AESNI_enc(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case AESNI_enc_last(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case AESNI_dec(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case AESNI_dec_last(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case AESNI_imc(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case AESNI_keygen_assist(dst, src, imm8) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case Pxor(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case Pshufd(dst, src, permutation) => operandObs(s, 128, dst) +  operandObs(s, 128, src)
        case VPSLLDQ(dst, src, count) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case MOVDQU(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case MOVD_xmm_rmm32(dst, src) => operandObs(s, 128, dst) + operandObs(s, 32, src)
        case PCLMULQDQ(dst, src, imm8) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case VPCLMULQDQ(dst, src1, src2, imm8) => operandObs(s, 128, dst) + operandObs(s, 128, src1) + operandObs(s, 128, src2)
        case VMOVDQA(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case VPSHUFD(dst, src, imm8) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case VPXOR(dst, src1, src2) => operandObs(s, 128, dst) + operandObs(s, 128, src1) + operandObs(s, 128, src2)
        case MOVDQA(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case POR(dst, src) => operandObs(s, 128, dst) + operandObs(s, 128, src)
        case PSLLD (dst, imm8) => operandObs(s, 64, dst)
        case PSLLDQ(dst, imm8) => operandObs(s, 128, dst)
        case PSRLD (dst, imm8) => operandObs(s, 64, dst)
        case PSRLDQ(dst, imm8) => operandObs(s, 128, dst)
        case PUSH(src)         => operandObs(s, 64, src)
        case POP (dst)         => operandObs(s, 64, dst)
        case MOV_m64_imm32(dst, src) => operandObs(s, 64, dst) + operandObs(s, 32, dst)
}

predicate evalIns(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then
        !r.ok
    else
        var obs := insObs(s, ins);
        match ins
            case Rand(x) => exists n:uint32 :: evalUpdateAndHavocFlags(s, x, n, r, obs)
            case Mov32(dst, src) => evalUpdateAndMaintainFlags(s, dst, eval_op32(s, src), r, obs) // mov doesn't change flags
            case Mov64(dst, src) => evalUpdateAndMaintainFlags64(s, dst, eval_op64(s, src), r, obs) // mov doesn't change flags

          case MOVQ64XMM(dst, src) =>
            var t := eval_op128(s,src);
              evalUpdateAndMaintainFlags64(s, dst, lowerUpper64(t.lo, t.mid_lo), r, obs) // mov doesn't change flags

          case MOVQXMM64(dst, src) =>
            var d := eval_op128(s,dst);
            var t := eval_op64(s,src);
              evalUpdateXmmsAndMaintainFlags(s, dst, Quadword(lower64(t), upper64(t), 0, 0), r, obs) // mov doesn't change flags

          case MOVHLPS(dst, src) =>
            var d := eval_op128(s,dst);
            var t := eval_op128(s,src);
              evalUpdateXmmsAndMaintainFlags(s, dst, Quadword(t.mid_hi, t.hi, d.mid_hi, d.hi), r, obs)

          case MOVLHPS(dst, src) =>
            var d := eval_op128(s,dst);
            var t := eval_op128(s,src);
              evalUpdateXmmsAndMaintainFlags(s, dst, Quadword(d.lo, d.mid_lo, t.lo, t.mid_lo), r, obs)

            case Add32(dst, src) => evalUpdateAndHavocFlags(s, dst, (eval_op32(s, dst) + eval_op32(s, src)) % 0x1_0000_0000, r, obs)
            case Add64(dst, src) => var sum := eval_op64(s, dst) + eval_op64(s, src);
                                    evalUpdateAndHavocFlags64(s, dst, sum % 0x1_0000_0000_0000_0000, r, obs)
                                    && Cf(r.flags) == (sum >= 0x1_0000_0000_0000_0000)
            case AddLea64(dst, src1, src2) => evalUpdateAndMaintainFlags64(s, dst, (eval_op64(s, src1) + eval_op64(s, src2)) % 0x1_0000_0000_0000_0000, r, obs)
            case Sub32(dst, src) => evalUpdateAndHavocFlags(s, dst, (eval_op32(s, dst) - eval_op32(s, src)) % 0x1_0000_0000, r, obs)
            case Sub64(dst, src) => evalUpdateAndHavocFlags64(s, dst, (eval_op64(s, dst) - eval_op64(s, src)) % 0x1_0000_0000_0000_0000, r, obs)
            case Mul32(src)      => var product := s.regs[X86Eax] * eval_op32(s, src);
                                    lemma_division_in_bounds(s.regs[X86Eax], eval_op32(s, src));  // Annoying
                                    var hi := (product / 0x1_0000_0000);
                                    var lo := (product % 0x1_0000_0000);
                                    r == s.(regs := s.regs[X86Edx := hi][X86Eax := lo], flags := r.flags)
            case Mul64(src)      => var product := s.regs[X86Eax] * eval_op64(s, src);
                                    lemma_division_in_bounds64(s.regs[X86Eax], eval_op64(s, src));  // Annoying
                                    var hi := (product / 0x1_0000_0000_0000_0000);
                                    var lo := (product % 0x1_0000_0000_0000_0000);
                                    r == s.(regs := s.regs[X86Edx := hi][X86Eax := lo], flags := r.flags)

            // Div64 is three registers. Divides rdx:rax / src and puts the quotient in rax and the remainder in rdx.
            // Intel 3-286 Vol. 2A, says DE gets turned on in EFL. Register state is unspecified.
            // We are avoiding division by zero in the instruction instead of setting conditions.
            case Div64(src) => var div := BitwiseDiv128by64(s.regs[X86Edx], s.regs[X86Eax], eval_op64(s, src)); // Will return 0 on 0 src.
                              var mod := BitwiseMod128by64(s.regs[X86Edx], s.regs[X86Eax], eval_op64(s, src)); // Will return 0 on 0 src.
                              evalUpdateAndMaintainFlagsDiv(s, src, div, mod, r, obs) &&
                              Ed(r.flags) == (eval_op64(s, src) != 0)

            case IMul64(dst, src) => evalUpdateAndHavocFlags64(s, dst, (eval_op64(s, dst) * eval_op64(s, src)) % 0x1_0000_0000_0000_0000, r, obs)
            // Add with carry (ADC) instruction
            case AddCarry(dst, src) => var old_carry := if Cf(s.flags) then 1 else 0;
                                       var sum := eval_op32(s, dst) + eval_op32(s, src) + old_carry;
                                       evalUpdateAndHavocFlags(s, dst, sum % 0x1_0000_0000, r, obs)
                                    && Cf(r.flags) == (sum >= 0x1_0000_0000)
            case AddCarry64(dst, src) => var old_carry := if Cf(s.flags) then 1 else 0;
                                       var sum := eval_op64(s, dst) + eval_op64(s, src) + old_carry;
                                       evalUpdateAndHavocFlags64(s, dst, sum % 0x1_0000_0000_0000_0000, r, obs)
                                    && Cf(r.flags) == (sum >= 0x1_0000_0000_0000_0000)
            case BSwap32(dst)    => evalUpdateAndMaintainFlags(s, dst, bswap32(eval_op32(s, dst)), r, obs)
            case BSwap64(dst)    => evalUpdateAndMaintainFlags64(s, dst, bswap64(eval_op64(s, dst)), r, obs)
            case Xor32(dst, src) => evalUpdateAndHavocFlags(s, dst, xor32(eval_op32(s, dst), eval_op32(s, src)), r, obs)
            case Xor64(dst, src) => evalUpdateAndHavocFlags64(s, dst, xor64(eval_op64(s, dst), eval_op64(s, src)), r, obs)
            case And32(dst, src) => evalUpdateAndHavocFlags(s, dst, and32(eval_op32(s, dst), eval_op32(s, src)), r, obs)
            case And64(dst, src) => evalUpdateAndHavocFlags64(s, dst, BitwiseAnd64(eval_op64(s, dst), eval_op64(s, src)), r, obs)
            case Not32(dst)      => evalUpdateAndHavocFlags(s, dst, not32(eval_op32(s, dst)), r, obs)
            // Sticks the carry flag (CF) in a register (see SETC instruction
            case GetCf(dst)      => // Instruction only writes the first uint8
                                    evalUpdateAndMaintainFlags(s, dst, clear_low_byte(eval_op32(s, dst)) + if Cf(s.flags) then 1 else 0, r, obs)
            case Rol32(dst, amount)  =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, rol32(eval_op32(s, dst), n), r, obs) else !r.ok

            case Ror32(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, ror32(eval_op32(s, dst), n), r, obs) else !r.ok

            case Shl32(dst, amount)  =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, shl32(eval_op32(s, dst), n), r, obs) else !r.ok
            case Shl64(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 64 then evalUpdateAndHavocFlags64(s, dst, BitwiseShl64(eval_op64(s, dst), n), r, obs) else !r.ok

            case Shr32(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, shr32(eval_op32(s, dst), n), r, obs) else !r.ok
            case Shr64(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.regs[X86Ecx];
                if 0 <= n < 64 then evalUpdateAndHavocFlags64(s, dst, BitwiseShr64(eval_op64(s, dst), n), r, obs) else !r.ok
            case AESNI_enc(dst, src) => evalUpdateXmmsAndHavocFlags(s, dst, QuadwordXor(MixColumns(SubBytes(ShiftRows(s.xmms[dst.r.xmm]))), s.xmms[src.r.xmm]), r, obs)
            case AESNI_enc_last(dst, src) => evalUpdateXmmsAndHavocFlags(s, dst, QuadwordXor(SubBytes(ShiftRows(s.xmms[dst.r.xmm])), s.xmms[src.r.xmm]), r, obs)
            case AESNI_dec(dst, src) => evalUpdateXmmsAndHavocFlags(s, dst, QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(s.xmms[dst.r.xmm]))), s.xmms[src.r.xmm]), r, obs)
            case AESNI_dec_last(dst, src) => evalUpdateXmmsAndHavocFlags(s, dst, QuadwordXor(InvSubBytes(InvShiftRows(s.xmms[dst.r.xmm])), s.xmms[src.r.xmm]), r, obs)
            case AESNI_imc(dst, src) => evalUpdateXmmsAndHavocFlags(s, dst, InvMixColumns(s.xmms[src.r.xmm]), r, obs)
            case AESNI_keygen_assist(dst, src, imm8) => evalUpdateXmmsAndHavocFlags(s, dst, Quadword(
                                                                                                SubWord(s.xmms[src.r.xmm].mid_lo), 
                                                                                                BitwiseXor(RotWord(SubWord(s.xmms[src.r.xmm].mid_lo)), eval_op32(s, imm8)),
                                                                                                SubWord(s.xmms[src.r.xmm].hi),
                                                                                                BitwiseXor(RotWord(SubWord(s.xmms[src.r.xmm].hi)), eval_op32(s, imm8))
                                                                                                ), r, obs)
            //BUG, Intel says no flag changed.
            case Pxor(dst, src) => evalUpdateXmmsAndHavocFlags(s, dst, QuadwordXor(s.xmms[dst.r.xmm], s.xmms[src.r.xmm]), r, obs)
            case Pshufd(dst, src, permutation) => evalUpdateXmmsAndHavocFlags(s, dst, Quadword(
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).lo),
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).mid_lo),
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).mid_hi),
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).hi)
                                                                             ), r, obs)
            case VPSLLDQ(dst, src, count)  => evalUpdateXmmsAndHavocFlags(s, dst, Quadword(0, s.xmms[src.r.xmm].lo, s.xmms[src.r.xmm].mid_lo, s.xmms[src.r.xmm].mid_hi), r, obs)
            case MOVDQU(dst, src)          => evalUpdate128AndHavocFlags(s, dst, Eval128BitOperand(s, src), r, obs)
// AES-GCM instructions
            case MOVD_xmm_rmm32(dst, src)    => evalUpdate128AndHavocFlags(s, dst, Quadword(eval_op32(s, src), 0,0,0), r, obs)
            case POR(dst, src)                     => evalUpdateXmmsAndHavocFlags(s, dst, QuadwordOr(s.xmms[dst.r.xmm], s.xmms[src.r.xmm]), r, obs)
            case MOVDQA(dst, src)                  => evalUpdateXmmsAndMaintainFlags(s, dst, Eval128BitOperand(s, src), r, obs)
            case VMOVDQA(dst, src)                 => evalUpdateXmmsAndMaintainFlags(s, dst, Eval128BitOperand(s, src), r, obs)
            case VPSHUFD(dst, src, permutation)    => evalUpdateXmmsAndHavocFlags(s, dst, Quadword(
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).lo),
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).mid_lo),
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).mid_hi),
                                                                             select_word(s.xmms[src.r.xmm], byte_to_bits(eval_op32(s,permutation)).hi)
                                                                             ), r, obs)
            case VPXOR(dst, src1, src2)            => evalUpdateXmmsAndMaintainFlags(s, dst, QuadwordXor(Eval128BitOperand(s, src1), Eval128BitOperand(s, src2)), r, obs)
            case PSLLD(dst, count)                 => evalUpdateAndMaintainFlags64(s, dst, BitwiseShl64(eval_op64(s, dst), eval_op32(s,count)), r, obs)
            case PSLLDQ(dst, count)                => evalUpdateXmmsAndMaintainFlags(s, dst, 
                                                        Uint128ToQuadword(BitwiseShl128(QuadwordToUint128(Eval128BitOperand(s,dst)), 8 * eval_op32(s,count))), r, obs)

            case PSRLD(dst, count)                 => evalUpdateAndMaintainFlags64(s, dst, BitwiseShr64(eval_op64(s, dst), eval_op32(s,count)), r, obs)
            case PSRLDQ(dst, count)                => evalUpdateXmmsAndMaintainFlags(s, dst,
                                                        Uint128ToQuadword(BitwiseShr128(QuadwordToUint128(Eval128BitOperand(s,dst)), 8 * eval_op32(s,count))), r, obs)
            case PCLMULQDQ(dst, src, imm8)         => evalUpdate128AndHavocFlags(s, dst, Eval128BitOperand(s, src), r, obs)
            case VPCLMULQDQ(dst, src1, src2, imm8) => evalUpdate128AndHavocFlags(s, dst, Eval128BitOperand(s, src1), r, obs)
            case PUSH(src) => evalPush(s, src, eval_op64(s, src), r, obs)
            case POP(dst)  => evalPop(s, dst, r, obs)
            case MOV_m64_imm32(dst, src) => evalUpdateAndMaintainFlags64(s, dst, eval_op32(s, src), r, obs)
}

predicate evalBlock(block:codes, s:state, r:state)
{
    if block.CNil? then
        r == s
    else
        exists r':state :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

function {:axiom} updateFlagsUsingCondition(flags:uint32, cond:bool) : uint32

predicate branchRelation(s:state, s':state, cond:bool)
{
    // TODO: Make zero flag depend on evalOBool(s, cond)
    s' == s.(trace := s.trace + [BranchPredicate(cond)], flags := updateFlagsUsingCondition(s.flags, cond))
}

predicate evalIfElse(cond:obool, ifT:code, ifF:code, s:state, r:state)
    decreases if ValidSourceOperand(s, 64, cond.o1) && ValidSourceOperand(s, 64, cond.o2) && evalOBool(s, cond) then ifT else ifF;
{
    if s.ok && ValidSourceOperand(s, 64, cond.o1) && ValidSourceOperand(s, 64, cond.o2) then
        exists s' ::
           branchRelation(s, s', evalOBool(s, cond))
        && (if evalOBool(s, cond) then evalCode(ifT, s', r) else evalCode(ifF, s', r))
    else
        !r.ok
}

predicate evalWhile(b:obool, c:code, n:nat, s:state, r:state)
  decreases c, n
{
    if s.ok && ValidSourceOperand(s, 64, b.o1) && ValidSourceOperand(s, 64, b.o2) then
        if n == 0 then
            !evalOBool(s, b) && branchRelation(s, r, false)
        else
            exists loop_start:state, loop_end:state ::    evalOBool(s, b)
                                                 && branchRelation(s, loop_start, true)
                                                 && evalCode(c, loop_start, loop_end)
                                                 && evalWhile(b, c, n - 1, loop_end, r)
    else
        !r.ok
}

// evaluation (zero or more steps) may succeed and change s to r where r.ok == true
// evaluation (zero or more steps) may fail where r.ok == false
predicate evalCode(c:code, s:state, r:state)
  decreases c, 0
{
    match c
        case Ins(ins) => evalIns(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => exists n:nat :: evalWhile(cond, body, n, s, r)
}

}
