/*

  This demonstrates x64 callee save using push and pop of r64 registers.
  Brian Milnes 31 Aug 2017

*/

/* 
  Vale seems to be using the following calling conventions:

  https://en.wikipedia.org/wiki/X86_calling_conventions#List_of_x86_calling_conventions

  Arch  OS       Convention                            Arguments                                 Caller saved
  x86
     Linux      cdecl                                 arguments on the stack                  EAX, ECX, and EDX
     Windows    cdecl?stdcall                         arguments on the stack                        ?
  x64 
     Linux      System V AMD64 ABI                    RDI, RSI, RDX, RCX, R8, R9, XMM0–7            ?
     Windows    Microsoft x64 calling convention      RCX/XMM0, RDX/XMM1, R8/XMM2, R9/XMM3          ?
 
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> // for uint?_t
#include "gcc_compat.h"
#include <inttypes.h>

void __stdcall TestCalleeSaveRestoreLinux();

int before_rbp = 0;
int before_rbx = 0;
int before_r12 = 0;
int before_r13 = 0;
int before_r14 = 0;
int before_r15 = 0;

int after_rbp = -1;
int after_rbx = -1;
int after_r12 = -1;
int after_r13 = -1;
int after_r14 = -1;
int after_r15 = -1;

int test_callee_save_linux() {
  register int register_rbp asm ("rbp"); before_rbp = register_rbp;
  register int register_rbx asm ("rbx"); before_rbx = register_rbx;
  register int register_r12 asm ("r12"); before_r12 = register_r12;
  register int register_r13 asm ("r13"); before_r13 = register_r13;
  register int register_r14 asm ("r14"); before_r14 = register_r14;
  register int register_r15 asm ("r15"); before_r15 = register_r15;

  TestCalleeSaveRestoreLinux();

  after_rbp = register_rbp;
  after_rbx = register_rbx;
  after_r12 = register_r12;
  after_r13 = register_r13;
  after_r14 = register_r14;
  after_r15 = register_r15;

  if (before_rbx == after_rbx) { printf("rbx OK\n"); } else {printf("FAILURE rbx was %d is now %d.\n", before_rbx, after_rbx); return 1;}
  if (before_rbp == after_rbp) { printf("rbp OK\n"); } else {printf("FAILURE rbp was %d is now %d.\n", before_rbp, after_rbp); return 1;}
  if (before_r12 == after_r12) { printf("r12 OK\n"); } else {printf("FAILURE r12 was %d is now %d.\n", before_r12, after_r12); return 1;}
  if (before_r13 == after_r13) { printf("r13 OK\n"); } else {printf("FAILURE r13 was %d is now %d.\n", before_r13, after_r13); return 1;}
  if (before_r14 == after_r14) { printf("r14 OK\n"); } else {printf("FAILURE r14 was %d is now %d.\n", before_r14, after_r14); return 1;}
  if (before_r15 == after_r15) { printf("r15 OK\n"); } else {printf("FAILURE r15 was %d is now %d.\n", before_r15, after_r15); return 1;}

  return 0;
}

/*
void __stdcall TestCalleeSaveRestoreWindowsMM();

int test_callee_save_windowsMM() {

  register int old_rbx asm ("rbx");
  register int old_rbp asm ("rbp");
  register int old_rdi asm ("rdi");
  register int old_rsi asm ("rsi");
  register int old_r10 asm ("r10");
  register int old_r11 asm ("r11");
  register int old_r12 asm ("r12");
  register int old_r14 asm ("r14");
  register int old_r15 asm ("r15");
  TestCalleeSaveRestoreWindowsMM();
  register int rbx asm ("rbx");
  register int rbp asm ("rbp");
  register int rdi asm ("rdi");
  register int rsi asm ("rsi");
  register int r10 asm ("r10");
  register int r11 asm ("r11");
  register int r12 asm ("r12");
  register int r14 asm ("r14");
  register int r15 asm ("r15");

  if (old_rbx == rbx) { printf("rbx OK\n"); } else {printf("FAILURE rbx was %d is now %d.\n", old_rbx, rbx); return 1;}
  if (old_rbp == rbp) { printf("rbp OK\n"); } else {printf("FAILURE rbp was %d is now %d.\n", old_rbp, rbp); return 1;}
  if (old_rdi == rdi) { printf("rdi OK\n"); } else {printf("FAILURE rdi was %d is now %d.\n", old_rdi, rdi); return 1;}
  if (old_rsi == rsi) { printf("rsi OK\n"); } else {printf("FAILURE rsi was %d is now %d.\n", old_rsi, rsi); return 1;}
  if (old_r10 == r10) { printf("r10 OK\n"); } else {printf("FAILURE r10 was %d is now %d.\n", old_r10, r10); return 1;}
  if (old_r11 == r11) { printf("r11 OK\n"); } else {printf("FAILURE r11 was %d is now %d.\n", old_r11, r11); return 1;}
  if (old_r12 == r12) { printf("r12 OK\n"); } else {printf("FAILURE r12 was %d is now %d.\n", old_r12, r12); return 1;}
  if (old_r14 == r14) { printf("r14 OK\n"); } else {printf("FAILURE r14 was %d is now %d.\n", old_r14, r14); return 1;}
  if (old_r15 == r15) { printf("r15 OK\n"); } else {printf("FAILURE r15 was %d is now %d.\n", old_r15, r15); return 1;}

  return 0;
}

void __stdcall TestCalleeSaveRestoreWindowsXMM();
//xmm6; xmm7; xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;
int test_callee_save_windowsXMM() {
  register long long int old_xmm6 asm ("xmm6"); 
  register long long int old_xmm7 asm ("xmm7"); 
  register long long int old_xmm8 asm ("xmm8"); 
  register long long int old_xmm9 asm ("xmm9"); 
  register long long int old_xmm10 asm ("xmm10"); 
  register long long int old_xmm11 asm ("xmm11"); 
  register long long int old_xmm12 asm ("xmm12"); 
  register long long int old_xmm13 asm ("xmm13"); 
  register long long int old_xmm14 asm ("xmm14"); 
  register long long int old_xmm15 asm ("xmm15");
  TestCalleeSaveRestoreWindowsXMM();
  register long long int xmm6 asm ("xmm6"); 
  register long long int xmm7 asm ("xmm7"); 
  register long long int xmm8 asm ("xmm8"); 
  register long long int xmm9 asm ("xmm9"); 
  register long long int xmm10 asm ("xmm10"); 
  register long long int xmm11 asm ("xmm11"); 
  register long long int xmm12 asm ("xmm12"); 
  register long long int xmm13 asm ("xmm13"); 
  register long long int xmm14 asm ("xmm14"); 
  register long long int xmm15 asm ("xmm15");

  if (old_xmm6 == xmm6) { printf("xmm6 OK\n"); } else {printf("FAILURE xmm6 was %lld is now %lld.\n", old_xmm6, xmm6); return 1;}
  if (old_xmm7 == xmm7) { printf("xmm7 OK\n"); } else {printf("FAILURE xmm7 was %lld is now %lld.\n", old_xmm7, xmm7); return 1;}
  if (old_xmm8 == xmm8) { printf("xmm8 OK\n"); } else {printf("FAILURE xmm8 was %lld is now %lld.\n", old_xmm8, xmm8); return 1;}
  if (old_xmm9 == xmm9) { printf("xmm9 OK\n"); } else {printf("FAILURE xmm9 was %lld is now %lld.\n", old_xmm9, xmm9); return 1;}
  if (old_xmm10 == xmm10) { printf("xmm10 OK\n"); } else {printf("FAILURE xmm10 was %lld is now %lld.\n", old_xmm10, xmm10); return 1;}
  if (old_xmm11 == xmm11) { printf("xmm11 OK\n"); } else {printf("FAILURE xmm11 was %lld is now %lld.\n", old_xmm11, xmm11); return 1;}
  if (old_xmm12 == xmm12) { printf("xmm12 OK\n"); } else {printf("FAILURE xmm12 was %lld is now %lld.\n", old_xmm12, xmm12); return 1;}
  if (old_xmm13 == xmm13) { printf("xmm13 OK\n"); } else {printf("FAILURE xmm13 was %lld is now %lld.\n", old_xmm13, xmm13); return 1;}
  if (old_xmm14 == xmm14) { printf("xmm14 OK\n"); } else {printf("FAILURE xmm14 was %lld is now %lld.\n", old_xmm14, xmm14); return 1;}
  if (old_xmm15 == xmm15) { printf("xmm15 OK\n"); } else {printf("FAILURE xmm15 was %lld is now %lld.\n", old_xmm15, xmm15); return 1;}

  return 0;
}

*/

int __cdecl main(void) {
  printf("Callee Save starting tests.\n");

  if (test_callee_save_linux() == 0) {
    printf("Callee Save all linux tests passed.\n");
  } else {
    printf("Callee Save some linux test failed.\n");
  }

  /*
  if (test_callee_save_windowsMM() == 0) {
    printf("Callee Save all windowsMM tests passed.\n");
  } else {
    printf("Callee Save some windowsMM test failed.\n");
  }

  if (test_callee_save_windowsXMM() == 0) {
    printf("Callee Save all windowsXMM tests passed.\n");
  } else {
    printf("Callee Save some windowsXMM test failed.\n");
  }
 */

  printf("Callee Save finished tests.\n");
}



