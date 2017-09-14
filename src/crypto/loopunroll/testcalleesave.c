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

void __stdcall CalleeSaveRestoreLinux();

int test_callee_save_linux() {
  register int old_rbx asm ("rbx");
  register int old_rbp asm ("rbp");
  register int old_r12 asm ("r12");
  register int old_r13 asm ("r13");
  register int old_r14 asm ("r14");    
  register int old_r15 asm ("r15");
  CalleeSaveRestoreLinux();
  register int rbx asm ("rbx");
  register int rbp asm ("rbp");
  register int r12 asm ("r12");
  register int r13 asm ("r13");
  register int r14 asm ("r14");    
  register int r15 asm ("r15");

  if (old_rbx == rbx) { printf("rbx OK\n"); } else {printf("FAILURE rbx was %d is now %d.\n", old_rbx, rbx); return 1;}
  if (old_rbp == rbp) { printf("rbp OK\n"); } else {printf("FAILURE rbp was %d is now %d.\n", old_rbp, rbp); return 1;}
  if (old_r12 == r12) { printf("r12 OK\n"); } else {printf("FAILURE r12 was %d is now %d.\n", old_r12, r12); return 1;}
  if (old_r13 == r13) { printf("r13 OK\n"); } else {printf("FAILURE r13 was %d is now %d.\n", old_r13, r13); return 1;}
  if (old_r14 == r14) { printf("r14 OK\n"); } else {printf("FAILURE r14 was %d is now %d.\n", old_r14, r14); return 1;}
  if (old_r15 == r15) { printf("r15 OK\n"); } else {printf("FAILURE r15 was %d is now %d.\n", old_r15, r15); return 1;}

  return 0;
}

void __stdcall CalleeSaveRestoreWindowsMM();

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
  CalleeSaveRestoreWindowsMM();
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

int __cdecl main(void) {
  printf("Callee Save starting tests.\n");
  if (test_callee_save_linux() == 0) {
    printf("Callee Save all linux tests passed.\n");
  } else {
    printf("Callee Save some linux test failed.\n");
  }
  if (test_callee_save_windowsMM() == 0) {
    printf("Callee Save all windowsMM tests passed.\n");
  } else {
    printf("Callee Save some windowsMM test failed.\n");
  }

  printf("Callee Save finished tests.\n");
}



