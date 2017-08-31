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
void __stdcall CalleeSaveRestore(void *one, void *two, void *three, void *four, void *five, void *six, void *seven, void *eight);

uint64_t *one;
uint64_t *two;
uint64_t *three;
uint64_t *four;
uint64_t *five;
uint64_t *six;
uint64_t *seven;
uint64_t *eight;

int test_callee_save() {
  one   = (uint64_t *) malloc(sizeof(uint64_t));
  two   = (uint64_t *) malloc(sizeof(uint64_t));
  three = (uint64_t *) malloc(sizeof(uint64_t));
  four  = (uint64_t *) malloc(sizeof(uint64_t));
  five  = (uint64_t *) malloc(sizeof(uint64_t));
  six   = (uint64_t *) malloc(sizeof(uint64_t));
  seven = (uint64_t *) malloc(sizeof(uint64_t));
  eight = (uint64_t *) malloc(sizeof(uint64_t));

  *one   = 0x100000000;
  *two   = 0x200000000;
  *three = 0x300000000;
  *four  = 0x400000000;
  *five  = 0x500000000;
  *six   = 0x600000000;
  *seven = 0x700000000;
  *eight = 0x800000000;

  CalleeSaveRestore(one, two, three, four, five, six, seven, eight);

  if (*one   != 0x1)   { return 1; }
  if (*two   != 0x2)   { return 1; }
  if (*three != 0x3)   { return 1; }
  if (*four  != 0x4)   { return 1; }  
  if (*five  != 0x5)   { return 1; }
  if (*six   != 0x6)   { return 1; }
  if (*seven != 0x7)   { return 1; }
  if (*eight != 0x8)   { return 1; }
}

int __cdecl main(void) {
  printf("Callee Save starting tests.\n");
  if (test_callee_save() == 0) {
    printf("Callee Save all tests passed.\n");
  } else {
    printf("Callee Save some test failed.\n");
  }
  printf("Callee Save finished tests.\n");
}



