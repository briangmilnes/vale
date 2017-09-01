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
  one   = (uint64_t *) malloc(sizeof(uint64_t)); // rax
  two   = (uint64_t *) malloc(sizeof(uint64_t)); // rsi
  three = (uint64_t *) malloc(sizeof(uint64_t)); // rdx
  four  = (uint64_t *) malloc(sizeof(uint64_t)); // rcx
  five  = (uint64_t *) malloc(sizeof(uint64_t)); // r10
  six   = (uint64_t *) malloc(sizeof(uint64_t)); // r9
  seven = (uint64_t *) malloc(sizeof(uint64_t)); // rdi
  eight = (uint64_t *) malloc(sizeof(uint64_t)); // r8 

  *one   = 0x100000000;
  *two   = 0x200000000;
  *three = 0x300000000;
  *four  = 0x400000000;
  *five  = 0x500000000;
  *six   = 0x600000000;
  *seven = 0x700000000;
  *eight = 0x800000000;

  CalleeSaveRestore(one, two, three, four, five, six, seven, eight);

  if (*one   != 0x100000000)  { printf("one   is %" PRIu64 "\n", *one);   return 1; }
  if (*two   != 0x200000000)  { printf("two   is %" PRIu64 "\n", *two);   return 1; }
  if (*three != 0x300000000)  { printf("three is %" PRIu64 "\n", *three); return 1; }
  if (*four  != 0x400000000)  { printf("four  is %" PRIu64 "\n", *four);  return 1; }
  if (*five  != 0x500000000)  { printf("five  is %" PRIu64 "\n", *five);  return 1; }
  if (*six   != 0x600000000)  { printf("six   is %" PRIu64 "\n", *six);   return 1; }
  if (*seven != 0x700000000)  { printf("seven is %" PRIu64 "\n", *seven); return 1; }
  if (*eight != 0x800000000)  { printf("eight is %" PRIu64 "\n", *eight); return 1; }

  return 0;
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



