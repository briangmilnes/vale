/* Test code for AES CTR mode based upon AES CBC test code. 
   BG Milnes, 23 April 2017

  Test data from:

    NIST Special Publication 800-38A 
    Recommendation for Block 
    2001 Edition 
    Cipher Modes of Operation 
    Methods and Techniques 
    Dworkin

*/


#define justfinalcall 1

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
 
 We appear to be using linux identical calling conventions on the mac in that
  we are testing only iswin or !iswin.

 Getting an argument on x86, both windows and linux:
    reads
        stack;
    requires
        // Stack has the right size.
        HasStackSlots(stack, 2); 
	// key_ptr is in frame 0, 32 bit position 0
        let key_ptr := stack[0][0] in
	// ... position 1 
       let key_expansion_ptr := stack[0][1] in ...
	// I can read from key_ptr up to 128 units for the type of heap.
        && ValidSrcAddr(mem, input_key_id, key_ptr, 128, taint);
	// I can write to .. up to 176 bytes.
        && ValidDstAddrs(mem, output_key_expansion_id, key_expansion_ptr, 128, 176);
    ensures
        let key_ptr := old(stack[0][0]) in
        let key_expansion_ptr := old(stack[0][1]) in
	// Seems I have to ensure that I have valid readable stuff after writing.
	ValidSrcAddrs(mem, output_key_expansion_id, key_expansion_ptr, 128, taint, 176);

 Getting an argument on x64, both windows and linux:
       inline win:bool,
       reads
        rcx; rsi; rdi;  
       requires
        let key_ptr := if win then rcx else rdi;
        let key_expansion_ptr := if win then rdx else rsi;
	ValidSrcAddr(mem, input_key_id, key_ptr, 128, taint);                        
        ValidDstAddrs(mem, output_key_expansion_id, key_expansion_ptr, 128, 176);
       ensures
        ValidSrcAddrs(mem, output_key_expansion_id, key_expansion_ptr, 128, taint, 176)

 Question: how to get testX.c to run from crypto/X as compared to crypto/X/X-x64?

*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> // for uint?_t
#include <string.h> // for memcmp
#include <byteswap.h>
#include "gcc_compat.h"

/* Top level behaviour flags. */
int trace  = 1;   // Turn on extra tracing.

/* Utilities */

void print128BitVectorHex(const uint8_t v[16]) {
  printf("{");
  for (int i = 0; i < 16; ++i) {
    printf(" 0x%2x",v[i]);
  }
  printf("}\n");
}


/* Encryption test cases. */

/* Test the counter generation at each step. 
  Although the specification calls this input block/output block, we give it sensible names.

   The specification is vague on how to create the counter. It offers multiple techniques and I have
 yet to understand what is done by default. In the sole test examples they are starting with ictr,
 initial counter below and incrementing by one. However, the spec says one could use only the 
 lowest b bits for this incrementing counter. We can't see here what is going on.

 https://www.cryptopp.com/wiki/CTR_Mode#Counter_Increment for example uses the entire counter as an
 addition.

 Openssl implements a 32 bit CTR for one protocol and 128, 96 and 64 bit counters for AES.

 We'll just do a single 128 bit counter to start with a 64 bit lower part incrementing.

*/

const int ctr_tests = 4;
uint8_t ctr[][16]      = {{0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff },
                          {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x00 },
                          {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x01 },
                          {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x02 }};

void test_alignment_in_memory() {
  printf("test alignment in memory \n");

  printf("as uint64_t * \n");

  uint64_t *v1 = (((uint64_t*)ctr)+0);
  *v1 = bswap_64(*v1);
  printf("%lx \n",*v1);

  uint64_t *v2 = (((uint64_t*)ctr)+1);
  *v2 = bswap_64(*v2);
  printf("%lx \n",*v2);

  printf("as uint64_t * after malloc \n");
  uint64_t *w = (uint64_t *)malloc(sizeof(uint64_t) * 2);
  w[0] = *v2;
  w[1] = *v1;
  printf("high %lx \n",w[1]);
  printf("low  %lx \n",w[0]);

  printf("as uint64_t [2] on stack \n");
  uint64_t x[2];
  x[0] = *v2;
  x[1] = *v1;
  printf("high %lx \n",x[1]);
  printf("low  %lx \n",x[0]);

}

/*

 The test vectors from FIPS 800-38A are written in host standard order. We convert them from
bytes to words with a cast.
*/

#if __x86_64__
typedef struct { uint64_t low, hi; } ctr_t; // C will align fields as increasing address.

void print_ctr(ctr_t *ctr) {
  printf("%lx%lx \n", ctr->hi, ctr->low);
  //  printf("high %lx \n", ctr->hi);
  //  printf("low  %lx \n", ctr->low);
}

ctr_t *make_ctr(uint8_t *v8) {
  ctr_t *ctr = (ctr_t *) malloc(sizeof(ctr));
  uint64_t *v64 = (uint64_t*)v8;
  uint64_t high = bswap_64(*(v64+1)); 
  uint64_t low  = bswap_64(*(v64+0));
  ctr->low = high;
  ctr->hi  = low;
  return ctr;
}
#else

#endif

int test_make_ctr() {
  printf("\nTest Make Counter \n");
  for (int i = 0; i < 4; ++i) {
    printf("make counter ctr %d ",i);
    print_ctr(make_ctr((uint8_t*) (ctr+i)));
  }
}

#ifndef justfinalcall
void __stdcall CTR128Increment64StdCall(const void* input_ptr, void* output_ptr);

int test_counter_increment_64() {
  printf("\nTest Counter Increment 64\n");
  int status = 1;
  for (int i = 0; i < 3; ++i) {
    ctr_t* before      = make_ctr((uint8_t*)(ctr+i));
    ctr_t* incremented = (ctr_t *)malloc(sizeof(ctr_t));
    ctr_t* after       = make_ctr((uint8_t*)(ctr+i+1));
    CTR128Increment64StdCall(before, incremented);
    if (memcmp(incremented, after, sizeof(ctr_t)) == 0) {
      printf("AES128 CTR 64 increment %i succeeded.\n", i);
    } else {
      printf("AES128 CTR 64 increment %i failed.\n", i);
      if (trace == 1) {
	printf("AES128 CTR 64 before      ");
	print_ctr(before);
	printf("AES128 CTR 64 incremented ");	
	print_ctr(incremented);
	printf("AES128 CTR 64 should be   ");
	print_ctr(after);
      }
      status = 0;
    }
    free(before);
    free(incremented);
    free(after);
  }
  return status;
}

void __stdcall CTR128Increment128StdCall(const void* input_ptr, void* output_ptr);

int test_counter_increment_128() {
  printf("\nTest Counter Increment 128\n");
  int status = 1;
  for (int i = 0; i < 3; ++i) {
    ctr_t* before      = make_ctr((uint8_t*)(ctr+i));
    ctr_t* incremented = (ctr_t *)malloc(sizeof(ctr_t));
    ctr_t* after       = make_ctr((uint8_t*)(ctr+i+1));
    CTR128Increment128StdCall(before, incremented);
    if (memcmp(incremented, after, sizeof(ctr_t)) == 0) {
      printf("AES128 CTR 128 increment %i succeeded.\n", i);
    } else {
      printf("AES128 CTR 128 increment %i failed.\n", i);
      if (trace == 1) {
	printf("AES128 CTR 128 before      ");
	print_ctr(before); 
	printf("AES128 CTR 128 incremented ");	
	print_ctr(incremented); 
	printf("AES128 CTR 128 should be   ");
	print_ctr(after);
      }
      status = 0;
    }
    free(before);
    free(incremented);
    free(after);
  }
  return status;
}

/* Test overflow on 128 bit counter. */
uint8_t ctr_ready_to_overflow[] = {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
uint8_t ctr_overflowed       [] = {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };

int test_counter_overflow_64() {
  ctr_t *tooverflow = make_ctr(ctr_ready_to_overflow);
  ctr_t *overflowed = (ctr_t *)malloc(sizeof(ctr_t));
  ctr_t *checkoverflowed = make_ctr(ctr_overflowed);
  CTR128Increment64StdCall(tooverflow, overflowed);
  if (memcmp(overflowed, checkoverflowed, sizeof(ctr_t)) == 0) {
    printf("AES128 CTR 64 overflow succeeded.\n");
    return 1;
  } else {
    printf("AES128 CTR 64 overflow failed.\n");
    printf("to overflow "); print_ctr(tooverflow); 
    printf("overflowed  "); print_ctr(overflowed); 
    return 0;
  }
}

int test_counter_overflow_128() {
  ctr_t *tooverflow = make_ctr(ctr_ready_to_overflow);
  ctr_t *overflowed = (ctr_t *)malloc(sizeof(ctr_t));
  ctr_t *checkoverflowed = make_ctr(ctr_overflowed);
  CTR128Increment128StdCall(tooverflow, overflowed);
  if (memcmp(overflowed, checkoverflowed, sizeof(ctr_t)) == 0) {
    printf("AES128 CTR 128 overflow succeeded.\n");
    return 1;
  } else {
    printf("AES128 CTR 128 overflow failed.\n");
    printf("to overflow "); print_ctr(tooverflow); 
    printf("overflowed  "); print_ctr(overflowed); 
    return 0;
  }
}

int test_counters_64() {
  int status = 1;
  status = status && test_counter_increment_64();
  status = status && test_counter_overflow_64();
  if (status == 1) {
    printf("AES128 CTR 64 counter tests all succeded.\n");
    return 1;
  } else {
    printf("AES128 CTR 64 some counter test failed.\n");
    return 0;
  }
}

int test_counters_128() {
  int status = 1;
  status = status && test_counter_increment_128();
  status = status && test_counter_overflow_128();
  if (status == 1) {
    printf("AES128 CTR 128 counter tests all succeded.\n");
    return 1;
  } else {
    printf("AES128 CTR 128  some counter test failed.\n");
    return 0;
  }
}

#endif


/* Key */
const uint8_t k[]    = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };
/* Initial counter. */
const uint8_t ictr[] = { 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff };

/* The input_block is the incremented iv and it is AES_k(input_block[i]) to get output_block[i] */

const uint8_t input_block[][16] = {
  { 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff },
  { 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x00 },
  { 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x01 },
  { 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x02 }
};

const uint8_t output_block[][16] = {
  { 0xec, 0x8c, 0xdf, 0x73, 0x98, 0x60, 0x7c, 0xb0, 0xf2, 0xd2, 0x16, 0x75, 0xea, 0x9e, 0xa1, 0xe4 },
  { 0x36, 0x2b, 0x7c, 0x3c, 0x67, 0x73, 0x51, 0x63, 0x18, 0xa0, 0x77, 0xd7, 0xfc, 0x50, 0x73, 0xae },
  { 0x6a, 0x2c, 0xc3, 0x78, 0x78, 0x89, 0x37, 0x4f, 0xbe, 0xb4, 0xc8, 0x1b, 0x17, 0xba, 0x6c, 0x44 },
  { 0xe8, 0x9c, 0x39, 0x9f, 0xf0, 0xf1, 0x98, 0xc6, 0xd4, 0x0a, 0x31, 0xdb, 0x15, 0x6c, 0xab, 0xfe }
};


void __stdcall aes_main_i_KeyExpansionStdcall(const void * key_ptr, void *expanded_key_ptr);
#ifndef justfinalcall
void __stdcall AES128EncryptOneBlockStdcall(const void *output, const void *input, const void *expanded_key);

int test_key_aes_encryption() {
  printf("\nTest Key AES Encryption \n");
  int status = 1;
  int size = sizeof(uint8_t) * 16;

  for (int i = 0; i < 4; ++i) {
    uint8_t expanded_key[176];
    uint8_t* aes_k_of_counter = malloc(size);
    aes_main_i_KeyExpansionStdcall(k, expanded_key);
    AES128EncryptOneBlockStdcall((void *)aes_k_of_counter, (const void *) input_block[i], (const void *)expanded_key);

    if (memcmp(aes_k_of_counter, output_block[i], size) == 0) {
      printf("AES128 CTR aes_k_of_counter[%d] succeeded.\n", i);
    } else {
      printf("AES128 CTR aes_k_of_counter[%d] failed.\n", i);
      if (trace == 1) {
	printf("AES128 CTR aes_k_of_counter[%d] ", i);
	print128BitVectorHex(aes_k_of_counter);
	printf("AES128 CTR output_block[%d]  ", i);
	print128BitVectorHex(output_block[i]);
      }
      status = 1;
    }
    free(aes_k_of_counter);
  }
  return status;
}
#endif

/*
F.5.1       CTR-AES128.Encrypt       
Key            2b7e151628aed2a6abf7158809cf4f3c      
Init. Counter  f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff  
Block #1  
Input Block    f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff  
Output Block   ec8cdf7398607cb0f2d21675ea9ea1e4  
Plaintext      6bc1bee22e409f96e93d7e117393172a  
Ciphertext     874d6191b620e3261bef6864990db6ce      
Block #2  
Input Block    f0f1f2f3f4f5f6f7f8f9fafbfcfdff00  
Output Block   362b7c3c6773516318a077d7fc5073ae  
Plaintext      ae2d8a571e03ac9c9eb76fac45af8e51  
Ciphertext     9806f66b7970fdff8617187bb9fffdff      
Block #3  
Input Block    f0f1f2f3f4f5f6f7f8f9fafbfcfdff01  
Output Block   6a2cc3787889374fbeb4c81b17ba6c44  
Plaintext      30c81c46a35ce411e5fbc1191a0a52ef  
Ciphertext     5ae4df3edbd5d35e5b4f09020db03eab      
Block #4  
Input Block    f0f1f2f3f4f5f6f7f8f9fafbfcfdff02  
Output Block   e89c399ff0f198c6d40a31db156cabfe  
Plaintext      f69f2445df4f9b17ad2b417be66c3710  
Ciphertext     1e031dda2fbe03d1792170a0f3009cee      
*/

/* Plain text. */
const uint8_t P[][16]    = { { 0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a},
                             { 0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51},
                             { 0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef},
                             { 0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10}};
/* Cipher Text */
const uint8_t C[][16]    = { { 0x87, 0x4d, 0x61, 0x91, 0xb6, 0x20, 0xe3, 0x26, 0x1b, 0xef, 0x68, 0x64, 0x99, 0x0d, 0xb6, 0xce},
                             { 0x98, 0x06, 0xf6, 0x6b, 0x79, 0x70, 0xfd, 0xff, 0x86, 0x17, 0x18, 0x7b, 0xb9, 0xff, 0xfd, 0xff},
                             { 0x5a, 0xe4, 0xdf, 0x3e, 0xdb, 0xd5, 0xd3, 0x5e, 0x5b, 0x4f, 0x09, 0x02, 0x0d, 0xb0, 0x3e, 0xab},
                             { 0x1e, 0x03, 0x1d, 0xda, 0x2f, 0xbe, 0x03, 0xd1, 0x79, 0x21, 0x70, 0xa0, 0xf3, 0x00, 0x9c, 0xee}};

#ifndef justfinalcall
// The standard calling sequence of x86 on both windows/linux will give us four arguments in registers.

void __stdcall CTREncryptOneBlockStdCall(const void* expanded_key, const void* counter, const void* input_ptr, void* output_ptr);

int test_encryption_one_block() {
  printf("\nTest AES Encryption One Block \n");
  int status = 1;
  uint8_t expanded_key[176];
  aes_main_i_KeyExpansionStdcall(k, expanded_key);
  for (int i = 0; i < 4; ++i) {
    uint8_t *output = malloc(sizeof(uint8_t) * 16);
    // Actually passing args in rax, esi, rsi and rdx.
    CTREncryptOneBlockStdCall(expanded_key, input_block+i, P+i, output);
    if (memcmp(output, C+i, sizeof(uint8_t) *16) == 0) {
      printf("AES128 Encrypt One Block CTR P[%d] succeded.\n",i);
    } else {
      printf("AES128 Encrypt One Block CTR P[%d] failed.\n", i);
      if (trace == 1) {
  	printf("AES128 Encrypt One Block CTR P[%d] \n",i );
  	print128BitVectorHex((uint8_t *)P+i);
  	printf("AES128 Encrypt One Block CTR C[%d] \n",i);
  	print128BitVectorHex((uint8_t *)C+i);
  	printf("AES128 Encrypt One Block CTR output \n");
  	print128BitVectorHex(output);
      }
      status = 0;
    }
  }
  return status;
}

int test_decryption_one_block() {
  printf("\nTest AES Decryption One Block \n");
  int status = 1;
  uint8_t expanded_key[176];
  aes_main_i_KeyExpansionStdcall(k, expanded_key);
  for (int i = 0; i < 4; ++i) {
    uint8_t *output = malloc(sizeof(uint8_t) * 16);
    // Actually passing args in rax, esi, rsi and rdx.
    CTREncryptOneBlockStdCall(expanded_key, input_block+i, C+i, output);
    if (memcmp(output, P+i, sizeof(uint8_t) *16) == 0) {
      printf("AES128 Decrypt One Block CTR C[%d] succeded.\n",i);
    } else {
      printf("AES128 Decrypt One Block CTR C[%d] failed.\n", i);
      if (trace == 1) {
  	printf("AES128 Decrypt One Block CTR C[%d] \n",i );
  	print128BitVectorHex((uint8_t *)P+i);
  	printf("AES128 Decrypt One Block CTR P[%d] \n",i);
  	print128BitVectorHex((uint8_t *)C+i);
  	printf("AES128 Decrypt One Block CTR output \n");
  	print128BitVectorHex(output);
      }
      status = 0;
    }
  }
  return status;
}
#endif

/* Plain text. */
const uint8_t PStream[64]    = {  0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
                                  0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
                                  0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
                                  0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10};
/* Cipher Text */
const uint8_t CStream[64]    = { 0x87, 0x4d, 0x61, 0x91, 0xb6, 0x20, 0xe3, 0x26, 0x1b, 0xef, 0x68, 0x64, 0x99, 0x0d, 0xb6, 0xce,
                                 0x98, 0x06, 0xf6, 0x6b, 0x79, 0x70, 0xfd, 0xff, 0x86, 0x17, 0x18, 0x7b, 0xb9, 0xff, 0xfd, 0xff,
                                 0x5a, 0xe4, 0xdf, 0x3e, 0xdb, 0xd5, 0xd3, 0x5e, 0x5b, 0x4f, 0x09, 0x02, 0x0d, 0xb0, 0x3e, 0xab,
                                 0x1e, 0x03, 0x1d, 0xda, 0x2f, 0xbe, 0x03, 0xd1, 0x79, 0x21, 0x70, 0xa0, 0xf3, 0x00, 0x9c, 0xee};

// This is a bad test case in that it has no final truncated block.


void print_stream(const uint8_t stream[64]) {
  for (int i = 0; i < 64; ++i) {
    printf("0x%2x,", stream[i]);
    if ((i +1) % 16 == 0) {
      printf("\n");
    }
  }
}

// Change code to get compile.
void __stdcall CTR128EncryptStdcall(
                                 const void* key,
                                 const void* input_end, // rsi 
                                 const void* iv,
                                 const void* input,
                                 const void* expanded_key, //r8 - aes wants it here.
                                 void* output,
                                 const void* init_ctr
);

int test_encrypt_stream() {
  printf("\nTest AES Encrypt Stream \n");
  int status = 1;

  uint8_t expanded_key[176];
  aes_main_i_KeyExpansionStdcall(k, expanded_key);

  uint8_t *CypherText = (uint8_t *)malloc(sizeof(uint8_t) * 64); 
  uint64_t iv = 0xf0f1f2f3f4f5f6f7;
  // Damn it, Dworkin did not start the counter at ZERO in the text code.
  uint64_t init_ctr = 0xf8f9fafbfcfdfeff;

  // In CTR mode one just encrypts a ctr with a key in sequence and
  // XORs it with the input. So the decrypt is to just run it in the
  // other direction.
  CTR128EncryptStdcall(k, (const void*)((size_t)PStream + sizeof(PStream)), (const void *)iv, 
                       PStream, expanded_key, CypherText, (const void*)init_ctr);

  if (memcmp(CypherText,CStream,64) == 0) {
    printf("AES128 CTR Encrypt Stream success\n");
  } else {
    printf("AES128 CTR Encrypt Stream failure\n");
    printf("AES128 CTR Encrypt Stream Input  stream\n");
    print_stream(PStream);printf("\n");
    printf("AES128 CTR Encrypt Stream Output stream\n");
    print_stream(CypherText);printf("\n");
    printf("AES128 CTR Encrypt Stream Should Be stream\n");
    print_stream(CStream);printf("\n");
    return 0;
  }

  return status;
}

#ifndef justfinalcall

int test_decrypt_stream() {
  printf("\nTest AES Decrypt Stream \n");
  int status = 1;

  uint8_t expanded_key[176];
  aes_main_i_KeyExpansionStdcall(k, expanded_key);

  uint8_t CypherText[64]; 
  // Damn it, Dworkin did not start the counter at ZERO.
  uint64_t iv = 0xf0f1f2f3f4f5f60xf7;

  // In CTR mode one just encrypts a ctr with a key in sequence and
  // XORs it with the input. So the decrypt is to just run it in the
  // other direction.
  CTR128EncryptStdcall(k, (const void*)((size_t)CStream + sizeof(CStream)), (const void *)iv, 
                       CStream, expanded_key, CypherText, (const void*)init_ctr);
  // Why scratch?
  if (memcmp(CypherText,PStream,64) == 0) {
    printf("AES128 CTR Decrypt Stream success\n");
  } else {
    printf("AES128 CTR Decrypt Stream failure\n");
    printf("AES128 CTR Decrypt Stream Input  stream\n");
    print_stream(PStream);
    printf("AES128 CTR Decrypt Stream Output stream\n");
    print_stream(CypherText);
    printf("AES128 CTR Decrypt Stream Should Be stream\n");
    print_stream(CStream);
    return 0;
  }

  return status;
}

int test_encryption() {
  int b1 = test_encryption_one_block();
  int stream = test_encrypt_stream();

  return (b1 == 1) && (stream == 1);
}


int test_decryption() {
  int b1     = test_decryption_one_block();
  int stream = test_decrypt_stream();

  return (b1 == 1) && (stream == 1);
}


int __cdecl main(void) {
  //  test_alignment_in_memory();
  test_make_ctr();
  int tc64 = test_counters_64();
  int tc128 = test_counters_128();
  int tk = test_key_aes_encryption();
  int te = test_encryption();
  int td = test_decryption();
  
  int status = (tk == 1 && tc64 == 1 && tc128 == 1 && te == 1 && td == 1);

  if (status == 1) {
    printf("AES128 CTR all tests succeded.\n");
    return 0; // give back a return code, not a boolean.
  } else {
    printf("AES128 CTR some test failed.\n");
    return 1;
  }
}

#endif

#ifdef justfinalcall
int __cdecl main(void) {
  //  test_alignment_in_memory();
  test_encrypt_stream();
}
#endif
