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

const int ctr_tests = 4;
uint8_t ctr[][16]      = {{0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff },
                          {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x00 },
                          {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x01 },
                          {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xff, 0x02 }};

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

/*
 What Dworkin must mean here for input block is the CTR going into AES at that key. 
Output block is that CTR  being encrypted. It is then XORd with the plain text
to get the cypher text.

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

// The standard calling sequence of x86 on both windows/linux will give us four arguments in registers.

void __stdcall CTREncryptOneBlockStdCall(const void* expanded_key, const void* counter, const void* input_ptr, void* output_ptr);

int test_encryption_one_block() {
  printf("\nTest AES Encryption One Block \n");
  int status = 1;
  uint8_t expanded_key[176];
  aes_main_i_KeyExpansionStdcall(k, expanded_key);
  for (int i = 0; i < 4; ++i) {
    uint8_t *output = malloc(sizeof(uint8_t) * 16);
    // WTF? I'm not passing in the counter and this works? ==> ctr is zero?
    // rsi is hanging around from the key expansion, but it works. Why?
    CTREncryptOneBlockStdCall(expanded_key, input_block+i, P+i, output);
    if (memcmp(output, C+i, sizeof(uint8_t) * 16) == 0) {
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

// This is a weak test case in that it has no final truncated block.

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

  uint8_t expanded_key[176];
  aes_main_i_KeyExpansionStdcall(k, expanded_key);

  uint8_t *CypherText = (uint8_t *)malloc(sizeof(uint8_t) * 64); 
  uint64_t iv = 0xf7f6f5f4f3f2f1f0; // Swap endianness.
  // Damn it, Dworkin did not start the counter at ZERO in the test vectors.
  // And he xors with the ctr in low endian byte order.
  // We enter it bigendian and byte swap it as needed.
  uint64_t init_ctr = 0xf8f9fafbfcfdfeff;

  // In CTR mode one just encrypts a ctr with a key in sequence and
  // XORs it with the input. So the decrypt is to just run it in the
  // other direction.
  CTR128EncryptStdcall(k,                                                       //edi
                       (const void*)((size_t)PStream + sizeof(PStream)),        //esi
                       (const void *)iv,                                        //rdx
                       PStream,                                                 //rcx
                       expanded_key,                                            //r8
                       CypherText,                                              //r9
                       (const void*)init_ctr);                                  //stack

  if (memcmp(CypherText,CStream,sizeof(PStream)) == 0) {
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

  return 1;
}

int test_decrypt_stream() {
  printf("\nTest AES Decrypt Stream \n");

  uint8_t expanded_key[176];
  aes_main_i_KeyExpansionStdcall(k, expanded_key);

  uint8_t *CypherText = (uint8_t *)malloc(sizeof(uint8_t) * 64); 
  // So he has the IV in the low bytes, reversed and the ctr in the high bytes and is treating it
  // little endian.
  uint64_t iv = 0xf7f6f5f4f3f2f1f0;
  // Damn it, Dworkin did not start the counter at ZERO in the test vectors.
  // And he xors with the ctr in low endian byte order.
  // We enter it bigendian and byte swap it as needed.
  uint64_t init_ctr = 0xf8f9fafbfcfdfeff;

  // In CTR mode one just encrypts a ctr with a key in sequence and
  // XORs it with the input. So the decrypt is to just run it in the
  // other direction.
  CTR128EncryptStdcall(k,                                                       //edi
                       (const void*)((size_t)CStream + sizeof(CStream)),        //esi
                       (const void *)iv,                                        //rdx
                       CStream,                                                 //rcx
                       expanded_key,                                            //r8
                       CypherText,                                              //r9
                       (const void*)init_ctr);                                  //stack

  if (memcmp(CypherText,PStream,sizeof(PStream)) == 0) {
    printf("AES128 CTR Decrypt Stream success\n");
  } else {
    printf("AES128 CTR Decrypt Stream failure\n");
    printf("AES128 CTR Decrypt Stream Input  stream\n");
    print_stream(PStream);printf("\n");
    printf("AES128 CTR Decrypt Stream Output stream\n");
    print_stream(CypherText);printf("\n");
    printf("AES128 CTR Decrypt Stream Should Be stream\n");
    print_stream(CStream);printf("\n");
    return 0;
  }
  return 1;
}

void test_encryption() {
  test_encryption_one_block();
  test_encrypt_stream();
}

void test_decryption() {
  test_decryption_one_block();
  test_decrypt_stream();
}

int __cdecl main(void) {
  printf("AES128 CTR running tests.\n");
  test_encryption();
  test_decryption();
  printf("\nAES128 CTR all tests run.\n");
}
