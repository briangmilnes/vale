/* Test code to learn about loop unrolling in Vale.
   BG Milnes, 23 Jun 2017
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> 
#include <string.h> // for memcmp
#include "gcc_compat.h"

// How big are our vectors?
uint64_t size = 1000;

// How many rounds for benchmarking?
int rounds = 1000;

// Increment all of the uint32s one.
void __stdcall IncrementVector (const void *input, const void* size);
void __stdcall IncrementVector2(const void *input, const void* size);
void __stdcall IncrementVector4(const void *input, const void* size);
void __stdcall IncrementVector8(const void *input, const void* size);

uint32_t* getVector(uint32_t size) {
  uint32_t *v = (uint32_t *)malloc(sizeof(uint32_t) * size);
  for (int i = 0; i < size; ++i) {
    *(v+i) = i;
  }
  return v;
}

int testVector(uint32_t *v) {
  for (int i = 0; i < size; ++i) {
    if (*(v+i) != i+1) {
        return 0;
      }
  }
  return 1;
}

void test_IncrementVector() {
  uint32_t *v = getVector(size);
  IncrementVector(v, (void *) (v+size));
  if (testVector(v)) {
      printf("Test Increment Vector succeeded.\n");
    } else {
      printf("Test Increment Vector failed.\n");
  }
}

void test_IncrementVector2() {
  uint32_t *v = getVector(size);
  IncrementVector(v, (void*) (v+size));
  if (testVector(v)) {
      printf("Test Increment Vector 2 succeeded.\n");
    } else {
      printf("Test Increment Vector 2 failed.\n");
  }
}

void test_IncrementVector4() {
  uint32_t *v = getVector(size);
  IncrementVector(v, (void*) (v+size));
  if (testVector(v)) {
      printf("Test Increment Vector 4 succeeded.\n");
    } else {
      printf("Test Increment Vector 4 failed.\n");
  }
}

void test_IncrementVector8() {
  uint32_t *v = getVector(size);
  IncrementVector(v, (void*)(v+size));
  if (testVector(v)) {
      printf("Test Increment Vector 8 succeeded.\n");
    } else {
      printf("Test Increment Vector 8 failed.\n");
  }
}

void test_Increments() {
  printf("Loop Unrolling tests.\n");
  test_IncrementVector();
  test_IncrementVector2();
  test_IncrementVector4();
  test_IncrementVector8();
  printf("Loop Unrolling tests completed.\n");
}

int __cdecl main(void) {
  test_Increments();
}
