/* Test code to learn about loop unrolling in Vale.
   BG Milnes, 23 Jun 2017
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> 
#include <string.h> // for memcmp
#include "gcc_compat.h"
#include <time.h>
#include <inttypes.h>

// How big are our vectors?
uint64_t size = 10000; // Breaks after 10,000 must be some memory size issue.
// How many rounds to test?
uint32_t rounds = 10000;

// Increment all of the uint32s one.
//void __stdcall IncrementVector (const void *input, const void* size);
void __stdcall IncrementVectorUnrolledN(const void *input, const void* size);

uint64_t* getVector(uint64_t size) {
  uint64_t *v = (uint64_t *)malloc(sizeof(uint64_t) * size);
  for (int i = 0; i < size; ++i) {
    *(v+i) = i;
  }
  return v;
}

uint64_t* initVector(uint64_t* v, uint64_t size) {
  for (int i = 0; i < size; ++i) {
    *(v+i) = i;
  }
  return v;
}

int testVector(uint64_t *v) {
  for (int i = 0; i < size; ++i) {
    if (*(v+i) != i+8) {
        return 0;
      }
  }
  return 1;
}

void printVector(const uint64_t *v) {
  printf("{");
  int max = 100;
  if (size < max) {
    max = size;
  }

  for (int i = 0; i < max; ++i) {
    printf("0x%" PRIx64 " " ,*(v+i));
  }
  printf("}\n");
}

/*
void test_IncrementVector() {
  uint64_t *v = getVector(size);
  IncrementVector(v, (void *) (v+size));
  if (testVector(v)) {
      printf("Test Increment Vector succeeded.\n");
    } else {
      printf("Test Increment Vector failed.\n");
      printVector(v);
  }
}
*/

void test_IncrementVectorUnrolledN() {
  uint64_t *v = getVector(size);
  printf("Start vector\n");
  printVector(v);
  clock_t start = clock(), diff;
  for (int i = 0; i < rounds; ++i) {
    initVector(v, size);
    IncrementVectorUnrolledN(v, (void *) (v+size));
  }
  diff = clock() - start;
  int msec = diff * 1000 / CLOCKS_PER_SEC;
  if (testVector(v)) {
      printf("Test Increment Vector Unrolled N succeeded, last round only tested.\n");
      printf("Time taken %d seconds %d milliseconds\n", msec/1000, msec%1000);
    } else {
      printf("Test Increment Vector Unrolled N failed.\n");
      printVector(v);
  }
}

void test_Increments() {
  printf("Loop Unrolling tests.\n");
  //  test_IncrementVector();
  test_IncrementVectorUnrolledN();
  printf("Loop Unrolling tests completed.\n");
}

int __cdecl main(void) {
  test_Increments();
}
