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
#include <unistd.h>

// How big are our vectors?
uint64_t size = 10000; // Breaks after 10,000 must be some memory size issue.
// How many rounds to test?
uint32_t rounds = 10000;

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
        printf("testVector failed at %d\n", i);
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
    printf("%" PRIu64 " " ,*(v+i));
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

//void __stdcall IncrementVector (const void *input, const void* size);
void __stdcall IncrementVectorUnrolled1(const void *input, const void* size,
                                        // Can't see how to increase the stack pointers.
                                        const void *one,
                                        const void *two,
                                        const void *three,
                                        const void *four,
                                        const void *five,
                                        const void *six,
                                        const void *seven,
                                        const void *eight,
                                        const void *nine,
                                        const void *ten);

// Something is wrong with my save, restore registers.
clock_t start;

void test_IncrementVectorUnrolled1() {
  uint64_t *v = getVector(size);
  start = clock();
  for (int i = 0; i < rounds; ++i) {
    initVector(v, size);
    IncrementVectorUnrolled1(v, (void *) (size * 8),
                             (void *)0, (void *)0, (void *)0, (void *)0, (void *)0, 
                             (void *)0, (void *)0, (void *)0, (void *)0, (void *)0);
  }
  clock_t end = clock();
  clock_t diff = end - start;
  long int msec = diff * 1000 / CLOCKS_PER_SEC;
  if (testVector(v)) {
      printf("Test Increment Vector Unrolled 1 succeeded, last round only tested.\n");
      printf("Time taken %ld seconds %ld milliseconds\n", msec/1000, msec%1000);
    } else {
      printf("Test Increment Vector Unrolled 1 failed.\n");
      printf("Start vector\n");
      printVector(v);
      printf("Returned vector\n");
      printVector(v);
  }
}

//void __stdcall IncrementVector (const void *input, const void* size);
void __stdcall IncrementVectorUnrolled4(const void *input, const void* size,
                                        // Can't see how to increase the stack pointers.
                                        const void *one,
                                        const void *two,
                                        const void *three,
                                        const void *four,
                                        const void *five,
                                        const void *six,
                                        const void *seven,
                                        const void *eight,
                                        const void *nine,
                                        const void *ten);

void test_IncrementVectorUnrolled4() {
  uint64_t *v = getVector(size);
  start = clock();
  for (int i = 0; i < rounds; ++i) {
    initVector(v, size);
    IncrementVectorUnrolled4(v, (void *) (size * 8),
                             (void *)0, (void *)0, (void *)0, (void *)0, (void *)0, 
                             (void *)0, (void *)0, (void *)0, (void *)0, (void *)0);
  }
  clock_t end = clock();
  clock_t diff = end - start;
  long int msec = diff * 1000 / CLOCKS_PER_SEC;
  if (testVector(v)) {
      printf("Test Increment Vector Unrolled 4 succeeded, last round only tested.\n");
      printf("Time taken %ld seconds %ld milliseconds\n", msec/1000, msec%1000);
    } else {
      printf("Test Increment Vector Unrolled 4 failed.\n");
      printf("Start vector\n");
      printVector(v);
      printf("Returned vector\n");
      printVector(v);
  }
}

//void __stdcall IncrementVector (const void *input, const void* size);
void __stdcall IncrementVectorUnrolled8(const void *input, const void* size,
                                        // Can't see how to increase the stack pointers.
                                        const void *one,
                                        const void *two,
                                        const void *three,
                                        const void *four,
                                        const void *five,
                                        const void *six,
                                        const void *seven,
                                        const void *eight,
                                        const void *nine,
                                        const void *ten);

void test_IncrementVectorUnrolled8() {
  uint64_t *v = getVector(size);
  start = clock();
  for (int i = 0; i < rounds; ++i) {
    initVector(v, size);
    IncrementVectorUnrolled8(v, (void *) (size * 8),
                             (void *)0, (void *)0, (void *)0, (void *)0, (void *)0, 
                             (void *)0, (void *)0, (void *)0, (void *)0, (void *)0);   
  }
  clock_t end = clock();
  clock_t diff = end - start;
  long int msec = diff * 1000 / CLOCKS_PER_SEC;
  if (testVector(v)) {
      printf("Test Increment Vector Unrolled 8 succeeded, last round only tested.\n");
      printf("Time taken %ld seconds %ld milliseconds\n", msec/1000, msec%1000);
    } else {
      printf("Test Increment Vector Unrolled 8 failed.\n");
      printf("Start vector\n");
      printVector(v);
      printf("Returned vector\n");
      printVector(v);
  }
}

void test_Increments() {
  printf("Loop Unrolling tests.\n");
    test_IncrementVectorUnrolled1();
    test_IncrementVectorUnrolled4();
    test_IncrementVectorUnrolled8();
  printf("Loop Unrolling tests completed.\n");
}

int __cdecl main(void) {
  test_Increments();
}
