/*
  Test code for returning a value from a value procedure.
  Brian Milnes, 25 Sept 2017.

  Both Linux and 

*/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> // for uint?_t
#include <string.h> // for memcmp
#include <ctype.h> // for memcmp
#include "gcc_compat.h" // For registers.

int __stdcall ReturnValue1();
int __stdcall ReturnValue0();

void test_return_value() {
// According to the ABI we put the value in RAX.
  int r1 = ReturnValue1();
  if (r1 == 1) {
  } else {
    printf("Expecting 1 got %d FAILED\n", r1);
  }
  int r0 = ReturnValue0();
  if (r0 == 0) {
  } else {
    printf("Expecting 0 got %d FAILED\n", r0);
  }
}

void __cdecl main(void) {
  printf("Test return value from Vale\n");
  test_return_value();
  printf("Test return value from Vale Finished.\n");
}
