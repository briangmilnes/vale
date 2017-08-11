/* 

   Someday test regions.

*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> 
#include <string.h> // for memcmp
#include "gcc_compat.h"
#include <time.h>
#include <inttypes.h>
#include <unistd.h>

uint64_t divit(uint64_t this, uint64_t that) {
  return this / that;
}

void test_regions(uint64_t this, uint64_t that) {
  printf("And the division is %" PRIu64 "\n",  divit(this,that));
}



uint64_t __cdecl main(void) {
  test_regions(128,2);
}
