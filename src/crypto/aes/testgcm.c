/* Test code for AES GCM. 
   Brian Milnes, 14 Aug 2017.
*/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> // for uint?_t
#include <string.h> // for memcmp
#include "gcc_compat.h"

// ipter   := rax;
// iendptr := rsi;
// optr    := rdx;
// ctr     := rcx;
// icbptr  := r10; // 96 high bits of IV and 32 bits of zero in memory in 128 bits of memory.
void __stdcall AESGCTR(const void* iptr, const void* iendptr, const void* optr, const void* ctr, const void* icbptr);

void test_aesgctr() {
  

}


int __cdecl main(void) {
  printf("AES128 GCM tests\n");
  test_aesgctr();
  printf("AES128 GCM tests completed.\n");
}
