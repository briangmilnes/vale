/* Test code for AES GCM. 
   Brian Milnes, 14 Aug 2017.
*/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h> // for uint?_t
#include <string.h> // for memcmp
#include <ctype.h> // for memcmp
#include "gcc_compat.h" // For registers.

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

uint8_t hexDigitToUint8(char digit) {
    digit = tolower(digit);
    if ('0' <= digit && digit <= '9') 
        return (uint8_t)(digit - '0');
    else if ('a' <= digit && digit <= 'f') 
        return (uint8_t)(digit - ('a' - 10));
    else
      return (uint8_t) -1;
}

uint8_t *HexStringToUint8(char* hexstring, int min) {
  int      len    = (strlen(hexstring) < min ? min : strlen(hexstring)) / 2;
  uint8_t *output = malloc(len);
  memset(output, 48, len); // Put char zeros in.
  for(int i= 0; i < len; i++) {
    *(output+i) = hexDigitToUint8(hexstring[2 * i]) * 16 + hexDigitToUint8(hexstring[2 * i + 1]);
  }  
  return output;
}

/* Testing structures. */

typedef struct {
  int Count;
  char* Key;
  char* IV; 
  char* PT;
  char* AAD;
  char* CT;
  char* Tag;
  int   FAIL; // On decrypt does this have a failing MAC?
} CTEST;

typedef struct {
  int Count;
  uint8_t *Key; // 16 bytes as we are AES-128 only.
  uint8_t *IV;  // 16 bytes because we pad out zeros for the counter.
  uint8_t *PT;  // Plain text.
  int PTlen;    // Length in bytes.
  uint8_t *AAD;  // Fixed at 128 
  uint8_t *CT;  // Crypt test of PTLen.
  uint8_t *Tag;  // 16 as we are only building 128 bit tags/MAC.
  int     FAIL; // On decrypt does this have a failing MAC?
} UTEST;


UTEST *mkUTEST(CTEST *s) {
  UTEST *u = malloc(sizeof(UTEST));  
  u->Count = s->Count;
  u->PTlen = strlen(s->PT) / 2;
  u->Key   = HexStringToUint8(s->Key,16);
  u->IV    = HexStringToUint8(s->IV, 16);
  u->PT    = HexStringToUint8(s->PT, 16);
  u->AAD   = HexStringToUint8(s->AAD,16);
  u->CT    = HexStringToUint8(s->CT, 16);
  u->Tag   = HexStringToUint8(s->Tag,16);
  u->FAIL  = s->FAIL;
  return u;
}

void printCTEST(CTEST *c) {
  printf("CTEST {\n");
  printf("    Count %d,\n", c->Count);
  printf("    Key   %s,\n", c->Key);
  printf("    IV    %s,\n", c->IV);
  printf("    PT    %s,\n", c->PT);
  printf("    AAD   %s,\n", c->AAD);
  printf("    CT    %s,\n", c->CT);
  printf("    Tag   %s,\n", c->Tag);
  printf("    FAIL  %d,\n", c->FAIL);
  printf("}\n");
}

void printUTEST(UTEST *e) {
  printf("UTEST {\n");
  printf("    Count %d,\n", e->Count);
  printf("    Key   "); print128BitVectorHex(e->Key);
  printf("    IV    "); print128BitVectorHex(e->IV);
  printf("    PT    "); print128BitVectorHex(e->PT);
  printf("    PTlen %d,\n", e->PTlen);
  printf("    AAD   "); print128BitVectorHex(e->AAD);
  printf("    CT    "); print128BitVectorHex(e->CT);
  printf("    Tag   "); print128BitVectorHex(e->Tag);
  printf("    FAIL %d\n", e->FAIL);
  printf("}\n");
}

void test_tests(CTEST *c) {
  printf("Testing CTEST/ETEST conversion\n");
  printCTEST(c);
  printUTEST(mkUTEST(c));
}

// Our three calls so far, only doing CTR not GHASH mac creation.
void __stdcall aes_main_i_KeyExpansionStdcall(const void * key_ptr, void *exp_key_ptr);
void __stdcall AES128GCTREncryptStdcall(void* exp_key_ptr, const void* iptr, const void* iendptr, const void* optr, const void* ivptr);
int __stdcall AES128GCTRDecryptStdcall(void* exp_key_ptr, const void* iptr, const void* iendptr, const void* optr, const void* ivptr);
// TO DO add AAD and TAG.

// Test vectors from,https://pdfs.semanticscholar.org/114a/4222c53f1a6879f1a77f1bae2fc0f8f55348.pdf seem broken as they don't have AAD.
// Test vectors from https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/cavp-testing-block-cipher-modes#GCMVS

//[Keylen = 128]
//[IVlen = 96]
//[PTlen = 0]
//[AADlen = 0]
//[Taglen = 128]

// Mac only, no PT.
CTEST ctestsmac_encrypt[] = {
  { 0, "11754cd72aec309bf52f7687212e8957", "3c819d9a9bed087615030b65", "", "", "", "250327c674aaf477aef2675748cf6971", 0},
  { 1, "ca47248ac0b6f8372a97ac43508308ed", "ffd2b598feabc9019262d2be", "", "", "", "60d20404af527d248d893ae495707d1a", 0},
  { 2, "db1ad0bd1cf6db0b5d86efdd8914b218", "36fad6acb3c98e0138aeb9b1", "", "", "", "5ee2ba737d3f2a944b335a81f6653cce", 0},
  { 3, "1c7135af627c04c32957f33f9ac08590", "355c094fa09c8e9281178d34", "", "", "", "b6ab2c7d906c9d9ec4c1498d2cbb5029", 0},
  { 4, "6ca2c11205a6e55ab504dbf3491f8bdc", "b1008b650a2fee642175c60d", "", "", "", "7a9a225d5f9a0ebfe0e69f371871a672", 0},
  { 5, "69f2ca78bb5690acc6587302628828d5", "701da282cb6b6018dabd00d3", "", "", "", "ab1d40dda1798d56687892e2159decfd", 0},
  { 6, "dcf4e339c487b6797aaca931725f7bbd", "2c1d955e35366760ead8817c", "", "", "", "32b542c5f344cceceb460a02938d6b0c", 0},
  { 7, "7658cdbb81572a23a78ee4596f844ee9", "1c3baae9b9065961842cbe52", "", "", "", "70c7123fc819aa060ed2d3c159b6ea41", 0},
  { 8, "281a570b1e8f265ee09303ecae0cc46d", "8c2941f73cf8713ad5bc13df", "", "", "", "a42e5e5f6fb00a9f1206b302edbfd87c", 0},
  { 9, "cd332a986f82d98c215278131ad387b7", "1d12b259f44b873d3942bc11", "", "", "", "34238023648185d7ef0cfcf5836e93cc", 0},
  { 10, "80e1d98d10b27237386f029189ec0448", "239ebab2f524fd62c554a190", "", "", "", "4c0f29d963f0ed68dccf34496cf43d00", 0},
  { 11, "40650cdb61e3e19a1a98fb4e05377d35", "69f0a81aaf6bb8486282f1b9", "", "", "", "2657e12dec21c3ecf071af6179529fb4", 0},
  { 12, "1e89a6cd7528cce1e2b2b5f7fd2b6b52", "e11fd427a782d543f78efc60", "", "", "", "eeedff874c8edeea53e8be2a13afd81b", 0},
  { 13, "2a7ad6146676057db777dea4683d0d45", "ed721ea67456d4594aafbd51", "", "", "", "ee3cab5778888439d90fa718b75738ad", 0},
  { 14, "a364f494a4cd0147c34731074dc1a85b", "4aa8470dd404e4054b30093a", "", "", "", "d8a7bba3a451902e3adc01060c3c91a7", 0},
};

//[Keylen = 128]
//[IVlen = 96]
//[PTlen = 128]
//[AADlen = 128]
//[Taglen = 128]

CTEST ctests128_encrypt[] = {
  { 0, "c939cc13397c1d37de6ae0e1cb7c423c", "b3d8cc017cbb89b39e0f67e2", "c3b3c41f113a31b73d9a5cd432103069", "24825602bd12a984e0092d3e448eda5f", "93fe7d9e9bfd10348a5606e5cafa7354", "0032a1dc85f1c9786925a2e71d8272dd", 0},
  { 1, "599eb65e6b2a2a7fcc40e51c4f6e3257", "d407301cfa29af8525981c17", "a6c9e0f248f07a3046ece12125666921", "10e72efe048648d40139477a2016f8ce", "1be9359a543fd7ec3c4bc6f3c9395e89", "e2e9c07d4c3c10a6137ca433da42f9a8", 0},
  { 2, "2d265491712fe6d7087a5545852f4f44", "c59868b8701fbf88e6343262", "301873be69f05a84f22408aa0862d19a", "67105634ac9fbf849970dc416de7ad30", "98b03c77a67831bcf16b1dd96c324e1c", "39152e26bdc4d17e8c00493fa0be92f2", 0},
  { 3, "1fd1e536a1c39c75fd583bc8e3372029", "281f2552f8c34fb9b3ec85aa", "f801e0839619d2c1465f0245869360da", "bf12a140d86727f67b860bcf6f34e55f", "35371f2779f4140dfdb1afe79d563ed9", "cc2b0b0f1f8b3db5dc1b41ce73f5c221", 0},
  { 4, "7b0345f6dcf469ecf9b17efa39de5359", "b15d6fcde5e6cf1fa99ba145", "822ae01a0372b6aa46c2e5bf19db92f2", "72e9cb26885154d4629e7bc91279bb19", "382e440694b0c93be8dd438e37635194", "2fa042bff9a9cd35e343b520017841bb", 0},
  { 5, "9db91a40020cdb07f88769309a6ac40b", "f89e1b7e598cc2535a5c8659", "f4a5003db4a4ebbc2fdb8c6756830391", "70910598e7abd4f0503ecd9e21bdafb5", "40d7fc4ccc8147581f40655a07f23ee9", "243331b48404859c66af4d7b2ee44109", 0},
  { 6, "e2f483989b349efb59ae0a7cadc74b7a", "3338343f9b97ebb784e75027", "14d80ad66e8f5f2e6c43c3109e023a93", "8b12987e600ff58df54f1f5e62e59e61", "43c2d68384d486e9788950bbb8cd8fd1", "47d7e9144ff0ed4aa3300a944a007882", 0},
  { 7, "5c1155084cc0ede76b3bc22e9f7574ef", "9549e4ba69a61cad7856efc1", "d1448fa852b84408e2dad8381f363de7", "e98e9d9c618e46fef32660976f854ee3", "f78b60ca125218493bea1c50a2e12ef4", "d72da7f5c6cf0bca7242c71835809449", 0},
  { 8, "2352503740a4e1b22dcc9c002f53bd11", "474ecccc3182e03c80a7be74", "dc1c35bc78b985f2d2b1a13ce635dd69", "a1bc98dacec4b6aa7fee6dfa0802f21a", "3f6f4daf6d07743b9bd2a069d3710834", "b9c2b319adbd743f5e4ffd44304a1b5f", 0},
  { 9, "fc1f971b514a167865341b828a4295d6", "8851ea68d20ce0beff1e3a98", "2fec17b1a9570f6651bbe9a657d82bce", "ece8d5f63aebda80ebde4b750637f654", "2d27e5fa08e218f02b2e36dfad87a50e", "eb9966774c588a31b71c4d8daa495e9e", 0},
  { 10, "00ef3c6762be3fbab38154d902ff43b5", "c3c1c3079cda49a75a53b3cc", "be425e008e9b0c083b19a2d945c2ede9", "714fa1d6904187b3c5c08a30dffc86e8", "c961a1758dcf91e539658372db18968e", "eaf9bda9b3322f501f7329cb61c1c428", 0},
  { 11, "2d70b9569943cc49cdef8495bdb6f0e6", "b401d0f50880a6211fde9d9c", "47a87a387944f739bd3cb03e0e8be499", "592e7276bda066327f2b3cd8cc39f571", "c1b2af4d273231e71e7e066c206bf567", "c68d8d3cf8b89e6b15f623d60fef60bd", 0},
  { 12, "775cb7f8dc73f04fe4f9d22126bb7b57", "81ceb17deee19b8153ff927c", "8242c6c0eed6d5d1ab69cd11dbe361d0", "97e07cd65065d1edc863192de98bc62c", "580f063ab1a4801d279e4ee773200abe", "29e4d7e054a6b0a4e01133573fbe632b", 0},
  { 13, "58ba3cb7c0a0cf5775002bf3b112d051", "bb923c93ddca303ab131238d", "6b93d2d92de05b53769ec398ab8097dc", "0898ea55c0ca0594806e2dc78be15c27", "d0564006b1897bf21922fef4f6386fd4", "3a92f3c9e3ae6b0c69dcb8868d4de27c", 0},
  { 14, "955b761de8e98f37acb41259fa308442", "a103db8a0825e606b70427fc", "d18344c86caffc4237d2daae47817b13", "c2d0d8b77a6fd03ced080e0f89de8a4b", "065d228c1289007a682aa847a36b6f30", "fb367f47922d67c84bf47aabb2b98421", 0}
};

CTEST ctestsmac_decrypt[] = {
  { 0, "cf063a34d4a9a76c2c86787d3f96db71", "113b9785971864c83b01c787", "", "", "", "72ac8493e3a5228b5d130a69d2510e42", 0},
  { 1, "a49a5e26a2f8cb63d05546c2a62f5343", "907763b19b9b4ab6bd4f0281", "", "", "", "a2be08210d8c470a8df6e8fbd79ec5cf", 1},
  { 2, "2ad0bf5aeb47a0c1a98da3dfdab4fded", "25f1b6091ee7040fea4ba854", "", "", "", "d7963d240317653e01cf5abe5d0966ae", 0},
  { 3, "d8cd400a0a73d114cd3ecf36537cab3d", "3c162c9f16a49b8fe6c92a81", "", "", "", "4203aec165f9d397cf9009770a088c16", 1},
  { 4, "a982a7bae2b3eae1b7832f16faf693b4", "78d2d2fa43850483ce933576", "", "", "", "ceabb89ee3179e25ed32d5a225006361", 0},
  { 5, "f9e3992196f7d7a21bd956f4b5a5ffce", "0794a6bdf5f198c9f193b9ba", "", "", "", "f8247fd5dc7bd6d40e96af32aa9c1889", 0},
  { 6, "c91aab7ebe13653a71a4232fd1beb793", "7799464b6de6383da0daec52", "", "", "", "00c4f7033f3c05e9d531f3ca573dc98d", 1},
  { 7, "e7e4eefd0a3abd4ee1bef270d257eab7", "f548f2a04a50a2f0342b2250", "", "", "", "044159b8a18668167fbd28ac500c20fe", 0},
  { 8, "1bd49e553457459aee1b5d83e7c216a2", "2b37cf40ed2685eb2a907cd0", "", "", "", "fcb41d17fdb023d4d14f84a387d3ad77", 1},
  { 9, "4d6486fa68ce5a14b9db7334ab4838cb", "afad3f4190d56a1b8eb08e58", "", "", "", "4bda04755b7ce9da020ce7467a5ced8f", 1},
  { 10, "da5b59d5eb448fd6c08c350df9a82114", "15fb65d9fe2fa27f226312c0", "", "", "", "e407fccbb9f00eeb9cef4a520cff957c", 1},
  { 11, "07d5a7d405b21c64d74cc0988693b784", "2eefd7990ea025925e9ca6f9", "", "", "", "1439522d18c9eb129f1f776590027761", 1},
  { 12, "48760dec952010140ffc4b4078438b56", "930cc3ff276d7bbb74d187ef", "", "", "", "8673dcb97934d54dc17de0037344737f", 1},
  { 13, "ed7c50762dc0dc4aa5c8be4cf0a56b88", "50dfb73b5034cffb6709af8f", "", "", "", "cb02203ee8eccec446ed1c2cf68fd1c0", 1},
  { 14, "b5d4b3e80a56adbc780ff02c5da6a7ab", "abc5b96c5e872502971dcc55", "", "", "", "4e85677cc16e2b2fb50a2ca9c0ac1b9c", 1}
};

CTEST ctests128_decrypt[] = {
  {0,  "816e39070410cf2184904da03ea5075a", "32c367a3362613b27fc3e67e", "ecafe96c67a1646744f1c891f5e69427", "552ebe012e7bcf90fcef712f8344e8f1", "f2a30728ed874ee02983c294435d3c16", "ecaae9fc68276a45ab0ca3cb9dd9539f", 0},
  {1,  "867fc5d5476d5008f0703d81e3622255", "22945529dff947c3c9264df7", "FAIL" /* FAIL */                     , "1c785025e5a2678e4b29b29276e395bb", "261a9efd4f32bc3d07c115b4edcf8adf", "87fdf1261846164a950c37a3f2eea17d", 1},
  {2,  "3d17f97bf1dae4268b6610dc90c70b28", "ebcd88fc18d4c99d28524d41", "ec18a057c22d12373b5efe4d177eb068", "0128a239bb43c12885f9591386ecac0f", "681a4feac147ee2d25e9191aaa4c8830", "144def0210af9348f07afe27e65bdc7e", 0},
  {3,  "5c32091e288d4780fcaff52a69c1234e", "bedb360b22847fc2ff60ab78", "FAIL" /* FAIL */                     , "60c883306c91a0e6e98f8d7bf7ee9fd9", "dc7c3a89a00b688af2bd372530bfed0b", "ffb93af9106e95e9a65ef147765970da", 1},
  {4,  "75fb7f243336b78979988c08f39c44ab", "69fed95864cad27f83503f8d", "FAIL" /* FAIL */                     , "7bb1d878239966163a3db5712f57b096", "b4783565715e8cdb46f8a2bb72030ce2", "bfee0dda5e1afde5c7b0928774f80d21", 1},
  {5,  "7a3d71615ec0e6ee2257f33d06611b89", "1ccf177092a1518be9f6612f", "9c0e1b4ea43af8b1d4d173b31424fa40", "d0bb72968ff7fdbd3499d6e7a34ec043", "0753ecc820e7ed3b6ce6b60dde776fdf", "3a7c708e0e6e74a654987a257ab96461", 0},
  {6,  "bf283c584efcc4778bc6091804b2b66d", "1fad1f81b45de44392497629", "c40fee049bac9b688601506d63450869", "51f94491184b13f46defe609642adc16", "791856131d5d4ed0e7b205b8b2ff4012", "f2e8b0bc4e1bdd9d2604c0607c4f7fc7", 0},
  {7,  "93477009c0bbbde3aead970dd96811a9", "6f096b1f3773a928301aea03", "FAIL" /* FAIL */                     , "8643e7d1686b916cdd2b74f1cf26ce72", "7e61a6b6cb73c187d08509ad5b940a2d", "f98afcefacdc71410eef471d5bb2a599", 1},
  {8,  "ec3f4315316aca1bdc2806210bbd36ad", "fa0698f32e058389f11e519e", "FAIL" /* FAIL */                     , "16a9fbf2fe33d6c8c0b22117bc0e6634", "414ac255598157e3b506876d00843b31", "88f4a30ea229c8c4641f60363436702c", 1},
  {9,  "b431bd21c8ae9845c469b8906618e715", "8579a353df1f7dd0bac1229c", "8347a939a90f4e33dfc70c70e6447994", "bca7919e99c8de9ccb7d2dc2e1fde95b", "79d9a0a2c7536fde809aeb9f084739a0", "2b7d96b083a1fdafab7b64839a53b90d", 0},
  {10, "71ccaf526ec51e5117c22869289d1b10", "9fc7b2fc3a762a9c28f64200", "FAIL" /* FAIL */                     , "6f65ed418dad09ffd883afcb3c3f2333", "0b8ddf8514761fc60ca20c11b0a9e27b", "22e0056532a847859e2aa181b80fd97e", 1},
  {11, "42deade4fcd2728eef0c258f0f80c56e", "033393d7167c23327271b58f", "FAIL" /* FAIL */                     , "0cc5f4e993fcdbc81904f5b26071b360", "34ae2559e79d88aa25ec8c0a97f4f8c1", "cff5af162a6bf4b7e9169632a40f3f41", 1},
  {12, "1fe8b08b096103debbebe1ed1b5e0ecf", "4f2442796ffc2cd7b7a6b6c7", "5b90f102d5cb5c4cf10db51f88d5bf03", "61ca6232340df229dea57b2bc45eed28", "9c953a6b978ffd3457c0c1e2f9e29358", "b61b58eda5efa804d42b8038a9ca6472", 0},
  {13, "3f8a905c888fc42dcceac21ae09027c1", "fb3db97addf0f67eb369c62c", "FAIL" /* FAIL */                     , "743cdf63d80bd79d4664af2f5625d95d", "b74eae31f9d55f9666899c8474cdc80e", "a2bc61b1e16ac2ac9c23bf40bbfe18ad", 1},
  {14, "fba087aa3a2b5b4109e36938d011a0b0", "f92af1ed2065fac9eb4d7601", "FAIL" /* FAIL */                     , "700613d946dedd760da35483ab668685", "90501a414620af8e76dcf165f5cbe603", "63703fac96bb981f74bc52f557271b2c", 1}
};

int test_ghash_encrypt(int i, CTEST *c) {
  UTEST   *u = mkUTEST(c);
  uint8_t  exp_key_ptr[176];
  uint8_t *optr = malloc(u->PTlen);

  printf("\nTest test_ghash_encrypt %d ", i);
  aes_main_i_KeyExpansionStdcall(u->Key, exp_key_ptr);

  // GCC is generating:
  //	movslq	32(%rbp), %rdx
  //	movq	24(%rbp), %rsi
  //	movq	%rbx, %rcx
  //	movq	16(%rbp), %r8
  //	movq	%rsp, %rdi
  //	addq	%rsi, %rdx
  //	call	AES128GCTREncrypt
  AES128GCTREncryptStdcall(exp_key_ptr, u->PT, u->PT + u->PTlen, optr, u->IV);
  if (memcmp(optr, u->PT, u->PTlen) == 0) {
    printf("SUCCEEDED\n"); 
    return 1;
  } else {
    printf("FAILED\n");
      if (trace == 1) {
        printUTEST(u);
        printf("\n decrypted output calculated ");
  	print128BitVectorHex(optr);
     }
    return 0;
  }
}

int test_ghash_encrypts(int num, CTEST c[]) {
  printf("\nStarting tests test_ghash_encrypts.\n");
  int i = 0;
  for (i = 0; i < num; ++i) {
    test_ghash_encrypt(i, &(c[i]));
  }
  printf("\nEnding test test_ghash_encrypts.\n");
}

int test_ghash_decrypt(int i, CTEST *c) {
  UTEST   *u = mkUTEST(c);
  uint8_t  exp_key_ptr[176];
  uint8_t *optr = malloc(u->PTlen);

  printf("\nTest test_ghash_decrypt %d ", i);
  aes_main_i_KeyExpansionStdcall(u->Key, exp_key_ptr);

  // GCC is generating:
  //	movslq	32(%rbp), %rdx
  //	movq	24(%rbp), %rsi
  //	movq	%rbx, %rcx
  //	movq	16(%rbp), %r8
  //	movq	%rsp, %rdi
  //	addq	%rsi, %rdx
  //	call	AES128GCTREncrypt
  int code = AES128GCTRDecryptStdcall(exp_key_ptr, u->CT, u->CT + u->PTlen, optr, u->IV);
  if (c->FAIL) {
    if (code == 1) {
      printf("Expecting FAIL, found FAIL, SUCCEEDED.\n");
      return 1;
    } else {
      printf("Expecting FAIL, found success, FAILED.\n");
      if (trace == 1) {
        printUTEST(u);
        printf("\n decrypted output calculated ");
  	print128BitVectorHex(optr);
     }
    }
  } else {
    printf("Expecting success, found success, testing decrypted text.\n");
  }
  if (memcmp(optr, u->CT, u->PTlen) == 0) {
    printf("SUCCEEDED\n"); 
    return 1;
  } else {
    printf("FAILED\n");
      if (trace == 1) {
        printUTEST(u);
        printf("\n decrypted output calculated ");
  	print128BitVectorHex(optr);
     }
    return 0;
  }
}

int test_ghash_decrypts(int num, CTEST c[]) {
  printf("\nStarting tests test_ghash_decrypts.\n");
  int i = 0;
  for (i = 0; i < num; ++i) {
    test_ghash_decrypt(i, &(c[i]));
  }
  printf("\nEnding test test_ghash_decrypts\n");
}


int test_aesgctr() {
  printf("Starting AES128 GCTR tests \n");
  //  test_tests(&(ctests128[0])); // just during development.
  printf("Finished AES128 GCTR tests \n");
  test_ghash_encrypts(15, ctests128_encrypt);
  test_ghash_decrypts(14, ctests128_decrypt);
  return 0;
}

int __cdecl main(void) {
  printf("AES128 GCM tests\n");
  test_aesgctr();
  printf("AES128 GCM tests completed.\n");
}
