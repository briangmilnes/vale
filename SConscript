#
# Main file for building Vale source code, under the src\tree
#

# Python imports
import os, os.path
import sys

# Imported identifiers defined in the SConstruct file
Import('env', 'BuildOptions', 'dafny_default_args', 'dafny_default_args_nonlarith')

#
# Verify *.vad and *.dfy under src/test/ and tools/vale/test/
#
verify_paths = [
  'src/',
  'tools/Vale/test'
]
Export('verify_paths')

#
# Table of special-case Dafny source which requires non-default arguments
#
verify_options = {
  'src/arch/arm/nlarith.s.dfy': BuildOptions(dafny_default_args),
  'src/arch/arm/bitvectors.i.dfy': BuildOptions(dafny_default_args_nonlarith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'src/crypto/aes/aes-x64/aes_main.i.dfy': BuildOptions(dafny_default_args_nonlarith),
  'src/lib/math/mul_nonlinear.i.dfy': BuildOptions(dafny_default_args),
  'src/lib/math/div_nonlinear.i.dfy': BuildOptions(dafny_default_args),
  'src/crypto/hashing/sha-arm/bit-vector-lemmas.i.dfy': BuildOptions(dafny_default_args_nonlarith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'src/crypto/hashing/sha-x64/sha256_vale_main.i.dfy': BuildOptions(dafny_default_args_nonlarith),
  'src/lib/math/div.i.dfy': BuildOptions(dafny_default_args_nonlarith + ' /timeLimit:60'),
  'src/lib/util/operations.i.dfy': BuildOptions(dafny_default_args_nonlarith + ' /proverOpt:OPTIMIZE_FOR_BV=true'),
  'obj/crypto/aes/cbc.gen.dfy': BuildOptions(dafny_default_args_nonlarith + ' /timeLimit:120'),
  'obj/crypto/aes/aes-x64/cbc.gen.dfy': BuildOptions(dafny_default_args_nonlarith + ' /timeLimit:120'),
  'src/crypto/aes/dtestaes.dfy': None,
  'src/crypto/aes/dtestgcm.dfy': None,
  'obj/crypto/aes/aes-x64/ctr.gen.dfy': BuildOptions(dafny_default_args_nonlarith + ' /errorLimit:1'), # + ' /noVerify',
  'obj/crypto/loopunroll/loopunroll.gen.dfy': BuildOptions(dafny_default_args_nonlarith),
  'obj/crypto/loopunroll/seq.gen.dfy': BuildOptions(dafny_default_args_nonlarith),
  # .dfy files default to this set of options
  '.dfy': BuildOptions(dafny_default_args_nonlarith),

  'tools/Vale/test/vale-debug.vad': None,

  # .vad files default to this set of options when compiling .gen.dfy
  '.vad': BuildOptions(dafny_default_args_nonlarith)

  # Disable verification by adding 'filename': None
}
if env['TARGET_ARCH']!='x86':
 verify_options['src/test/memcpy.vad'] = None
 verify_options['src/test/stack-test.vad'] = None
 
Export('verify_options')

#
# build sha256-exe
#
sha_asm = env.ExtractValeCode(
  ['src/crypto/hashing/$SHA_ARCH_DIR/sha256.vad'],           # Vale source
  'src/crypto/hashing/$SHA_ARCH_DIR/sha256_vale_main.i.dfy', # Dafny main
  'sha256'                                                   # Base name for the ASM files and EXE
  )
sha_c_h = env.ExtractDafnyCode(['src/crypto/hashing/sha256_main.i.dfy'])
sha_include_dir = os.path.split(str(sha_c_h[0][1]))[0]
env.BuildTest(['src/crypto/hashing/testsha256.c', sha_asm[0], sha_c_h[0][0]], sha_include_dir, 'testsha256')

#
# build cbc-exe
#
if env['TARGET_ARCH']=='x86' or env['TARGET_ARCH']=='amd64':   # x86 and x64 only
  cbc_asm = env.ExtractValeCode(
    ['src/crypto/aes/$AES_ARCH_DIR/aes.vad', 'src/crypto/aes/$AES_ARCH_DIR/cbc.vad'], # Vale source
    'src/crypto/aes/$AES_ARCH_DIR/cbc_main.i.dfy',              # Dafny main
    'cbc'                                                       # Base name for the ASM files and EXE
    )
  env.BuildTest(['src/crypto/aes/testcbc.c', cbc_asm[0]], '', 'testcbc')
else:
  print('Not building AES-CBC for this target architecture')  

#
# build ctr-exe
#
if env['TARGET_ARCH']=='amd64':  
  ctr_asm = env.ExtractValeCode(
    ['src/crypto/aes/$AES_ARCH_DIR/aes.vad', 'src/crypto/aes/$AES_ARCH_DIR/ctr.vad'], # Vale source
     'src/crypto/aes/$AES_ARCH_DIR/ctr_main.i.dfy',              # Dafny main
     'ctr'                                                       # Base name for the ASM files and EXE
    )
  env.BuildTest(['src/crypto/aes/testctr.c', ctr_asm[0]], '', 'testctr')
else:
  print('Not building AES-CTR for this target architecture')  

#
# build loopunroll-exe
#
if env['TARGET_ARCH']=='amd64':  
  loopunroll_asm = env.ExtractValeCode(
    ['src/crypto/loopunroll/loopunroll.vad'], # Vale source
     'src/crypto/loopunroll/loopunroll_main.i.dfy',
     'loopunroll'            
    )
  env.BuildTest(['src/crypto/loopunroll/testloopunroll.c', loopunroll_asm[0]], '', 'testloopunroll')
else:
  print('Not building LOOPUNROLL for this target architecture')  

#
# build seq-exe
#
if env['TARGET_ARCH']=='amd64':  
  seq_asm = env.ExtractValeCode(
    ['src/crypto/loopunroll/seq.vad'], # Vale source
     'src/crypto/loopunroll/seq_main.i.dfy',
     'seq'
    )
  env.BuildTest(['src/crypto/loopunroll/testseq.c', seq_asm[0]], '', 'testseq')
else:
  print('Not building Seq for this target architecture')  

#
# build aes-exe
#
if env['TARGET_ARCH']=='x86' or env['TARGET_ARCH']=='amd64':   # x86 and x64 only
  aes_asm = env.ExtractValeCode(
    ['src/crypto/aes/$AES_ARCH_DIR/aes.vad'],        # Vale source
    'src/crypto/aes/$AES_ARCH_DIR/aes_main.i.dfy',   # Dafny main
    'aes'                                            # Base name for the ASM files and EXE
    )
  env.BuildTest(['src/crypto/aes/testaes.c', aes_asm[0]], 'src/crypto/aes', 'testaes')
  env.BuildDafnyTest(['src/crypto/aes/dtestaes.dfy'], dafny_default_args, 'dtestaes')
else:
  print('Not building AES for this target architecture')

#
# build poly1305
#
if env['TARGET_ARCH']=='amd64' and sys.platform == "win32":     # x64-only; not yet tested on Linux
  poly1305_asm = env.ExtractValeCode(
    ['src/thirdPartyPorts/OpenSSL/poly1305/x64/poly1305.vad'],  # Vale source
    'src/crypto/poly1305/x64/poly1305_main.i.dfy',              # Dafny main
    'poly1305'                                                  # Base name for the ASM files and EXE
    )
  env.BuildTest(['src/crypto/poly1305/testpoly1305.c', poly1305_asm[0]], 'src/crypto/poly1305', 'testpoly1305')
else:
  print('Not building Poly1305 for this target architecture')
 
if 'KREMLIN_HOME' in os.environ:
  kremlin_path = os.environ['KREMLIN_HOME']
else:
  kremlin_path = '#tools/Kremlin'

kremlib_path = kremlin_path + '/kremlib'

#
# Build the OpenSSL engine
#
if env['OPENSSL_PATH'] != None:
  engineenv = env.Clone()
  engineenv.Append(CPPPATH=[kremlib_path, '#obj/crypto/hashing', '$OPENSSL_PATH/include', '#src/lib/util'])
  cdeclenv = engineenv.Clone(CCFLAGS='/Ox /Zi /Gd /LD') # compile __cdecl so it can call OpenSSL code
  stdcallenv=engineenv.Clone(CCFLAGS='/Ox /Zi /Gz /LD') # compile __stdcall so it can call the Vale crypto code
  everest_sha256 = cdeclenv.Object('src/Crypto/hashing/EverestSha256.c')
  everest_glue = stdcallenv.Object('src/Crypto/hashing/EverestSHA256Glue.c')
  if env['TARGET_ARCH']=='x86':
    sha256_obj = engineenv.Object('obj/sha256_openssl', sha_c_h[0][0])
    cbc_obj = engineenv.Object('obj/cbc_openssl', cbc_asm[0])
    aes_obj = engineenv.Object('obj/aes_openssl', sha_asm[0])
    engine = engineenv.SharedLibrary(target='obj/EverestSha256.dll',
      source=[everest_sha256, everest_glue, sha256_obj, cbc_obj, aes_obj, '$OPENSSL_PATH/libcrypto.lib'])
  if env['TARGET_ARCH']=='amd64' and sys.platform == "win32":
    sha256_obj = engineenv.Object('obj/sha256_openssl', sha_c_h[0][0])
    sha256asm_obj = engineenv.Object('obj/sha256asm_openssl', sha_asm[0])
    poly1305_obj = engineenv.Object('obj/poly1305_openssl', poly1305_asm[0])
    engine = engineenv.SharedLibrary(target='obj/EverestSha256.dll',
      source=[everest_sha256, everest_glue, sha256_obj, sha256asm_obj, poly1305_obj, '$OPENSSL_PATH/libcrypto.lib'])

