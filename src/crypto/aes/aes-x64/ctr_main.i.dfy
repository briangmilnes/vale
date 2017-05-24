include "../../../../obj/crypto/aes/aes-x64/ctr.gen.dfy"
include "../../../arch/x64/print.s.dfy"
include "../../../lib/util/Io.s.dfy"

module CTRMain {

import opened CTR
import opened x64_print_s
import opened Io_s

method {:main} Main(ghost env:HostEnvironment)
    requires env != null && allocated(env) && env.Valid();
    decreases *
{
    var argc := HostConstants.NumCommandLineArgs(env);
    if argc < 3 {
        print("Expected usage: ./[executable].exe [GCC|MASM] [Win|Linux|MacOS]\n");
        return;
    }

    var asm_choice_name := HostConstants.GetCommandLineArg(1, env);
    var platform_choice_name := HostConstants.GetCommandLineArg(2, env);
    var asm_choice;
    var platform_choice;

    if platform_choice_name[..] == "Win" {
        platform_choice := Win;
    } else if platform_choice_name[..] == "Linux" {
        platform_choice := Linux;
    } else if platform_choice_name[..] == "MacOS" {
        platform_choice := MacOS;
    } else {
        print("Please choose a correct assembler option: Win or Linux or MacOS\n");
        return;
    }

    if asm_choice_name[..] == "GCC" {
        asm_choice := GCC;
    } else if asm_choice_name[..] == "MASM" {
        asm_choice := MASM;
    } else {
        print("Please choose a correct assembler option: GCC or MASM\n");
        return;
    }

    printHeader(asm_choice );
    if asm_choice_name[..] == "MASM" {
        print(".XMM\n");
    }

    var win := (platform_choice == Win);

    // Make available the StdCall version for test from c. 

//    printProcPlatform("CTR128Increment64StdCall",
//       va_code_CTR128Increment64StdCall(),
//       0, 24,
//       asm_choice, platform_choice);
//
//    printProcPlatform("CTR128Increment128StdCall",
//       va_code_CTR128Increment128StdCall(),
//       0, 24,
//       asm_choice, platform_choice);
//
//    printProcPlatform("CTREncryptOneBlockStdCall",
//        va_code_CTREncryptOneBlockStdCall(),
//        0, 0, asm_choice, platform_choice);
//
      printProcPlatform("aes_main_i_KeyExpansionStdcall",
         va_code_KeyExpansionStdcall(Secret, win),
         0, 8,
        asm_choice, platform_choice);
// 
//    printProcPlatform("AES128EncryptOneBlockStdcall",
//        va_code_AES128EncryptOneBlockStdcall(win),
//        0, 0, asm_choice, platform_choice);

    printProcPlatform("CTR128EncryptStdcall",
        va_code_CTR128EncryptStdcall(),
        0, 0, asm_choice, platform_choice);

 	  printFooter(asm_choice);
}

}
