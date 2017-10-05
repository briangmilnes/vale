include "../../../../obj/crypto/aes/aes-x64/gcm.gen.dfy"
include "../../../arch/x64/print.s.dfy"
include "../../../lib/util/Io.s.dfy"

module GCMMain {

import opened GCM
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
    var win := (platform_choice == Win);

    // Allow C to call the key expansion.

     printProcPlatform("aes_main_i_KeyExpansionStdcall",
         va_code_KeyExpansionStdcall(Secret, win),
         0, 8,
        asm_choice, platform_choice);

/*
    printProcPlatform("Test",
         va_code_Test(),
         0, 0,
        asm_choice, platform_choice);
*/

/*
    printProcPlatform("AES128GCTREncryptStdcall",
        va_code_AES128GCTREncryptStdcall(),
        10, 2, asm_choice, platform_choice);
*/

    printProcPlatform("AES128GCTREncryptStdcall1",
        va_code_AES128GCTREncryptStdcall1(),
        10, 0, asm_choice, platform_choice);

    printProcPlatform("AES128GCTRDecryptStdcall1",
        va_code_AES128GCTREncryptStdcall1(),
        20, 0, asm_choice, platform_choice);


//    printProcPlatform("AES128EncryptOneBlockOp",
//        va_code_AES128EncryptOneBlockOp(Secret, xmm0, xmm1, exp_key_ptr),
//        90, 4, asm_choice, platform_choice);

/*
    printProcPlatform("AES128GCTREncryptStdcall2",
        va_code_AES128GCTREncryptStdcall2(),
        20, 2, asm_choice, platform_choice);

    printProcPlatform("AES128GCTREncryptStdcall3",
        va_code_AES128GCTREncryptStdcall3(),
        30, 2, asm_choice, platform_choice);

    printProcPlatform("AES128GCTREncryptStdcall4",
        va_code_AES128GCTREncryptStdcall4(),
        40, 2, asm_choice, platform_choice);

    printProcPlatform("AES128GCTREncryptStdcall5",
        va_code_AES128GCTREncryptStdcall5(),
        50, 2, asm_choice, platform_choice);

    printProcPlatform("AES128GCTREncryptStdcall6",
        va_code_AES128GCTREncryptStdcall6(),
        60, 2, asm_choice, platform_choice);

    printProcPlatform("AES128GCTREncryptStdcall7",
        va_code_AES128GCTREncryptStdcall7(),
        70, 2, asm_choice, platform_choice);

    printProcPlatform("AES128GCTREncryptStdcall8",
        va_code_AES128GCTREncryptStdcall8(),
        80, 2, asm_choice, platform_choice);
*/
/*
    printProcPlatform("AES128GCTRDecryptStdcall",
        va_code_AES128GCTRDecryptStdcall(),
        100, 2, asm_choice, platform_choice);
*/
 	  printFooter(asm_choice);
 }

}
