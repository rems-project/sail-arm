/******************************************************************************/
/*  BSD 3-clause Clear License                                                */
/*                                                                            */
/*  Copyright (c) 2023                                                        */
/*    Arm Limited (or its affiliates),                                        */
/*    Thomas Bauereiss,                                                       */
/*    Brian Campbell,                                                         */
/*    Alasdair Armstrong,                                                     */
/*    Alastair Reid,                                                          */
/*    Peter Sewell                                                            */
/*                                                                            */
/*  All rights reserved.                                                      */
/*                                                                            */
/*  Redistribution and use in source and binary forms, with or without        */
/*  modification, are permitted (subject to the limitations in the            */
/*  disclaimer below) provided that the following conditions are met:         */
/*                                                                            */
/*    * Redistributions of source code must retain the above copyright        */
/*      notice, this list of conditions and the following disclaimer.         */
/*    * Redistributions in binary form must reproduce the above copyright     */
/*      notice, this list of conditions and the following disclaimer in the   */
/*      documentation and/or other materials provided with the distribution.  */
/*    * Neither the name of ARM Limited nor the names of its contributors     */
/*      may be used to endorse or promote products derived from this          */
/*      software without specific prior written permission.                   */
/*                                                                            */
/*  NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE GRANTED   */
/*  BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND   */
/*  CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,    */
/*  BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND         */
/*  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE   */
/*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT  */
/*  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON    */
/*  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT   */
/*  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF  */
/*  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.         */
/******************************************************************************/

val ImpDefBool : string -> bool

function ImpDefBool x = {
    if x == "the PE resets into EL2 or EL3" then {
        return(EL2 == HighestEL() | EL3 == HighestEL())
    } else if x == "the PE resets into EL1" then {
        return(EL1 == HighestEL())
    } else if x == "the PE resets into EL2" then {
        return(EL2 == HighestEL())
    } else if x == "the PE resets into EL3" then {
        return(EL3 == HighestEL())
    } else if x == "IMPLEMENTED_ITD" then {
        return(true)
    } else if x == "IMPLEMENTED_CP15BEN" then {
        return(true)
    } else if x == "in a system that supports only a single Security state" then {
        return(false)
    } else if x == "access is Secure, in a system that supports two Security states" then {
        return(false)
    } else if x == "GICD_CTLR.DS==0, Secure access" then {
        return(false)
    } else if x == "Has FP16 extension" then {
        return(FEAT_FP16_IMPLEMENTED)
    } else if x == "Edge-triggered SError" then {
        return(false)
    } else if x == "AMEVCNTR1[m] is fixed" then {
        return(false)
    } else if x == "AMEVCNTR1_EL0[m] is fixed" then {
        return(false)
    } else if x == "Has LRCPC3 support" then {
        return(true)
    } else if x == "accessed from EL0" then {
        return(PSTATE.EL == EL0)
    } else if x == "Highest EL using AArch64" then {
        return(not_bool(__highest_el_aarch32))
    } else if x == "PE can reset into AArch64 state" then {
        return(true)
    } else if x == "PE can reset into AArch32 state" then {
        return(true)
    } else if x == "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ" then {
        return(false)
    } else if x == "System register access to the PE Trace Unit registers is implemented" then {
        return(true)
    } else if x == "AArch32 floating-point is implemented" then {
        return(true)
    } else if x == "the implementation includes a PMU event export bus" then {
        return(false)
    } else if x == "Edge-triggered SError" then {
        return(true)
    } else if x == "Support trapping of floating-point exceptions" then {
        return(true)
    } else if x == "IMPLEMENTED_trapping of floating-point exceptions" then {
        return(true)
    } else if x == "Has 16-bit VMID" then {
        return(FEAT_VMID16_IMPLEMENTED)
    } else if x == "DC_ZVA tag fault reported with lowest faulting address" then {
        return(true)
    } else if x == "When PoC is before any level of cache, data cache maintenance operations are NOP" then {
        return(false)
    } else if x == "DCIMVAC generates watchpoint" then {
        return(false)
    } else if x == "Trapped by MDCR_EL2.TDOSA" then {
        return(true)
    } else if x == "Trapped by MDCR_EL3.TDOSA" then {
        return(true)
    } else if x == "Trapped by HDCR.TDOSA" then {
        return(true)
    } else if x == "EL3 trap priority when SDD == '1'" then {
        return(false)
    } else if x == "Address Size Fault on LPA descriptor bits [15:12]" then {
        return(true)
    } else if x == "ID_MMFR5_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "ID_MMFR5 trapped by HCR.TID3" then {
        return(true)
    } else if x == "ID_MMFR5 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "Has Trace Architecture functionality" then {
        return(true)
    } else if x == "Reserved Control Space Supported" then {
        return(true)
    } else if x == "Reserved Control Space Traps Supported" then {
        return(true)
    } else if x == "Reserved Control Space EL0 Trapped" then {
        return(true)
    } else if x == "Illegal Execution State on return to AArch32" then {
        return(true)
    } else if x == "Floating-Point Traps Information" then {
        return(true)
    } else if x == "Condition valid for trapped T32" then {
        return(false)
    } else if x == "Translation fault on misprogrammed contiguous bit" then {
        return(false)
    } else if x == "Virtual SError syndrome valid" then {
        return(false)
    } else if x == "Have CRC extension" then {
        return(true)
    } else if x == "Report I-cache maintenance fault in IFSR" then {
        return(true)
    } else if x == "Permission fault on EL0 IC_IVAU execution" then {
        return(false)
    } else if x == "UNDEF unallocated CP15 access at EL0" then {
        return(true)
    } else if x == "Align PC on illegal exception return" then {
        return(true)
    } else if x == "EL from SPSR on illegal exception return" then {
        return(false)
    } else if x == "Has SHA1 Crypto instructions" then {
        return(FEAT_SHA1_IMPLEMENTED)
    } else if x == "Has SHA256 Crypto instructions" then {
        return(FEAT_SHA256_IMPLEMENTED)
    } else if x == "Has 128-bit form of PMULL instructions" then {
        return(FEAT_AES_IMPLEMENTED & FEAT_PMULL_IMPLEMENTED)
    } else if x == "vector instructions set TFV to 1" then {
        return(true)
    } else if x == "JOSCR UNDEFINED at EL0" then {
        return(true)
    } else if x == "JMCR UNDEFINED at EL0" then {
        return(true)
    } else if x == "JIDR UNDEFINED at EL0" then {
        return(true)
    } else if x == "Has accumulate FP16 product into FP32 extension" then {
        return(true)
    } else if x == "Has Dot Product extension" then {
        return(true)
    } else if x == "Has SHA512 Crypto instructions" then {
        return(FEAT_SHA512_IMPLEMENTED)
    } else if x == "Has SHA3 Crypto instructions" then {
        return(FEAT_SHA3_IMPLEMENTED)
    } else if x == "Has SM3 Crypto instructions" then {
        return(FEAT_SM3_IMPLEMENTED)
    } else if x == "Has SM4 Crypto instructions" then {
        return(FEAT_SM4_IMPLEMENTED)
    } else if x == "CPY* instructions use Option A" then {
        return(__cpy_mops_option_a_supported)
    } else if x == "CPYF* instructions use Option A" then {
        return(__cpyf_mops_option_a_supported)
    } else if x == "SET* instructions use Option A" then {
        return(__set_mops_option_a_supported)
    } else if x == "SETG* instructions use Option A" then {
        return(__setg_mops_option_a_supported)
    } else if x == "Has PMUv3 threshold extension" then {
        return(FEAT_PMUv3_TH_IMPLEMENTED)
    } else if x == "Has PMUv3 fixed-function instruction counter" then {
        return(true)
    } else if x == "Has Flag manipulate extension" then {
        return(false)
    } else if x == "Has Nested Virtualization" then {
        return(FEAT_NV_IMPLEMENTED)
    } else if x == "Has support for Enhanced Nested Virtualization" then {
        return(FEAT_NV2_IMPLEMENTED)
    } else if x == "BBM level 1 or 2 support nT bit causes Translation Fault" then {
        return(true)
    } else if x == "Apply effective shareability at stage 1" then {
        return(__apply_effective_shareability)
    } else if x == "Has MPAM extension" then {
        return(FEAT_MPAM_IMPLEMENTED)
    } else if x == "Has enhanced MPAMv0p1 extension" then {
        return(__mpam_major == 0b0000 & __mpam_frac == 0b0001)
    } else if x == "Has enhanced MPAMv1p1 extension" then {
        return(__mpam_major == 0b0001 & __mpam_frac == 0b0001)
    } else if x == "Has EMPAM SDEFLT" then {
        return(__empam_sdeflt_implemented)
    } else if x == "Has EMPAM FORCE_NS" then {
        return(__empam_force_ns_implemented)
    } else if x == "EMPAM FORCE_NS is RAO" then {
        return(__empam_force_ns_RAO)
    } else if x == "Has EMPAM TIDR" then {
        return(__empam_tidr_implemented)
    } else if x == "Has AArch32 hierarchical permission disables" then {
        return(FEAT_AA32HPD_IMPLEMENTED)
    } else if x == "Has enhanced PAC functionality" then {
        return(FEAT_EPAC_IMPLEMENTED)
    } else if x == "Has enhanced PAC 2 functionality" then {
        return(true)
    } else if x == "Has FPAC functionality" then {
        return(true)
    } else if x == "Has FPAC Combined functionality" then {
        return(true)
    } else if x == "Has MTE extension" then {
        return(UInt(__mte_implemented) == UInt(0b0001))
    } else if x == "Has MTE2 extension" then {
        return(UInt(__mte_implemented) == UInt(0b0010))
    } else if x == "Has MTE Asynchronous Faulting extension" then {
        return(FEAT_MTE4_IMPLEMENTED)
    } else if x == "Has Store-only Tag Checking support" then {
        return(FEAT_MTE_STORE_ONLY_IMPLEMENTED)
    } else if x == "Has CLRBHB instruction" then {
        return(FEAT_CLRBHB_IMPLEMENTED)
    } else if x == "SPE PAT for tag unchecked access zero" then {
        return(true)
    } else if x == "SPE non-tbi tag is zero" then {
        return(true)
    } else if x == "Has AArch64 DGH extension" then {
        return(true)
    } else if x == "Has Performance Monitors extension" then {
        return(true)
    } else if x == "Has RNG extension" then {
        return(FEAT_RNG_IMPLEMENTED)
    } else if x == "Has Small Translation Table extension" then {
        return(true)
    } else if x == "Secure-only implementation" then {
        return(true)
    } else if x == "Non-secure only implementation" then {
        return(false)
    } else if x == "OS Double Lock is implemented" then {
        return(false)
    } else if x == "Have Common Short Sequence Compression instructions extension" then {
        return(true)
    } else if x == "Have SVE ISA" then {
        return(true)
    } else if x == "Have SVE FP32 Matrix Multiply extension" then {
        return(true)
    } else if x == "Have SVE FP64 Matrix Multiply extension" then {
        return(true)
    } else if x == "Have SVE2 AES extension" then {
        return(true)
    } else if x == "Have SVE2 128 bit PMULL extension" then {
        return(true)
    } else if x == "Have SVE2 SHA3 extension" then {
        return(true)
    } else if x == "Have SVE2 SHA256 extension" then {
        return(true)
    } else if x == "Have SVE2 SHA512 extension" then {
        return(true)
    } else if x == "Have SVE2 SM4 extension" then {
        return(true)
    } else if x == "Have SVE2 SM3 extension" then {
        return(true)
    } else if x == "Have SVE2GF  extension" then {
        return(true)
    } else if x == "Have SVE2.1 extension" then {
        return(true)
    } else if x == "Have SME extension" then {
        return(FEAT_SME_IMPLEMENTED)
    } else if x == "SME only" then {
        return(__sme_only)
    } else if x == "Has SME priority control" then {
        return(__has_sme_priority_control)
    } else if x == "Have SME FA64 extension" then {
        return(FEAT_SME_FA64_IMPLEMENTED)
    } else if x == "No tag checking of SME LDR & STR instructions" then {
        return(false)
    } else if x == "Shared SMCU" then {
        return(true)
    } else if x == "MPAMSM_EL1 label precedence" then {
        return(true)
    } else if x == "Have EBF16 extension" then {
        return(true)
    } else if x == "Have SME2 extension" then {
        return(true)
    } else if x == "Have SME2.1 extension" then {
        return(true)
    } else if x == "Have SME2.1 half-precision floating-point instructions" then {
        return(true)
    } else if x == "Have non-widening BFloat16 instructions" then {
        return(true)
    } else if x == "Has Transactional Memory extension" then {
        return(true)
    } else if x == "Memory Region does not support Transactional access" then {
        return(false)
    } else if x == "Has AArch64 BFloat16 extension" then {
        return(true)
    } else if x == "Has TWED extension" then {
        return(true)
    } else if x == "Has AArch32 BFloat16 extension" then {
        return(true)
    } else if x == "Has AArch64 Int8 Mat Mul extension" then {
        return(true)
    } else if x == "Has AArch32 Int8 Mat Mul extension" then {
        return(true)
    } else if x == "ID_MMFR4_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "ID_ISAR6_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "ID_AA64MMFR4_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "ID_AA64SMFR0_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "Has Branch Record Buffer Extension" then {
        return(FEAT_BRBE_IMPLEMENTED)
    } else if x == "ISB generates Branch records" then {
        return(__isb_is_branch)
    } else if x == "Has BRBEv1p1 extension" then {
        return(FEAT_BRBEv1p1_IMPLEMENTED)
    } else if x == "ID_AA64ZFR0_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "ID_DFR1_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "ID_DFR1 trapped by HCR.TID3" then {
        return(true)
    } else if x == "ID_PFR2_EL1 trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "Unallocated encodings trapped by HCR_EL2.TID3" then {
        return(true)
    } else if x == "Report abort using Long-descriptor format" then {
        return(true)
    } else if x == "Fault on TxSZ value above maximum" then {
        return(false)
    } else if x == "Fault on TxSZ value below minimum" then {
        return(false)
    } else if x == "Has 52-bit IPA and PA support" then {
        return(FEAT_LPA2_IMPLEMENTED)
    } else if x == "Has 56-bit PA support" then {
        return(FEAT_D128_IMPLEMENTED)
    } else if x == "Has 56-bit VA support" then {
        return(FEAT_LVA3_IMPLEMENTED)
    } else if x == "Has 128-bit Descriptor support" then {
        return(FEAT_D128_IMPLEMENTED)
    } else if x == "Has S1 Permission Indirection support" then {
        return(FEAT_S1PIE_IMPLEMENTED)
    } else if x == "Has S1 Permission Overlay support" then {
        return(FEAT_S1POE_IMPLEMENTED)
    } else if x == "Has S2 Permission Indirection support" then {
        return(FEAT_S2PIE_IMPLEMENTED)
    } else if x == "Has S2 Permission Overlay support" then {
        return(FEAT_S2POE_IMPLEMENTED)
    } else if x == "Has Translation Hardening Extension" then {
        return(FEAT_THE_IMPLEMENTED)
    } else if x == "Has LSE128" then {
        return(FEAT_LSE128_IMPLEMENTED)
    } else if x == "Has SysReg128" then {
        return(FEAT_SYSREG128_IMPLEMENTED)
    } else if x == "Has SysInstr128" then {
        return(FEAT_SYSINSTR128_IMPLEMENTED)
    } else if x == "Arch has TCR2" then {
        return(FEAT_TCR2_IMPLEMENTED)
    } else if x == "Arch has SCTLR2" then {
        return(FEAT_SCTLR2_IMPLEMENTED)
    } else if x == "Has 4K Translation Granule" then {
        return(true)
    } else if x == "Has 16K Translation Granule" then {
        return(true)
    } else if x == "Has 64K Translation Granule" then {
        return(true)
    } else if x == "Has Stage 2 4K Translation Granule" then {
        return(true)
    } else if x == "Has Stage 2 16K Translation Granule" then {
        return(true)
    } else if x == "Has Stage 2 64K Translation Granule" then {
        return(true)
    } else if x == "Has PAN3 extension" then {
        return(FEAT_PAN3_IMPLEMENTED)
    } else if x == "SCR_EL3.SIF affects EPAN" then {
        return(false)
    } else if x == "Has MTE3 extension" then {
        return(FEAT_MTE3_IMPLEMENTED)
    } else if x == "Has MTE Asymmetric Faults extension" then {
        return(FEAT_MTE4_IMPLEMENTED)
    } else if x == "Has MTE tag access permission extension" then {
        return(FEAT_MTE_PERM_IMPLEMENTED)
    } else if x == "Has Load Store 64-Byte instruction support" then {
        return(true)
    } else if x == "Memory location supports ST64B and LD64B" then {
        return(FEAT_LS64_IMPLEMENTED)
    } else if x == "Has Store 64-Byte with return instruction support" then {
        return(FEAT_LS64_V_IMPLEMENTED)
    } else if x == "Has Store 64-Byte EL0 with return instruction support" then {
        return(FEAT_LS64_ACCDATA_IMPLEMENTED)
    } else if x == "Has increased Reciprocal Estimate and Square Root Estimate precision support" then {
        return(__feat_rpres)
    } else if x == "Has SPEv1p1 extension" then {
        return(true)
    } else if x == "SPE SyncExternal as SError" then {
        return(false)
    } else if x == "SPE async External abort" then {
        return(false)
    } else if x == "Has Implicit Error Synchronization Barrier before Exception" then {
        return(false)
    } else if x == "SPE TTW fault External abort" then {
        return(true)
    } else if x == "Has SPEv1p2 extension" then {
        return(true)
    } else if x == "event [x] is not implemented, or filtering on event [x] is not supported" then {
        return(false)
    } else if x == "event 63 is not implemented, or filtering on event 63 is not supported" then {
        return(false)
    } else if x == "event 62 is not implemented, or filtering on event 62 is not supported" then {
        return(false)
    } else if x == "event 61 is not implemented, or filtering on event 61 is not supported" then {
        return(false)
    } else if x == "event 60 is not implemented, or filtering on event 60 is not supported" then {
        return(false)
    } else if x == "event 59 is not implemented, or filtering on event 59 is not supported" then {
        return(false)
    } else if x == "event 58 is not implemented, or filtering on event 58 is not supported" then {
        return(false)
    } else if x == "event 57 is not implemented, or filtering on event 57 is not supported" then {
        return(false)
    } else if x == "event 56 is not implemented, or filtering on event 56 is not supported" then {
        return(false)
    } else if x == "event 55 is not implemented, or filtering on event 55 is not supported" then {
        return(false)
    } else if x == "event 54 is not implemented, or filtering on event 54 is not supported" then {
        return(false)
    } else if x == "event 53 is not implemented, or filtering on event 53 is not supported" then {
        return(false)
    } else if x == "event 52 is not implemented, or filtering on event 52 is not supported" then {
        return(false)
    } else if x == "event 51 is not implemented, or filtering on event 51 is not supported" then {
        return(false)
    } else if x == "event 50 is not implemented, or filtering on event 50 is not supported" then {
        return(false)
    } else if x == "event 49 is not implemented, or filtering on event 49 is not supported" then {
        return(false)
    } else if x == "event 48 is not implemented, or filtering on event 48 is not supported" then {
        return(false)
    } else if x == "event 31 is not implemented, or filtering on event 31 is not supported" then {
        return(false)
    } else if x == "event 30 is not implemented, or filtering on event 30 is not supported" then {
        return(false)
    } else if x == "event 29 is not implemented, or filtering on event 29 is not supported" then {
        return(false)
    } else if x == "event 28 is not implemented, or filtering on event 28 is not supported" then {
        return(false)
    } else if x == "event 27 is not implemented, or filtering on event 27 is not supported" then {
        return(false)
    } else if x == "event 26 is not implemented, or filtering on event 26 is not supported" then {
        return(false)
    } else if x == "event 25 is not implemented, or filtering on event 25 is not supported" then {
        return(false)
    } else if x == "event 24 is not implemented, or filtering on event 24 is not supported" then {
        return(false)
    } else if x == "event 23 is not implemented, or filtering on event 23 is not supported" then {
        return(false)
    } else if x == "event 22 is not implemented, or filtering on event 22 is not supported" then {
        return(false)
    } else if x == "event 21 is not implemented, or filtering on event 21 is not supported" then {
        return(false)
    } else if x == "event 20 is not implemented, or filtering on event 20 is not supported" then {
        return(false)
    } else if x == "event 19 is not implemented, or filtering on event 19 is not supported" then {
        return(false)
    } else if x == "event 18 is not implemented, or filtering on event 18 is not supported" then {
        return(false)
    } else if x == "event 17 is not implemented, or filtering on event 17 is not supported" then {
        return(false)
    } else if x == "event 16 is not implemented, or filtering on event 16 is not supported" then {
        return(false)
    } else if x == "event 15 is not implemented, or filtering on event 15 is not supported" then {
        return(false)
    } else if x == "event 14 is not implemented, or filtering on event 14 is not supported" then {
        return(false)
    } else if x == "event 13 is not implemented, or filtering on event 13 is not supported" then {
        return(false)
    } else if x == "event 12 is not implemented, or filtering on event 12 is not supported" then {
        return(false)
    } else if x == "SPE get prev br if not br" then {
        return(false)
    } else if x == "SPE prev br on eret" then {
        return(false)
    } else if x == "SPE prev br on isb" then {
        return(false)
    } else if x == "SPE prev br on exception" then {
        return(false)
    } else if x == "SPE 16bit counters" then {
        return(HaveStatisticalProfilingv1p2())
    } else if x == "filtering on event 2 is optionally supported" then {
        return(true)
    } else if x == "filtering on event 4 is optionally supported" then {
        return(true)
    } else if x == "filtering on event 8 is optionally supported" then {
        return(true)
    } else if x == "filtering on event 9 is optionally supported" then {
        return(true)
    } else if x == "filtering on event 10 is optionally supported" then {
        return(true)
    } else if x == "event 8 is implemented" then {
        return(true)
    } else if x == "event 9 is implemented" then {
        return(true)
    } else if x == "event 10 is implemented" then {
        return(true)
    } else if x == "event 19 is implemented" then {
        return(true)
    } else if x == "event 20 is implemented" then {
        return(true)
    } else if x == "event 21 is implemented" then {
        return(true)
    } else if x == "event 22 is implemented" then {
        return(true)
    } else if x == "event 23 is implemented" then {
        return(true)
    } else if x == "Has SPEv1p4 extension" then {
        return(true)
    } else if x == "Has SPE_FDS extension" then {
        return(true)
    } else if x == "Has RME extension" then {
        return(FEAT_RME_IMPLEMENTED)
    } else if x == "GPC Fault on DC operations" then {
        return(true)
    } else if x == "Realm EL2&0 regime affects EPAN" then {
        return(false)
    } else if x == "Has feature WFxT" then {
        return(FEAT_WFxT_IMPLEMENTED)
    } else if x == "Has large 52-bit PA/IPA support" then {
        return(true)
    } else if x == "Has Enhanced Counter Virtualization extension" then {
        return(true)
    } else if x == "Has large 52-bit VA support" then {
        return(true)
    } else if x == "the PE supports sampling of speculative instructions" then {
        return(true)
    } else if x == "Debug has Software Lock" then {
        return(not_bool(HasArchVersion(v8Ap4)))
    } else if x == "External abort signaled in-band synchronously" then {
        return(true)
    } else if x == "PMU has Software Lock" then {
        return(false)
    } else if x == "CTI has Software Lock" then {
        return(false)
    } else if x == "Has PAC QARMA3 functionality" then {
        return(FEAT_PACQARMA3_IMPLEMENTED)
    } else if x == "Has PAC QARMA5 functionality" then {
        return(FEAT_PACQARMA5_IMPLEMENTED)
    } else if x == "Has PAC IMP functionality" then {
        return(not_bool(FEAT_PACQARMA3_IMPLEMENTED | FEAT_PACQARMA5_IMPLEMENTED))
    } else if x == "Has PAC QARMA3 Auth functionality" then {
        return(FEAT_PACQARMA3_IMPLEMENTED)
    } else if x == "Has PAC QARMA3 Generic functionality" then {
        return(FEAT_PACQARMA3_IMPLEMENTED)
    } else if x == "Has PAC QARMA5 Auth functionality" then {
        return(FEAT_PACQARMA5_IMPLEMENTED)
    } else if x == "Has PAC QARMA5 Generic functionality" then {
        return(FEAT_PACQARMA5_IMPLEMENTED)
    } else if x == "Has PAC IMPDEF Auth functionality" then {
        return(FEAT_PACIMP_IMPLEMENTED)
    } else if x == "Has PAC IMPDEF Generic functionality" then {
        return(FEAT_PACIMP_IMPLEMENTED)
    } else if x == "Bit 55 determines the size of the PAC field" then {
        return(FEAT_CONSTPACFIELD_IMPLEMENTED)
    } else if x == "FEAT_LSE2: access is atomic" then {
        return(false)
    } else if x == "Has Generic Counter Scaling support" then {
        return(FEAT_CNTSC_IMPLEMENTED)
    } else if x == "No tag checking of SIMD&FP loads and stores in Streaming SVE mode" then {
        return(false)
    } else if x == "No tag checking of ZA loads and stores" then {
        return(false)
    } else if x == "Has MTE4 extension" then {
        return(FEAT_MTE4_IMPLEMENTED)
    } else if x == "Has Canonical Tag Checking support" then {
        return(FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED)
    } else if x == "G1 activity monitor is implemented for counter 0" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 1" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 2" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 3" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 4" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 5" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 6" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 7" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 8" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 9" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 10" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 11" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 12" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 13" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 14" then {
        return(true)
    } else if x == "G1 activity monitor is implemented for counter 15" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 0" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 1" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 2" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 3" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 4" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 5" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 6" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 7" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 8" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 9" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 10" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 11" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 12" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 13" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 14" then {
        return(true)
    } else if x == "G1 activity monitor offset is implemented for counter 15" then {
        return(true)
    } else if x == "No fault generated for DC operations if PoC is before any level of cache" then {
        return(false)
    } else if x == "No fault generated for DC operations if PoU is before any level of cache" then {
        return(false)
    } else if x == "Generate access flag fault on IC/DC operations" then {
        return(true)
    } else if x == "Generate translation fault on IC operations" then {
        return(true)
    } else if x == "Generate access flag fault on IC operations" then {
        return(true)
    } else if x == "Generate address size fault on IC operations" then {
        return(true)
    } else if x == "IC_IVAU generates Permission fault at EL0 without read permission" then {
        return(true)
    } else if x == "Instruction Cache needs translation" then {
        return(true)
    } else if x == "reset into AArch32" then {
        return(false)
    } else if x == "Memory system does not supports PoP" then {
        return(false)
    } else if x == "Memory system does not supports PoDP" then {
        return(false)
    } else if x == "Arch has AIE" then {
        return(true)
    } else if x == "read" then {
        return(true)
    } else if x == "written" then {
        return(true)
    } else if x == "PFAR_ELx is valid" then {
        return(true)
    } else if x == "Apply granule protection check on DC to PoE" then {
        return(false)
    } else if x == "IMPLEMENTED_trapping of Input Denormal floating-point exceptions" then {
        return(true)
    } else if x == "IMPLEMENTED_trapping of Inexact floating-point exceptions" then {
        return(true)
    } else if x == "IMPLEMENTED_trapping of Underflow floating-point exceptions" then {
        return(true)
    } else if x == "IMPLEMENTED_trapping of Overflow floating-point exceptions" then {
        return(true)
    } else if x == "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions" then {
        return(true)
    } else if x == "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions" then {
        return(true)
    } else {
        println((x ++ "is an unrecognized IMPLEMENTATION_DEFINED boolean"));
        assert(false);
        return(undefined : bool)
    }
}

function __IMPDEF_boolean x = {
    return(ImpDefBool(x))
}

val ImpDefInt : string -> int

function ImpDefInt x = {
    if x == "Number of breakpoints" then {
        return(getNumBreakpoints())
    } else if x == "Number of watchpoints" then {
        return(getNumWatchpoints())
    } else if x == "Number of event counters" then {
        return(NUM_PMU_COUNTERS)
    } else if x == "Number of context-aware breakpoints" then {
        return(getNumCtxBreakpoints())
    } else if x == "Max implemented VL" then {
        return(__max_implemented_sveveclen)
    } else if x == "Maximum bytes used in a single block of a copy" then {
        return(1)
    } else if x == "Number of BRB records" then {
        return(NUM_BRBE_RECORDS)
    } else if x == "SPE Events packet payload size" then {
        return(4)
    } else if x == "SPE Data Source packet payload size" then {
        return(2)
    } else if x == "Reserved Intermediate Physical Address size value" then {
        return(52)
    } else if x == "Maximum Physical Address Size" then {
        return(__supported_pa_size)
    } else if x == "Block BBM support level" then {
        return(__block_bbm_implemented)
    } else if x == "SVE Extended BFloat16 instructions are implemented" then {
        return(__has_sve_extended_bf16)
    } else if x == "Max implemented SVL" then {
        return(__max_implemented_smeveclen)
    } else if x == "Data Cache Invalidate Watchpoint Size" then {
        return(4 * pow2(UInt(CTR_EL0[DminLine])))
    } else if x == "Instruction Cache Invalidate by VA Size" then {
        return(4 * pow2(UInt(CTR_EL0[DminLine])))
    } else if x == "Linesize for DC SW instructions" then {
        return(4 * pow2(UInt(CTR_EL0[DminLine])))
    } else if x == "Associativity for DC SW instructions" then {
        return(2)
    } else if x == "Numsets for DC SW instructions" then {
        return(2)
    } else {
        println((x ++ " is an unrecognized Implementation defined bit."));
        assert(false);
        return(undefined : int)
    }
}

function __IMPDEF_integer x = {
    return(ImpDefInt(x))
}

val ImpDefBits : forall 'N, 'N >= 0. (string, int('N)) -> bits('N)

function ImpDefBits (x, N) = {
    if x == "Coresight timestamp" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 64)));
        return(PhysicalCountInt()[N - 1 .. 0])
    } else if x == "Synchronous Error" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
        return(0b00[N - 1 .. 0])
    } else if x == "Asynchronous Error" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
        return(0b11[N - 1 .. 0])
    } else if x == "Virtual Asynchronous Abort ExT bit" then {
        return(Zeros(N))
    } else if x == "FPEXC.EN value when TGE==1 and RW==0" then {
        assert(constraint(0 <= 'N - 1));
        return(1[N - 1 .. 0])
    } else if x == "reset vector address" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 64)));
        return(CFG_RVBAR[N - 1 .. 0])
    } else if x == "TG0 encoded granule size" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
        return(__impdef_TG0[N - 1 .. 0])
    } else if x == "TG1 encoded granule size" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
        return(__impdef_TG1[N - 1 .. 0])
    } else if x == "Reserved short descriptor AP encoding" then {
        assert(constraint(0 <= 'N - 1));
        return(UInt(0b101)[N - 1 .. 0])
    } else if x == "Non-Faulting PAR" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 1)));
        return(0b0[N - 1 .. 0])
    } else if x == "Faulting PAR" then {
        return(Zeros(N))
    } else if x == "SPE mask 10:8,4,2" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 5)));
        return(0b11111[N - 1 .. 0])
    } else if x == "MPAM version" then {
        assert(constraint(0 <= 'N - 1));
        return(UInt(__mpam_major)[N - 1 .. 0])
    } else if x == "MPAM maximum PARTID" then {
        assert(constraint(0 <= 'N - 1));
        return(UInt(__mpam_partid_max)[N - 1 .. 0])
    } else if x == "MPAM maximum PMG" then {
        assert(constraint(0 <= 'N - 1));
        return(UInt(__mpam_pmg_max)[N - 1 .. 0])
    } else if x == "Has MPAMHCR_EL2" then {
        return(if __mpam_has_hcr then {
            assert(constraint(0 <= 'N - 1));
            1[N - 1 .. 0]
        } else Zeros(N))
    } else if x == "MPAM maximum VPMR" then {
        assert(constraint(0 <= 'N - 1));
        return(UInt(__mpam_vpmr_max)[N - 1 .. 0])
    } else if x == "SPE mask 63:48" then {
        return(Zeros(N))
    } else if x == "SPE mask 31:24" then {
        return(Zeros(N))
    } else if x == "SPE mask 15:12" then {
        return(Zeros(N))
    } else if x == "SPE EVENTS 63_48" then {
        return(Zeros(N))
    } else if x == "SPE EVENTS 31_24" then {
        return(Zeros(N))
    } else if x == "SPE EVENTS 15_12" then {
        return(Zeros(N))
    } else if x == "Default Memory Map XNX bit" then {
        assert(constraint(0 <= 'N - 1));
        return(0[N - 1 .. 0])
    } else if x == "0" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 1)));
        return(0b0[N - 1 .. 0])
    } else if x == "1" then {
        assert(constraint((0 <= 'N - 1 & 'N - 1 < 1)));
        return(0b1[N - 1 .. 0])
    } else if x == "IMPDEF ErrorState" then {
        return(Zeros(N))
    } else if x == "Virtual External abort type" then {
        return(Zeros(N))
    } else if x == "Virtual SError syndrome" then {
        return(Zeros(N))
    } else {
        println((x ++ " is not among the strings in the above list."));
        assert(false);
        return(undefined : bits('N))
    }
}

function __IMPDEF_bits (N, x) = {
    return(ImpDefBits(x, N))
}

function HasArchVersion(version) = true
function HaveAArch32() = true
function HaveAArch32EL(el) = (el == EL0)
function HaveEL(el) = true
function HaveFP16Ext() = true

function MaxImplementedVL() = MAX_VL
function MaxImplementedSVL() = __max_implemented_smeveclen

register __exclusive_always_succeeds: bool = false

function ProcessorID() = 0
function IsExclusiveGlobal(paddress, processorid, size) = true
function IsExclusiveLocal(paddress, processorid, size) =
    if __exclusive_always_succeeds then true else undefined

function AArch64_IsExclusiveVA(address, processorid, size) = true
function AArch64_MarkExclusiveVA(address, processorid, size) = ()
function ExclusiveMonitorsStatus() = 0b0

function AArch64_SetLSInstructionSyndrome(size, sign_extend, Rt, sixty_four, acq_rel) = ()
function LSInstructionSyndrome() = Zeros()

// Default to no activity monitors
register __g1_activity_monitor_implemented : bits(16) = 0x0000

function IsG1ActivityMonitorImplemented i = {
    assert(0 <= i & i < 16);
    return __g1_activity_monitor_implemented[i] == bitone
}

register __g1_activity_monitor_offset_implemented : bits(16) = 0x0000

function IsG1ActivityMonitorOffsetImplemented i = {
    assert(0 <= i & i < 16);
    return __g1_activity_monitor_offset_implemented[i] == bitone
}

function DataMemoryBarrier (domain, types) = {
    sail_barrier(Barrier_DMB(struct { domain = domain, types = types, nXS = false }))
}

function DataSynchronizationBarrier (domain, types, nXS) = {
    sail_barrier(Barrier_DSB(struct { domain = domain, types = types, nXS = nXS }))
}

function InstructionSynchronizationBarrier () = {
    sail_barrier(Barrier_ISB())
}

function SpeculationBarrier () = {
    sail_barrier(Barrier_SB())
}

// TODO: make configurable
function SupportedPowerTwoSVL nbits = {
    true
}
