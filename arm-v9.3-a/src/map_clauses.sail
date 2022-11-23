/******************************************************************************/
/*  BSD 3-clause Clear License                                                */
/*                                                                            */
/*  Copyright (c) 2022                                                        */
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

function __IMPDEF_bits_map ((N, x) if x == "Coresight timestamp") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 64)));
    return(PhysicalCountInt()[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Synchronous Error") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
    return(0b00[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Asynchronous Error") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
    return(0b11[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Virtual Asynchronous Abort ExT bit") = {
    assert(constraint('N >= 0));
    return(Zeros())
}
and __IMPDEF_bits_map ((N, x) if x == "FPEXC.EN value when TGE==1 and RW==0") = {
    assert(constraint(0 <= 'N - 1));
    return(1[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "reset vector address") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 64)));
    return(CFG_RVBAR[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Reserved TG0 encoding granule size") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
    return(__impdef_res_TG0[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Reserved TG1 encoding granule size") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 2)));
    return(__impdef_res_TG1[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Reserved short descriptor AP encoding") = {
    assert(constraint(0 <= 'N - 1));
    return(UInt(0b101)[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Non-Faulting PAR") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 1)));
    return(0b0[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Faulting PAR") = {
    assert(constraint('N >= 0));
    return(Zeros(N))
}
and __IMPDEF_bits_map ((N, x) if x == "MPAM version") = {
    assert(constraint(0 <= 'N - 1));
    return(UInt(CFG_ID_AA64PFR0_EL1_MPAM)[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "MPAM maximum PARTID") = {
    assert(constraint(0 <= 'N - 1));
    return(UInt(__mpam_partid_max)[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "MPAM maximum PMG") = {
    assert(constraint(0 <= 'N - 1));
    return(UInt(__mpam_pmg_max)[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "Has MPAMHCR_EL2") = {
    assert(constraint(0 <= 'N - 1));
    return(if __mpam_has_hcr then 1[N - 1 .. 0] else Zeros())
}
and __IMPDEF_bits_map ((N, x) if x == "MPAM maximum VPMR") = {
    assert(constraint(0 <= 'N - 1));
    return(UInt(__mpam_vpmr_max)[N - 1 .. 0])
}
and __IMPDEF_bits_map ((N, x) if x == "SPE mask 63:48") = {
    assert(constraint('N >= 0));
    return(Zeros())
}
and __IMPDEF_bits_map ((N, x) if x == "SPE mask 31:24") = {
    assert(constraint('N >= 0));
    return(Zeros())
}
and __IMPDEF_bits_map ((N, x) if x == "SPE mask 15:12") = {
    assert(constraint('N >= 0));
    return(Zeros())
}
and __IMPDEF_bits_map ((N, x) if x == "reset vector address") = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 64)));
    return(CFG_RVBAR[N - 1 .. 0])
}
and __IMPDEF_bits_map (N, x) = {
    throw(Error_ImplementationDefined("Unrecognized bits(N)"))
}

function __IMPDEF_boolean_map (x if x == "the PE resets into EL2 or EL3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "IMPLEMENTED_ITD") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "IMPLEMENTED_CP15BEN") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "in a system that supports only a single Security state") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "access is Secure, in a system that supports two Security states") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "GICD_CTLR.DS==0, Secure access") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR1[m] is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR1_EL0[m] is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR10_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR11_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR12_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR13_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR14_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR15_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR16_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR17_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR18_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR19_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR110_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR111_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR112_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR113_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR114_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR115_EL0 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR10 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR11 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR12 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR13 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR14 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR15 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR16 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR17 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR18 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR19 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR110 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR111 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR112 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR113 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR114 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "AMEVCNTR115 is fixed") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "accessed from EL0") = {
    return(PSTATE.EL == EL0)
}
and __IMPDEF_boolean_map (x if x == "Highest EL using AArch64") = {
    return(not_bool(__highest_el_aarch32))
}
and __IMPDEF_boolean_map (x if x == "PE can reset into AArch64 state") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "PE can reset into AArch32 state") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "AArch32 state is supported at at least EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "System register access to the PE Trace Unit registers is implemented") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "AArch32 floating-point is implemented") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "the implementation includes a PMU event export bus") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Edge-triggered SError") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Process floating-point exception") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has 16-bit VMID") = {
    return(__vmid16_implemented)
}
and __IMPDEF_boolean_map (x if x == "DC_ZVA tag fault reported with lowest faulting address") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "When PoC is before any level of cache, data cache maintenance operations are NOP") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "DCIMVAC generates watchpoint") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Trapped by MDCR_EL2.TDOSA") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Trapped by MDCR_EL3.TDOSA") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Trapped by HDCR.TDOSA") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "EL3 trap priority when SDD == '1'") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Address Size Fault on LPA descriptor bits [15:12]") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "ID_MMFR5_EL1 trapped by HCR_EL2.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "ID_MMFR5 trapped by HCR.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "ID_MMFR5 trapped by HCR_EL2.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Trace Architecture functionality") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Reserved Control Space Supported") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Reserved Control Space Traps Supported") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Reserved Control Space EL0 Trapped") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Illegal Execution State on return to AArch32") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Floating-Point Traps Support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Floating-Point Traps Information") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Condition valid for trapped T32") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Translation fault on misprogrammed contiguous bit") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Virtual SError syndrome valid") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Have CRC extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Report I-cache maintenance fault in IFSR") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Permission fault on EL0 IC_IVAU execution") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "UNDEF unallocated CP15 access at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Align PC on illegal exception return") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "EL from SPSR on illegal exception return") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has AES Crypto instructions") = {
    return(__crypto_aes_implemented == 1 | __crypto_aes_implemented == 2)
}
and __IMPDEF_boolean_map (x if x == "Has SHA1 Crypto instructions") = {
    return(__crypto_sha1_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SHA256 Crypto instructions") = {
    return(__crypto_sha256_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has 128-bit form of PMULL instructions") = {
    return(__crypto_aes_implemented == 2)
}
and __IMPDEF_boolean_map (x if x == "vector instructions set TFV to 1") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "JOSCR UNDEFINED at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "JMCR UNDEFINED at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "JIDR UNDEFINED at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has accumulate FP16 product into FP32 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has RAS extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Implicit Error Synchronization Barrier") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Implicit Error Synchronization Barrier before Exception") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Dot Product extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has SHA512 Crypto instructions") = {
    return(__crypto_sha512_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SHA3 Crypto instructions") = {
    return(__crypto_sha3_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SM3 Crypto instructions") = {
    return(__crypto_sm3_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SM4 Crypto instructions") = {
    return(__crypto_sm4_implemented)
}
and __IMPDEF_boolean_map (x if x == "CPY*/SET* instructions use Option A") = {
    return(__mops_option_a_supported)
}
and __IMPDEF_boolean_map (x if x == "Has PMUv3 threshold extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Flag manipulate extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has Nested Virtualization") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has support for Enhanced Nested Virtualization") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "BBM level 1 or 2 support nT bit causes Translation Fault") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Apply effective shareability at stage 1") = {
    return(__apply_effective_shareability)
}
and __IMPDEF_boolean_map (x if x == "Has MPAM extension") = {
    return(__mpam_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has enhanced MPAM extension") = {
    return(__empam_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has EMPAM SDEFLT") = {
    return(__empam_sdeflt_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has EMPAM FORCE_NS") = {
    return(__empam_force_ns_implemented)
}
and __IMPDEF_boolean_map (x if x == "EMPAM FORCE_NS is RAO") = {
    return(__empam_force_ns_RAO)
}
and __IMPDEF_boolean_map (x if x == "Has EMPAM TIDR") = {
    return(__empam_tidr_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has AArch32 hierarchical permission disables") = {
    return(__aa32_hpd_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has enhanced PAC functionality") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has enhanced PAC 2 functionality") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has FPAC functionality") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has FPAC Combined functionality") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has MTE extension") = {
    return(UInt(__mte_implemented) == UInt(0b0001))
}
and __IMPDEF_boolean_map (x if x == "Has MTE2 extension") = {
    return(UInt(__mte_implemented) == UInt(0b0010))
}
and __IMPDEF_boolean_map (x if x == "Has AArch64 DGH extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Performance Monitors extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has SB extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has DoPD extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has RNG extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has SSBS extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has Small Translation Table extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Secure-only implementation") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Non-secure only implementation") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "OS Double Lock is implemented") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Have SVE ISA") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE FP32 Matrix Multiply extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE FP64 Matrix Multiply extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 AES extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 128 bit PMULL extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 SHA3 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 SM4 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 BitPerm extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SME extension") = {
    return(__has_sme)
}
and __IMPDEF_boolean_map (x if x == "SME only") = {
    return(__sme_only)
}
and __IMPDEF_boolean_map (x if x == "Has SME priority control") = {
    return(__has_sme_priority_control)
}
and __IMPDEF_boolean_map (x if x == "Have SMEF64F64 extension") = {
    return(__has_sme_f64f64)
}
and __IMPDEF_boolean_map (x if x == "Have SMEI16I64 extension") = {
    return(__has_sme_i16i64)
}
and __IMPDEF_boolean_map (x if x == "Have SME FA64 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Shared SMCU") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "MPAMSM_EL1 label precedence") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have EBF16 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Transactional Memory extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Memory Region does not support Transactional access") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has AArch64 BFloat16 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has TWED extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has AArch32 BFloat16 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has AArch64 Int8 Mat Mul extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has AArch32 Int8 Mat Mul extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "ID_MMFR4_EL1 trapped by HCR_EL2.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "ID_ISAR6_EL1 trapped by HCR_EL2.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Branch Record Buffer Extension") = {
    return(__brbe_implemented)
}
and __IMPDEF_boolean_map (x if x == "ISB generates Branch records") = {
    return(__isb_is_branch)
}
and __IMPDEF_boolean_map (x if x == "Has BRBEv1p1 extension") = {
    return(__brbev1p1_implemented)
}
and __IMPDEF_boolean_map (x if x == "ID_AA64ZFR0_EL1 trapped by HCR_EL2.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "ID_DFR1_EL1 trapped by HCR_EL2.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "ID_DFR1 trapped by HCR.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Unallocated encodings trapped by HCR_EL2.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Stage 2 synchronous external abort reports using Long-descriptor format when TTBCR_S.EAE is 0b0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Fault on TxSZ value above maximum") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Fault on TxSZ value below minimum") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has 52-bit IPA and PA support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has PAN3 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "SCR_EL3.SIF affects EPAN") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has MTE3 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Load Store 64-Byte instruction support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Memory location supports ST64B and LD64B") = {
    return(__feat_ls64)
}
and __IMPDEF_boolean_map (x if x == "Has Store 64-Byte with return instruction support") = {
    return(__feat_ls64_v)
}
and __IMPDEF_boolean_map (x if x == "Has Store 64-Byte EL0 with return instruction support") = {
    return(__feat_ls64_accdata)
}
and __IMPDEF_boolean_map (x if x == "Has increased Reciprocal Estimate and Square Root Estimate precision support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has SPEv1p1 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has SPEv1p2 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "event [x] is not implemented, or filtering on event [x] is not supported") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has RME extension") = {
    return(__rme_implemented)
}
and __IMPDEF_boolean_map (x if x == "GPC Fault on DC operations") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Realm EL2&0 regime affects EPAN") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has feature WFxT2") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has large 52-bit PA/IPA support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Enhanced Counter Virtualization extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has large 52-bit VA support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "the PE supports sampling of speculative instructions") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Debug has Software Lock") = {
    return(not_bool(HasArchVersion(ARMv8p4)))
}
and __IMPDEF_boolean_map (x if x == "External abort signaled in-band synchronously") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "PMU has Software Lock") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "CTI has Software Lock") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has PAC QARMA3 functionality") = {
    return(__pacqarma3_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has PAC QARMA5 functionality") = {
    return(__pacqarma5_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has PAC IMP functionality") = {
    return(not_bool(__pacqarma3_implemented | __pacqarma5_implemented))
}
and __IMPDEF_boolean_map (x if x == "Bit 55 determines the size of the PAC field") = {
    return(__pac_frac_implemented)
}
and __IMPDEF_boolean_map (x if x == "Misaligned accesses within 16 byte aligned memory but not Normal Cacheable Writeback are Atomic") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has Generic Counter Scaling support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "No tag checking of SIMD&FP loads and stores in Streaming SVE mode") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "No tag checking of ZA loads and stores") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "No fault generated for DC operations if PoC is before any level of cache") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "No fault generated for DC operations if PoU is before any level of cache") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Generate access flag fault on IC/DC operations") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Generate translation fault on IC operations") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Generate access flag fault on IC operations") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Generate address size fault on IC operations") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "IC_IVAU generates permission fault at EL0 without read permission") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Instruction Cache needs translation") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Memory system does not supports PoP") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Memory system does not supports PoDP") = {
    return(false)
}
and __IMPDEF_boolean_map x = {
    throw(Error_ImplementationDefined("Unrecognized boolean"))
}

function __IMPDEF_integer_map (x if x == "Number of breakpoints") = {
    return(__num_breakpoints)
}
and __IMPDEF_integer_map (x if x == "Number of context-aware breakpoints") = {
    return(__num_ctx_breakpoints)
}
and __IMPDEF_integer_map (x if x == "Number of watchpoints") = {
    return(__num_watchpoints)
}
and __IMPDEF_integer_map (x if x == "Number of event counters") = {
    return(__num_event_counters)
}
and __IMPDEF_integer_map (x if x == "Maximum bytes used in a single block of a copy") = {
    return(1)
}
and __IMPDEF_integer_map (x if x == "Number of BRB records") = {
    return(__num_brb_records)
}
and __IMPDEF_integer_map (x if x == "SPE Events packet payload size") = {
    return(8)
}
and __IMPDEF_integer_map (x if x == "SPE Data Source packet payload size") = {
    return(2)
}
and __IMPDEF_integer_map (x if x == "Reserved Intermediate Physical Address size value") = {
    return(52)
}
and __IMPDEF_integer_map (x if x == "Maximum Physical Address Size") = {
    return(__supported_pa_size)
}
and __IMPDEF_integer_map (x if x == "Maximum Virtual Address Size") = {
    return(__supported_va_size)
}
and __IMPDEF_integer_map (x if x == "Block BBM support level") = {
    return(__block_bbm_implemented)
}
and __IMPDEF_integer_map (x if x == "SVE Extended BFloat16 instructions are implemented") = {
    return(__has_sve_extended_bf16)
}
and __IMPDEF_integer_map (x if x == "Data Cache Invalidate Watchpoint Size") = {
    return(4 * pow2(UInt(Slice(CTR_EL0, 16, 4))))
}
and __IMPDEF_integer_map (x if x == "Instruction Cache Invalidate by VA Size") = {
    return(4 * pow2(UInt(Slice(CTR_EL0, 16, 4))))
}
and __IMPDEF_integer_map (x if x == "Linesize for DC SW instructions") = {
    return(4 * pow2(UInt(Slice(CTR_EL0, 16, 4))))
}
and __IMPDEF_integer_map (x if x == "Assosciativity for DC SW instructions") = {
    return(2)
}
and __IMPDEF_integer_map (x if x == "Numsets for DC SW instructions") = {
    return(2)
}
and __IMPDEF_integer_map x = {
    throw(Error_ImplementationDefined("Unrecognized integer"))
}

function __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-1") = {
    __ConfigureV81Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-2") = {
    __ConfigureV82Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-3") = {
    __ConfigureV83Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-4") = {
    __ConfigureV84Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-5") = {
    __ConfigureV85Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-6") = {
    __ConfigureV86Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-7") = {
    __ConfigureV87Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-8") = {
    __ConfigureV88Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-0") = {
    __ConfigureV90Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-1") = {
    __ConfigureV91Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-2") = {
    __ConfigureV92Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-3") = {
    __ConfigureV93Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.CONFIG64") = {
    CFG_RMR_AA64 = [value_name[0]]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.RVBAR") = {
    CFG_RVBAR = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.num_loregions") = {
    LORID_EL1 = SetSlice(8, LORID_EL1, 0, value_name[7 .. 0])
}
and __SetConfig ((arg, value_name) if arg == "cpu.num_loregion_descriptors") = {
    LORID_EL1 = SetSlice(8, LORID_EL1, 16, value_name[7 .. 0])
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_mops_option") = {
    __mops_option_a_supported = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.mops_cpy_default_dir") = {
    __mops_forward_copy = value_name == 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_pstate_pan") = {
    __pan_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_16bit_vmids") = {
    __vmid16_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.enable_crc32") = {
    __crc32_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_dot_product") = {
    __dot_product_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_fp16") = {
    __fp16_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_aarch32_hpd") = {
    __aa32_hpd_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_aes") = {
    __crypto_aes_implemented = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha1") = {
    __crypto_sha1_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha256") = {
    __crypto_sha256_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha512") = {
    __crypto_sha512_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha3") = {
    __crypto_sha3_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sm3") = {
    __crypto_sm3_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sm4") = {
    __crypto_sm4_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.BBM") = {
    __block_bbm_implemented = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-breakpoints") = {
    __num_breakpoints = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-watchpoints") = {
    __num_watchpoints = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-context-breakpoints") = {
    __num_ctx_breakpoints = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.pmu-num_counters") = {
    __num_event_counters = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.PA_SIZE") = {
    __supported_pa_size = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.VA_SIZE") = {
    __supported_va_size = value_name
}
and __SetConfig ((arg, value_name) if arg == "ctiBase") = {
    __CTIBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "counter_addr") = {
    __CNTControlBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntReadBase") = {
    __CNTReadBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntBaseN") = {
    __CNTBaseN = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntEL0BaseN") = {
    __CNTEL0BaseN = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntCTLBase") = {
    __CNTCTLBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "ExtDebugBase") = {
    __ExtDebugBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.PERIPHBASE") = {
    __GICCPUInterfaceBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "gic_distributor.reg-base") = {
    __GICDistBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "rdBase") = {
    __RD_base = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "sgiBase") = {
    __SGI_base = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "vlpiBase") = {
    __VLPI_base = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "gic_distributor.ITS0-base") = {
    __GICITSControlBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "pmuBase") = {
    __PMUBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "dbg_rom_addr") = {
    __DBG_ROM_ADDR = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "etmBase") = {
    __ETEBase = value_name[52 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "globalcounter.base_frequency") = {
    __CNTbase_frequency = value_name[31 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_cacheable_read_is_sync") = {
    __syncAbortOnReadNormCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_noncacheable_read_is_sync") = {
    __syncAbortOnReadNormNonCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_device_read_is_sync") = {
    __syncAbortOnDeviceRead = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_so_read_is_sync") = {
    __syncAbortOnSoRead = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_so_write_is_sync") = {
    __syncAbortOnSoWrite = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_prefetch_is_sync") = {
    __syncAbortOnPrefetch = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_ttw_cacheable_read_is_sync") = {
    __syncAbortOnTTWCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_ttw_noncacheable_read_is_sync") = {
    __syncAbortOnTTWNonCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_cacheable_write_is_sync") = {
    __syncAbortOnWriteNormCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_noncacheable_write_is_sync") = {
    __syncAbortOnWriteNormNonCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_device_write_is_sync") = {
    __syncAbortOnDeviceWrite = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_mpam") = {
    __mpam_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_has_hcr") = {
    __mpam_has_hcr = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_max_partid") = {
    __mpam_partid_max = value_name[15 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_max_pmg") = {
    __mpam_pmg_max = value_name[7 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_max_vpmr") = {
    __mpam_vpmr_max = value_name[2 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_has_altsp") = {
    __mpam_has_altsp = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_empam") = {
    __empam_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpamidr_has_tidr") = {
    __empam_tidr_implemented = value_name > 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpamidr_has_sdeflt") = {
    __empam_sdeflt_implemented = value_name > 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpamidr_has_force_ns") = {
    __empam_force_ns_implemented = value_name > 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_force_ns_rao") = {
    __empam_force_ns_RAO = value_name > 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_frac") = {
    __empam_frac = value_name[3 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L1I_override") = {
    __ICACHE_CCSIDR_RESET[0] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L1D_override") = {
    __DCACHE_CCSIDR_RESET[0] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L2_override") = {
    __DCACHE_CCSIDR_RESET[1] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L3_override") = {
    __DCACHE_CCSIDR_RESET[2] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L4_override") = {
    __DCACHE_CCSIDR_RESET[3] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L5_override") = {
    __DCACHE_CCSIDR_RESET[4] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L6_override") = {
    __DCACHE_CCSIDR_RESET[5] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.CCSIDR-L7_override") = {
    __DCACHE_CCSIDR_RESET[6] = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.DCZID-log2-block-size") = {
    __dczid_log2_block_size = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.GMID-log2-block-size") = {
    __gmid_log2_block_size = value_name
}
and __SetConfig ((arg, value_name) if arg == "exclusive_monitor.log2_granule_size") = {
    __exclusive_granule_size = value_name[3 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.unpred_tsize_aborts") = {
    __unpred_tsize_aborts = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.CONFIG64") = {
    CFG_RMR_AA64 = [value_name[0]]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.RVBAR") = {
    CFG_RVBAR = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.VAL_ignore_rvbar_in_aarch32") = {
    __ignore_rvbar_in_aarch32 = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_tlb") = {
    __tlb_enabled = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_trickbox") = {
    __trickbox_enabled = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.MPIDR-override") = {
    CFG_MPIDR = value_name[31 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-heap_base") = {
    HEAP_BASE = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-heap_limit") = {
    HEAP_LIMIT = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-stack_base") = {
    STACK_BASE = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-stack_limit") = {
    STACK_LIMIT = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_qarma3_pac") = {
    __pacqarma3_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_const_pac") = {
    __pac_frac_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_rme") = {
    __rme_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.rme_l0pgtsz") = {
    __rme_l0gptsz = value_name[3 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_brbe") = {
    __brbe_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-branch-records") = {
    __num_brb_records = 16 * DIV(value_name, 16)
}
and __SetConfig ((arg, value_name) if arg == "cpu.isb_is_branch") = {
    __isb_is_branch = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_brbe_v9_3") = {
    __brbev1p1_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme_f64f64") = {
    __has_sme_f64f64 = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme_priority_control") = {
    __has_sme_priority_control = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme_i16i64") = {
    __has_sme_i16i64 = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.sme_veclens_implemented") = {
    __max_implemented_smeveclen = __decode_maxveclen(UInt(value_name[7 .. 0]))
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sve_extended_bf16") = {
    __has_sve_extended_bf16 = UInt(value_name[1 .. 0])
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme") = {
    __has_sme = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.sme_only") = {
    __sme_only = value_name != 0
}
and __SetConfig (arg, value_name) = ()
