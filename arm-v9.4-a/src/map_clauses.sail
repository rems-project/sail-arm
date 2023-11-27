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

function __SetConfig ((arg, value_name) if arg == "ZCR_EL3.LEN") = {
    if value_name >= 0 & value_name <= UInt(0xF) then {
        ZCR_EL3_LEN_VALUE = value_name
    } else {
        let msg : string = (" can accept a value between 0 and 15. Value provided is " ++ DecStr(value_name));
        println((arg ++ msg));
        assert(false)
    }
}
and __SetConfig ((arg, value_name) if arg == "CPTR_EL3.EZ") = {
    if value_name >= 0 & value_name <= UInt(0x1) then {
        CPTR_EL3_EZ_VALUE = value_name
    } else {
        let msg : string = (" can accept a value between 0 and 1. Value provided is " ++ DecStr(value_name));
        println((arg ++ msg));
        assert(false)
    }
}
and __SetConfig ((arg, value_name) if arg == "CPTR_EL3.ESM") = {
    if value_name >= 0 & value_name <= UInt(0x1) then {
        CPTR_EL3_ESM_VALUE = value_name
    } else {
        let msg : string = (" can accept a value between 0 and 1. Value provided is " ++ DecStr(value_name));
        println((arg ++ msg));
        assert(false)
    }
}
and __SetConfig ((arg, value_name) if arg == "SMCR_EL3.LEN") = {
    if value_name >= 0 & value_name <= UInt(0xF) then {
        SMCR_EL3_LEN_VALUE = value_name
    } else {
        let msg : string = (" can accept a value between 0 and 1. Value provided is " ++ DecStr(value_name));
        println((arg ++ msg));
        assert(false)
    }
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-1") = {
    __ConfigureV81(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-2") = {
    __ConfigureV82(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-3") = {
    __ConfigureV83(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-4") = {
    __ConfigureV84(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-5") = {
    __ConfigureV85(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-6") = {
    __ConfigureV86(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-7") = {
    __ConfigureV87(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-8") = {
    __ConfigureV88(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-9") = {
    __ConfigureV89(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-0") = {
    __ConfigureV90(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-1") = {
    __ConfigureV91(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-2") = {
    __ConfigureV92(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-3") = {
    __ConfigureV93(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v9-4") = {
    __ConfigureV94(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.CONFIG64") = {
    CFG_RMR_AA64 = [value_name[0]]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.RVBAR") = {
    CFG_RVBAR = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.num_loregions") = {
    LORID_EL1[LR] = value_name[7 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.num_loregion_descriptors") = {
    LORID_EL1[LD] = value_name[7 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpy_mops_option") = {
    __cpy_mops_option_a_supported = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpyf_mops_option") = {
    __cpyf_mops_option_a_supported = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.set_mops_option") = {
    __set_mops_option_a_supported = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.setg_mops_option") = {
    __setg_mops_option_a_supported = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.mops_cpy_default_dir") = {
    __mops_forward_copy = value_name == 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_pstate_pan") = {
    FEAT_PAN_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_16bit_vmids") = {
    FEAT_VMID16_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.enable_crc32") = {
    FEAT_CRC32_IMPLEMENTED = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_dot_product") = {
    FEAT_DotProd_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_fp16") = {
    FEAT_FP16_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_aarch32_hpd") = {
    FEAT_AA32HPD_IMPLEMENTED = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_aes") = {
    FEAT_AES_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha1") = {
    FEAT_SHA1_IMPLEMENTED = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha256") = {
    FEAT_SHA256_IMPLEMENTED = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha512") = {
    FEAT_SHA512_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha3") = {
    FEAT_SHA3_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sm3") = {
    FEAT_SM3_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sm4") = {
    FEAT_SM4_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.BBM") = {
    __block_bbm_implemented = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-breakpoints") = {
    NUM_BREAKPOINTS = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-watchpoints") = {
    NUM_WATCHPOINTS = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-context-breakpoints") = {
    __num_ctx_breakpoints = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.pmu-num_counters") = {
    NUM_PMU_COUNTERS = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.PA_SIZE") = {
    __supported_pa_size = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.VA_SIZE") = {
    __supported_va_size = value_name
}
and __SetConfig ((arg, value_name) if arg == "ctiBase") = {
    __CTIBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "counter_addr") = {
    __CNTControlBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntReadBase") = {
    __CNTReadBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntBaseN") = {
    __CNTBaseN = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntEL0BaseN") = {
    __CNTEL0BaseN = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cntCTLBase") = {
    __CNTCTLBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "ExtDebugBase") = {
    __ExtDebugBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.PERIPHBASE") = {
    __GICCPUInterfaceBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "gic_distributor.reg-base") = {
    __GICDistBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "rdBase") = {
    __RD_base = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "sgiBase") = {
    __SGI_base = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "vlpiBase") = {
    __VLPI_base = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "gic_distributor.ITS0-base") = {
    __GICITSControlBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "pmuBase") = {
    __PMUBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "dbg_rom_addr") = {
    __DBG_ROM_ADDR = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "etmBase") = {
    __ETEBase = value_name[56 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "trbeBase") = {
    __TRBEBase = value_name[56 - 1 .. 0]
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
    FEAT_MPAM_IMPLEMENTED = value_name == 1
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
    __mpam_frac = value_name[3 .. 0]
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
    if value_name != 0 then {
        FEAT_PACQARMA3_IMPLEMENTED = true;
        FEAT_PACQARMA5_IMPLEMENTED = false
    };
    ()
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_const_pac") = {
    FEAT_CONSTPACFIELD_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_rme") = {
    FEAT_RME_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.rme_l0pgtsz") = {
    __rme_l0gptsz = value_name[3 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_brbe") = {
    FEAT_BRBE_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.number-of-branch-records") = {
    NUM_BRBE_RECORDS = 16 * DIV(value_name, 16)
}
and __SetConfig ((arg, value_name) if arg == "cpu.isb_is_branch") = {
    __isb_is_branch = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_brbe_v9_3") = {
    FEAT_BRBEv1p1_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme_f64f64") = {
    FEAT_SME_F64F64_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme_priority_control") = {
    __has_sme_priority_control = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme_i16i64") = {
    FEAT_SME_I16I64_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.sme_veclens_implemented") = {
    __max_implemented_smeveclen = decode_max_smeveclen(value_name)
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sve_extended_bf16") = {
    __has_sve_extended_bf16 = UInt(value_name[1 .. 0])
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.has_sme") = {
    FEAT_SME_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.sme_only") = {
    __sme_only = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "SVE.ScalableVectorExtension.veclen") = {
    __max_implemented_sveveclen = decode_max_sveveclen(value_name)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_extended_recp_estimate") = {
    __feat_rpres = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "spe.pseudo_cycles") = {
    __has_spe_pseudo_cycles = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_nested_virtualization") = {
    FEAT_NV_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_rndr") = {
    FEAT_RNG_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_enhanced_pan") = {
    FEAT_PAN3_IMPLEMENTED = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.rme_mecid_width") = {
    __mecid_width = (value_name - 1)[3 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "emulator.termination_opcode") = {
    __emulator_termination_opcode = Some(value_name[31 .. 0])
}
and __SetConfig (arg, value_name) = ()
