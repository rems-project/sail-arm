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

function __EndCycle () = {
    {
        __cycle_count = __cycle_count + 1
    }
}

function __ListConfig () = {
    {
        print("cpu.has_arm_v8-1=0 (bool) default = '0'\\n        : Implement the ARMv8.1 Extension.\\n");
        print("cpu.has_arm_v8-2=0 (bool) default = '0'\\n        : Implement the ARMv8.2 Extension.\\n");
        print("cpu.has_arm_v8-3=0 (bool) default = '0'\\n        : Implement the ARMv8.3 Extension.\\n");
        print("cpu.has_arm_v8-4=0 (bool) default = '0'\\n        : Implement the ARMv8.4 Extension. This feature is incomplete and under development.\\n");
        print("cpu.num_loregions=0x0 (int) default = '0x0' \\n        : Number of Limited Ordering Regions implemented excluding background region (if ARM v8.1 extensions are implemented) : [0x0..0xFF]\\n");
        print("cpu.num_loregion_descriptors=0x0 (int) default = '0x0'\\n        : Number of Limited Ordering Region descriptors implemented (if ARM v8.1 extensions are implemented) : [0x0..0xFF]\\n");
        print("cpu.PA_SIZE=0x30 (int) default = '0x30'\\n        : Physical address range supported.  For ARMv8.0 and ARMv8.1 this is limited to 48 bits. : [0x20..0x34]\\n");
        print("counter_addr=0x0 (int) default = '0x0'\\n        : Address for memory-mapped system counter block.  0 means the counter is not mapped, otherwise the address must be 4KB aligned.\\n");
        print("cpu.ext_abort_normal_cacheable_read_is_sync=1 (bool) default = '1' \\n        : Synchronous reporting of normal write-back cacheable-read External aborts\\n");
        print("cpu.ext_abort_normal_noncacheable_read_is_sync=1 (bool) default = '1'\\n        : Synchronous reporting of normal noncacheable-read External aborts\\n");
        print("cpu.ext_abort_device_read_is_sync=1 (bool) default = '1'\\n        : Synchronous reporting of device-nGnRE read External aborts\\n");
        print("cpu.ext_abort_so_read_is_sync=1 (bool) default = '1'\\n        : Synchronous reporting of device-nGnRnE read External aborts\\n");
        print("cpu.ext_abort_so_write_is_sync=1 (bool) default = '1'\\n        : Synchronous reporting of device-nGnRnE write External aborts\\n");
        print("cpu.ext_abort_prefetch_is_sync=1 (bool) default = '1'\\n        : Behavior of External aborts generated by normal writeback cacheable instruction fetches.\\n        [0, 1], 0: asynchronous abort,  1: synchronous abort.\\n");
        print("cpu.ext_abort_ttw_cacheable_read_is_sync=1 (bool) default = '1'\\n        : Synchronous reporting of TTW cacheable read External aborts\\n");
        print("cpu.ext_abort_ttw_noncacheable_read_is_sync=1 (bool) default = '1'\\n        : Synchronous reporting of TTW noncacheable read External aborts\\n");
        print("cpu.ext_abort_normal_cacheable_write_is_sync=0 (bool) default = '0'\\n        : Synchronous reporting of normal write-back cacheable write External aborts\\n");
        print("cpu.ext_abort_normal_noncacheable_write_is_sync=0 (bool) default = '0'\\n        : Synchronous reporting of normal noncacheable write External aborts\\n");
        print("cpu.ext_abort_device_write_is_sync=0 (bool) default = '0'\\n        : Synchronous reporting of device-nGnRE write External aborts\\n");
        print("cpu.unpred_tsize_aborts=0 (bool) default = '0'\\n        : Behavior when TSize is out of range.\\n        [0, 1], 0: force into range. 1: translation fault, forces unpred_tsize_pamax_aborts to 1.\\n");
        print("cpu.isb_is_branch=1 (bool) default='1'\\n        : ISB is treated as branch");
        print("cpu.cpu0.enable_crc32=0x0 (int) default = '0x0'\\n        : CRC32 instructions supported.\\n        [0, 1], 0: CRC32 not implemented. 1: CRC32 instructions implemented.\\n");
        print("cpu.has_pstate_pan=0x1 (int) default = '0x1' \\n        : Implement the PSTATE.PAN (Privileged Access Never) control from ARMv8.1.\\n        [0, 1], 0: not implemented. 1: Implemented\\n");
        print("cpu.has_16bit_vmids=0x1 (int) default = '0x1'\\n        : Implement support for 16-bit VMIDs from ARMv8.1\\n        [0, 1], 0: Not enabled, 1: Implemented\\n");
        print("cpu.has_dot_product=0x1 (int) default = '0x1' \\n        : Implement the dot product (UDOT, SDOT) instructions from ARMv8.4\\n        [0, 1], 0: Not implemnetd, 1: Implemnetd\\n");
        print("cpu.has_fp16=0x1 (int) default = '0x1' \\n        : Implement the half-precision floating-point data processing instructions from ARMv8.2.\\n        [0, 1] 0: feature is not enabled. 1: feature is implemented\\n");
        print("cpu.has_aarch32_hpd=0 (bool) default = '0'\\n        : If true then hierarchical permission disable is supported in AArch32\\n");
        print("cpu.has_tlb=0x1 (bool) default = '1'\\n        : If true then TLB is enabled\\n");
        print("cpu.has_trickbox=0x1 (bool) default = '1'\\n        : If true then Trickbox and abort region checks are enabled\\n");
        print("cpu.VAL_ignore_rvbar_in_aarch32=0  default = '0'\\n        : If '1', ignore RVBAR while determining reset vector in AArch32. This is required for ACK tests \\n");
        print("SVE.ScalableVectorExtension.sme_veclens_implemented=7  (int) default = '0x7'\\n        : Implies which SME vector lengths are implemented: represented as a bitfield where bit[n]==1 implies SME vector length of 128*2^n bits is implemented \\n");
        print("SVE.ScalableVectorExtension.veclen=0x20  (int) default = '0x20'\\n        : Implies which non streaming SVE vector lengths are implemented: size of vector in uints of 64 bits \\n");
        print("SVE.ScalableVectorExtension.has_sme=1  (bool) default = '1'\\n        : If SME is implemented or not\\n");
        print("SVE.ScalableVectorExtension.sme_only=0  (bool) default = '0'\\n        : Where SME is implemented, whether SVE functionality is available only when SM=1 \\n");
        print("SVE.ScalableVectorExtension.has_sme_priority_control=1  (bool) default = '1'\\n        : Whether SME prioirty Control is implemented \\n");
        print("SVE.ScalableVectorExtension.has_sme_f64f64=1  (bool) default = '1'\\n        : Where SME is implemented, whether double precision FMOPA and FMOPS are implemented \\n");
        print("SVE.ScalableVectorExtension.has_sme_i16i64=1  (bool) default = '1'\\n        : Where SME is implemented, whether instructions that accumulate 16-bit integer outer products into 64-bit integer tiles are implemented \\n");
        print("SVE.ScalableVectorExtension.has_sve_extended_bf16=0x2  (int) default = '0x2'\\n        : Whether Extended BFloat16 instructions are implemented: 0 - Disabled, 1 - Enabled, 2 - Enabled if SME is implemented \\n");
        print("cpu.has_extended_recp_estimate=0x0  (int) default = '0x1'\\n        : Whether increased Reciprocal Estimate and Square Root Estimate precision is supported: 0 - Disabled, 1 - Enabled  \\n");
        print("cpu.has_mpam=1 (bool) default = 0\\n        : Implement the MPAM extension.\\n        [0, 1] 0: FALSE, not implemented. 1: TRUE, implemented.\\n");
        print("cpu.has_mpamhcr=1 (bool) default = 1\\n        : If MPAM is implemented, also implement the MPAM virtualization features.\\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\\n");
        print("cpu.mpam_partid_max=127 (int) default = 0\\n        : [0 .. 65535] Maximum MPAM PARTID supported by the implementation.");
        print("cpu.mpam_pmg_max=3 (int) default = 0\\n        : [0 .. 255] Maximum MPAM PMG supported by the implementation.\\n");
        print("cpu.mpam_vpmr_max=2 (int) default = 0\\n        : [0 .. 7] Maximum MPAM virtual PARTID mapping register implemented.\\n");
        print("cpu.mpam_has_altsp=1 (int) default = 1\\n        : [0, 1] Whether MPAMIDR_EL1.HAS_ALTSP is set or cleared.\\n");
        print("cpu.has_empam=1 (bool) default = 0\\n        : Implement the Enhanced MPAM extension.\\n        [0, 1] 0: FALSE, not implemented. 1: TRUE, implemented.\\n");
        print("cpu.empam_has_tidr (bool) default = 0\\n        : Implement the MPAM2_EL2.TIDR bit to trap MPAMIDR_EL1.\\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\\n");
        print("cpu.empam_has_sdeflt (bool) default = 0\\n        : Implement the MPAM3_EL3.SDEFLT bit to generate only the default PARTID in Secure execution.\\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\\n");
        print("cpu.empam_has_force_ns (bool) default = 0\\n        : Implement the MPAMe_EL3.FORCE_NS bit to generate Non-secure PARTIDs in Secure execution.\\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\\n");
        print("cpu.empam_force_ns_RAO (bool) default = 0\\n        : Implement the MPAM3_EL3.FORCE_NS bit as Read-as-One.\\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\\n");
        print("cpu.cpu0.crypto_aes=0x2 (int) default = '0x2'\\n        : AES and 128 bit PMULL instructions supported.\\n        [0, 1, 2], 0: AES instruction not implemented. 1: AES instruction implemented. 2: AES plus 128bit PMULL instruction implemented\\n");
        print("cpu.cpu0.crypto_sha1=0x1 (int) default = '0x1'\\n        : SHA1 instructions supported.\\n        [0, 1], 0: SHA1 not implemented. 1: SHA1 instructions implemented.\\n");
        print("cpu.cpu0.crypto_sha256=0x1 (int) default = '0x1'\\n        : SHA256 instructions supported.\\n        [0, 1], 0: SHA256 not implemented. 1: SHA256 instructions implemented.\\n");
        print("cpu.cpu0.crypto_sha512=0x0 (int) default = '0x0'\\n        : SHA512 instructions supported.\\n        [0, 1], 0: SHA512 not implemented. 1: SHA512 instructions implemented.\\n");
        print("cpu.cpu0.crypto_sha3=0x0 (int) default = '0x0'\\n        : SHA3 instructions supported.\\n        [0, 1], 0: SHA3 not implemented. 1: SHA3 instructions implemented.\\n");
        print("cpu.cpu0.crypto_sm3=0x0 (int) default = '0x0'\\n        : SM3 instructions supported.\\n        [0, 1], 0: SM3 not implemented. 1: SM3 instructions implemented.\\n");
        print("cpu.cpu0.crypto_sm4=0x0 (int) default = '0x0'\\n        : SM4 instructions supported.\\n        [0, 1], 0: SM4 not implemented. 1: SM4 instructions implemented.\\n");
        print("cpu.cpu0.number-of-breakpoints=0x10 (int) default='0x10'\\n        : [1 .. 16] Number of breakpoints.\\n");
        print("cpu.cpu0.number-of-context-breakpoints=0x10 (int) default='0x10'\\n        : [1 .. 16] Number of breakpoints that are context aware.\\n");
        print("cpu.cpu0.number-of-watchpoints=0x10 (int) default='0x10'\\n        : [1 .. 16] Number of watchpoints.\\n");
        print("cpu.pmu-num_counters=0x1f (int) default='0x1f'\\n        : [1 .. 16] Number of event counters.\\n");
        print("cpu.has_brbe=0x1 (int) default='0x1'\\n        : Branch Record Buffer Extension supported.\\n        [0, 1], 0 Not implemented, 1: Implemented\\n");
        print("cpu.cpu0.number-of-branch-records=0x40 (int) default='0x40'\\n        : [16, 32, 48, 64] Number of BRB records.\\n");
        print("cpu.has_mops_option=0x1 (int) default='0x1'\\n        : FEAT_MOPS uses option A or B. \\n        [1, 2], 1 FEAT_MOPS uses option A, 2 FEAT_MOPS uses option B\\n");
        print("cpu.mops_cpy_default_dir=0 (int) default='0x0'\\n        : CPY* instructions copy in forward/backward direction in non-overlapping case,\\n        [0, 1], 0 forward direction,  1 backward direction.\\n");
        print("cpu.has_brbe_v9_3=0x1 (int) default='0x1'\\n        :if 1, implements FEAT_BRBEv1p1.\\n");
        print("spe.pseudo_cycles=0 (bool) default=0 \\n        :if 1, extra cycles are generated on memory reads and writes.\\n");
        print("ZCR_EL3.LEN=0xf (int) default=UNKNOWN \\n        :Specify the vector size of VL at EL3.\\n");
        print("CPTR_EL3.EZ=0x1 (int) default=UNKNOWN \\n        :Enable Trap for non-streaming mode SVE instructions.\\n");
        print("CPTR_EL3.ESM=0x1 (int) default=UNKNOWN \\n        :Enable Trap for SME instructions.\\n");
        print("SMCR_EL3.LEN=0xf (int) default=UNKNOWN \\n        :Specify the effective streaming vector length.\\n")
    }
}

function __Reset cold = {
    {
        __last_cycle_count = 0
    };
    {
        __last_branch_valid = false
    };
    {
        sp_rel_access_pc = Ones(64)
    };
    {
        __cycle_count = 0
    }
}

function __WakeupRequest () = ()
