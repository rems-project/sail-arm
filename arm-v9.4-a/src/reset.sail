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

function SetResetVector value_name = {
    if not_bool(HaveAArch64()) then {
        if HaveEL(EL3) then {
            MVBAR = Mk_MVBAR_Type(value_name[31 .. 1] @ 0b1)
        } else {
            RVBAR = value_name[31 .. 1] @ 0b1
        }
    } else if HighestEL() == EL3 then {
        RVBAR_EL3 = Mk_RVBAR_EL3_Type(value_name)
    } else if HighestEL() == EL2 then {
        RVBAR_EL2 = Mk_RVBAR_EL2_Type(value_name)
    } else {
        RVBAR_EL1 = Mk_RVBAR_EL1_Type(value_name)
    };
    return()
}

function EncodePARange () = {
    match __supported_pa_size {
      32 => {
          return(0b0000)
      },
      36 => {
          return(0b0001)
      },
      40 => {
          return(0b0010)
      },
      42 => {
          return(0b0011)
      },
      44 => {
          return(0b0100)
      },
      48 => {
          return(0b0101)
      },
      52 => {
          assert(Have52BitPAExt());
          return(0b0110)
      },
      56 => {
          assert(Have56BitPAExt());
          return(0b0111)
      },
      _ => {
          return(0b0110)
      }
    }
}

function EncodeVARange () = {
    match __supported_va_size {
      48 => {
          return(0b0000)
      },
      52 => {
          assert(Have52BitVAExt());
          return(0b0001)
      },
      56 => {
          assert(Have56BitVAExt());
          return(0b0001)
      },
      _ => PatternMatchFailure("EncodeVARange")
    }
}

function AArch32_IMPDEFResets () = {
    PMCR_write() = [PMCR_read() with IMP = Zeros(8)];
    PMCR_write() = [PMCR_read() with IDCODE = if IsZero(PMCR_read()[IMP]) then
      Zeros(8)
    else
      CFG_PMCR_IDCODE];
    PMCR_write() = [PMCR_read() with N = NUM_PMU_COUNTERS[4 .. 0]];
    PMCR_write() = [PMCR_read() with C = 0b0];
    PMCR_write() = [PMCR_read() with P = 0b0];
    PMCEID0_write() = Mk_PMCEID0_Type(0b01001000000000100000000100000001);
    PMCEID2_write() = Mk_PMCEID2_Type(ZeroExtend(0b1111, 32));
    PMCEID1_write() = Mk_PMCEID1_Type(Zeros(32));
    PMCEID3_write() = Mk_PMCEID3_Type(Zeros(32));
    PMCFGR[NCG] = 0b0000;
    PMCFGR[FZO] = 0b1;
    PMCFGR[UEN] = 0b0;
    PMCFGR[WT] = 0b0;
    PMCFGR[NA] = 0b0;
    PMCFGR[EX] = 0b0;
    PMCFGR[CCD] = 0b1;
    PMCFGR[CC] = 0b1;
    PMCFGR[SIZE] = 0b111111;
    PMCFGR[N] = 0b000 @ NUM_PMU_COUNTERS[4 .. 0];
    PMDEVTYPE[SUB] = 0b0001;
    PMDEVTYPE[MAJOR] = 0b0110;
    PMPIDR0[PART_0] = 0b00001111;
    PMPIDR1[DES_0] = 0b1011;
    PMPIDR1[PART_1] = 0b1101;
    PMPIDR2[REVISION] = 0b0000;
    PMPIDR2[JEDEC] = 0b1;
    PMPIDR2[DES_1] = 0b011;
    PMPIDR3[REVAND] = 0b0000;
    PMPIDR3[CMOD] = 0b0000;
    PMPIDR4[SIZE] = 0b0000;
    PMPIDR4[DES_2] = 0b0100;
    PMCIDR0[PRMBL_0] = 0b00001101;
    PMCIDR1[CLASS] = 0b1001;
    PMCIDR1[PRMBL_1] = 0b0000;
    PMCIDR2[PRMBL_2] = 0b00000101;
    PMCIDR3[PRMBL_3] = 0b10110001;
    VBAR_S[31 .. 5] = Zeros(27);
    CCSIDR_write() = [CCSIDR_read() with Associativity = ZeroExtend(0x1, 21)];
    CCSIDR_write() = [CCSIDR_read() with LineSize = 0b010];
    CLIDR_write() = [CLIDR_read() with ICB = 0b00];
    CLIDR_write() = [CLIDR_read() with LoUU = 0b000];
    CLIDR_write() = [CLIDR_read() with LoUIS = 0b000];
    CLIDR_write() = Mk_CLIDR_Type([CLIDR_read().bits with 20 .. 0 = 0b000000000000000100011]);
    CTR_write() = [CTR_read() with DIC = 0b0];
    CTR_write() = [CTR_read() with IDC = 0b0];
    CTR_write() = [CTR_read() with CWG = 0b0100];
    CTR_write() = [CTR_read() with ERG = __exclusive_granule_size];
    CTR_write() = [CTR_read() with DminLine = 0b0100];
    CTR_write() = [CTR_read() with L1Ip = 0b10];
    CTR_write() = [CTR_read() with IminLine = 0b0100];
    FPSID[Implementer] = 0b01000001;
    FPSID[SW] = 0b0;
    FPSID[Subarchitecture] = 0b0000100;
    FPSID[PartNum] = 0b00110000;
    FPSID[Variant] = 0b0111;
    FPSID[Revision] = 0b0000;
    ID_DFR0_write() = [ID_DFR0_read() with MProfDbg = 0b0000];
    ID_DFR0_write() = [ID_DFR0_read() with MMapDbg = 0b0000];
    if not_bool(HaveEL(EL3)) & SCR[NS] == 0b1 then {
        ID_DFR0_write() = [ID_DFR0_read() with CopSDbg = 0b0000]
    } else {
        ID_DFR0_write() = [ID_DFR0_read() with CopSDbg = ID_DFR0_read()[CopDbg]]
    };
    ID_ISAR0_write() = [ID_ISAR0_read() with Divide = 0b0010];
    ID_ISAR0_write() = [ID_ISAR0_read() with Debug = 0b0001];
    ID_ISAR0_write() = [ID_ISAR0_read() with Coproc = 0b0000];
    ID_ISAR0_write() = [ID_ISAR0_read() with CmpBranch = 0b0001];
    ID_ISAR0_write() = [ID_ISAR0_read() with BitField = 0b0001];
    ID_ISAR0_write() = [ID_ISAR0_read() with BitCount = 0b0001];
    ID_ISAR0_write() = [ID_ISAR0_read() with Swap = 0b0000];
    ID_ISAR1_write() = [ID_ISAR1_read() with Jazelle = 0b0001];
    ID_ISAR1_write() = [ID_ISAR1_read() with Interwork = 0b0011];
    ID_ISAR1_write() = [ID_ISAR1_read() with Immediate = 0b0001];
    ID_ISAR1_write() = [ID_ISAR1_read() with IfThen = 0b0001];
    ID_ISAR1_write() = [ID_ISAR1_read() with Extend = 0b0010];
    ID_ISAR1_write() = [ID_ISAR1_read() with Except_AR = 0b0001];
    ID_ISAR1_write() = [ID_ISAR1_read() with Except = 0b0001];
    ID_ISAR1_write() = [ID_ISAR1_read() with Endian = 0b0001];
    ID_ISAR2_write() = [ID_ISAR2_read() with Reversal = 0b0010];
    ID_ISAR2_write() = [ID_ISAR2_read() with PSR_AR = 0b0001];
    ID_ISAR2_write() = [ID_ISAR2_read() with MultU = 0b0010];
    ID_ISAR2_write() = [ID_ISAR2_read() with MultS = 0b0011];
    ID_ISAR2_write() = [ID_ISAR2_read() with Mult = 0b0010];
    ID_ISAR2_write() = [ID_ISAR2_read() with MultiAccessInt = 0b0000];
    ID_ISAR2_write() = [ID_ISAR2_read() with MemHint = 0b0100];
    ID_ISAR2_write() = [ID_ISAR2_read() with LoadStore = 0b0010];
    ID_ISAR3_write() = [ID_ISAR3_read() with T32EE = 0b0000];
    ID_ISAR3_write() = [ID_ISAR3_read() with TrueNOP = 0b0001];
    ID_ISAR3_write() = [ID_ISAR3_read() with T32Copy = 0b0001];
    ID_ISAR3_write() = [ID_ISAR3_read() with TabBranch = 0b0001];
    ID_ISAR3_write() = [ID_ISAR3_read() with SynchPrim = 0b0010];
    ID_ISAR3_write() = [ID_ISAR3_read() with SVC = 0b0001];
    ID_ISAR3_write() = [ID_ISAR3_read() with SIMD = 0b0011];
    ID_ISAR3_write() = [ID_ISAR3_read() with Saturate = 0b0001];
    ID_ISAR4_write() = [ID_ISAR4_read() with SWP_frac = 0b0000];
    ID_ISAR4_write() = [ID_ISAR4_read() with PSR_M = 0b0000];
    ID_ISAR4_write() = [ID_ISAR4_read() with SynchPrim_frac = 0b0000];
    ID_ISAR4_write() = [ID_ISAR4_read() with Barrier = 0b0001];
    ID_ISAR4_write() = [ID_ISAR4_read() with SMC = 0b0000];
    ID_ISAR4_write() = [ID_ISAR4_read() with Writeback = 0b0001];
    ID_ISAR4_write() = [ID_ISAR4_read() with WithShifts = 0b0100];
    ID_ISAR4_write() = [ID_ISAR4_read() with Unpriv = 0b0010];
    ID_MMFR5_EL1[nTLBPA] = 0b0001;
    ID_ISAR5_write() = [ID_ISAR5_read() with VCMA = 0b0001];
    ID_ISAR5_write() = [ID_ISAR5_read() with RDM = 0b0001];
    ID_ISAR5_write() = [ID_ISAR5_read() with CRC32 = 0b0000];
    ID_ISAR5_write() = [ID_ISAR5_read() with SHA2 = 0b0001];
    ID_ISAR5_write() = [ID_ISAR5_read() with SHA1 = 0b0001];
    ID_ISAR5_write() = [ID_ISAR5_read() with AES = 0b0010];
    ID_ISAR5_write() = [ID_ISAR5_read() with SEVL = 0b0001];
    ID_ISAR6_write() = [ID_ISAR6_read() with DP = 0b0001];
    ID_ISAR6_write() = [ID_ISAR6_read() with BF16 = 0b0001];
    ID_ISAR6_write() = [ID_ISAR6_read() with I8MM = 0b0001];
    if IsFeatureImplemented(FEAT_FP16) then {
        MVFR1_write() = [MVFR1_read() with FPHP = 0b0011];
        MVFR1_write() = [MVFR1_read() with SIMDHP = 0b0010]
    } else {
        MVFR1_write() = [MVFR1_read() with FPHP = 0b0010];
        MVFR1_write() = [MVFR1_read() with SIMDHP = 0b0001]
    };
    if HasArchVersion(v8Ap3) then {
        ID_MMFR4_write() = [ID_MMFR4_read() with CCIDX = 0b0001];
        ID_ISAR6_write() = [ID_ISAR6_read() with JSCVT = 0b0001];
        ID_DFR0_write() = [ID_DFR0_read() with TraceFilt = 0b0001]
    };
    if HasArchVersion(v8Ap4) then {
        EDPFR.bits[39 .. 36] = 0b0001;
        ID_ISAR6_write() = [ID_ISAR6_read() with FHM = 0b0001];
        ID_PFR0_write() = [ID_PFR0_read() with AMU = 0b0001];
        ID_PFR0_write() = [ID_PFR0_read() with DIT = 0b0001];
        ID_DFR0_write() = [ID_DFR0_read() with CopDbg = 0b1001];
        if not_bool(HaveEL(EL3)) & SCR[NS] == 0b1 then {
            ID_DFR0_write() = [ID_DFR0_read() with CopSDbg = 0b0000]
        } else {
            ID_DFR0_write() = [ID_DFR0_read() with CopSDbg = ID_DFR0_EL1[CopDbg]]
        }
    };
    if HasArchVersion(v8Ap7) then {
        ID_DFR0_write() = [ID_DFR0_read() with PerfMon = 0b0111]
    };
    if HasArchVersion(v8Ap8) then {
        ID_MMFR5_write() = [ID_MMFR5_read() with ETS = 0b0010];
        ID_DFR0_write() = [ID_DFR0_read() with CopDbg = 0b1010];
        if not_bool(HaveEL(EL3)) & SCR[NS] == 0b1 then {
            ID_DFR0_write() = [ID_DFR0_read() with CopSDbg = 0b0000]
        } else {
            ID_DFR0_write() = [ID_DFR0_read() with CopSDbg = ID_DFR0_read()[CopDbg]]
        }
    };
    if HasArchVersion(v8Ap6) then {
        ID_PFR1_write() = [ID_PFR1_read() with GenTimer = 0b0010];
        ID_PFR0_write() = [ID_PFR0_read() with AMU = 0b0010]
    };
    ID_MMFR0_write() = [ID_MMFR0_read() with InnerShr = 0b0001];
    ID_MMFR0_write() = [ID_MMFR0_read() with FCSE = 0b0000];
    ID_MMFR0_write() = [ID_MMFR0_read() with AuxReg = 0b0010];
    ID_MMFR0_write() = [ID_MMFR0_read() with TCM = 0b0000];
    ID_MMFR0_write() = [ID_MMFR0_read() with ShareLvl = 0b0001];
    ID_MMFR0_write() = [ID_MMFR0_read() with OuterShr = 0b0001];
    ID_MMFR0_write() = [ID_MMFR0_read() with PMSA = 0b0000];
    ID_MMFR0_write() = [ID_MMFR0_read() with VMSA = 0b0101];
    ID_MMFR1_write() = [ID_MMFR1_read() with BPred = 0b0010];
    ID_MMFR1_write() = [ID_MMFR1_read() with L1TstCln = 0b0000];
    ID_MMFR1_write() = [ID_MMFR1_read() with L1Uni = 0b0000];
    ID_MMFR1_write() = [ID_MMFR1_read() with L1Hvd = 0b0000];
    ID_MMFR1_write() = [ID_MMFR1_read() with L1UniSW = 0b0000];
    ID_MMFR1_write() = [ID_MMFR1_read() with L1HvdSW = 0b0000];
    ID_MMFR1_write() = [ID_MMFR1_read() with L1UniVA = 0b0000];
    ID_MMFR1_write() = [ID_MMFR1_read() with L1HvdVA = 0b0000];
    ID_MMFR2_write() = [ID_MMFR2_read() with HWAccFlg = 0b0000];
    ID_MMFR2_write() = [ID_MMFR2_read() with WFIStall = 0b0001];
    ID_MMFR2_write() = [ID_MMFR2_read() with MemBarr = 0b0010];
    ID_MMFR2_write() = [ID_MMFR2_read() with UniTLB = 0b0110];
    ID_MMFR2_write() = [ID_MMFR2_read() with HvdTLB = 0b0000];
    ID_MMFR2_write() = [ID_MMFR2_read() with L1HvdRng = 0b0000];
    ID_MMFR2_write() = [ID_MMFR2_read() with L1HvdBG = 0b0000];
    ID_MMFR2_write() = [ID_MMFR2_read() with L1HvdFG = 0b0000];
    ID_MMFR3_write() = [ID_MMFR3_read() with Supersec = 0b0000];
    ID_MMFR3_write() = [ID_MMFR3_read() with CMemSz = 0b0010];
    ID_MMFR3_write() = [ID_MMFR3_read() with CohWalk = 0b0001];
    ID_MMFR3_write() = [ID_MMFR3_read() with PAN = 0b0001];
    ID_MMFR3_write() = [ID_MMFR3_read() with MaintBcst = 0b0010];
    ID_MMFR3_write() = [ID_MMFR3_read() with BPMaint = 0b0010];
    ID_MMFR3_write() = [ID_MMFR3_read() with CMaintSW = 0b0001];
    ID_MMFR3_write() = [ID_MMFR3_read() with CMaintVA = 0b0001];
    ID_PFR0_write() = [ID_PFR0_read() with RAS = 0b0010];
    ID_PFR0_write() = [ID_PFR0_read() with State3 = 0b0000];
    ID_PFR0_write() = [ID_PFR0_read() with State2 = 0b0001];
    ID_PFR0_write() = [ID_PFR0_read() with State1 = 0b0011];
    ID_PFR0_write() = [ID_PFR0_read() with State0 = 0b0001];
    ID_DFR1_write() = [ID_DFR1_read() with MTPMU = 0b0001];
    if HasArchVersion(v8Ap5) then {
        ID_PFR0_write() = [ID_PFR0_read() with CSV2 = 0b0001];
        ID_DFR0_write() = [ID_DFR0_read() with PerfMon = 0b0110]
    };
    ID_DFR0_write() = [ID_DFR0_read() with MMapTrc = 0b0001];
    ID_DFR0_write() = [ID_DFR0_read() with CopTrc = 0b0001];
    ID_PFR1_write() = [ID_PFR1_read() with GIC = 0b0000]; // In this model, no system register interface to the GIC is supported
    ID_PFR1_write() = [ID_PFR1_read() with Virt_frac = 0b0000];
    ID_PFR1_write() = [ID_PFR1_read() with Sec_frac = 0b0000];
    ID_PFR1_write() = [ID_PFR1_read() with MProgMod = 0b0000];
    ID_PFR1_write() = [ID_PFR1_read() with ProgMod = 0b0000];
    ID_PFR1_write() = [ID_PFR1_read() with Security = 0b0000];
    ID_PFR1_write() = [ID_PFR1_read() with Virtualization = 0b0000];
    MIDR_write() = [MIDR_read() with Implementer = 0b01000001];
    MIDR_write() = [MIDR_read() with Variant = 0b0000];
    MIDR_write() = [MIDR_read() with Architecture = 0b1111];
    MIDR_write() = [MIDR_read() with PartNum = 0b110100001111];
    MIDR_write() = [MIDR_read() with Revision = 0b0000];
    VPIDR_write() = [VPIDR_read() with Implementer = 0b01000001];
    VPIDR_write() = [VPIDR_read() with Variant = 0b0000];
    VPIDR_write() = [VPIDR_read() with Architecture = 0b1111];
    VPIDR_write() = [VPIDR_read() with PartNum = 0b110100001111];
    VPIDR_write() = [VPIDR_read() with Revision = 0b0000];
    MPIDR_write() = [MPIDR_read() with M = 0b1];
    MPIDR_write() = [MPIDR_read() with U = 0b0];
    MPIDR_write() = [MPIDR_read() with MT = 0b0];
    MPIDR_write() = [MPIDR_read() with Aff2 = 0b00000000];
    MPIDR_write() = [MPIDR_read() with Aff1 = 0b00000000];
    MPIDR_write() = [MPIDR_read() with Aff0 = 0b00000000];
    MVFR0_write() = [MVFR0_read() with FPRound = 0b0001];
    MVFR0_write() = [MVFR0_read() with FPShVec = 0b0000];
    MVFR0_write() = [MVFR0_read() with FPSqrt = 0b0001];
    MVFR0_write() = [MVFR0_read() with FPDivide = 0b0001];
    MVFR0_write() = [MVFR0_read() with FPTrap = 0b0001];
    MVFR0_write() = [MVFR0_read() with FPDP = 0b0010];
    MVFR0_write() = [MVFR0_read() with FPSP = 0b0010];
    MVFR0_write() = [MVFR0_read() with SIMDReg = 0b0010];
    MVFR1_write() = [MVFR1_read() with SIMDFMAC = 0b0001];
    MVFR1_write() = [MVFR1_read() with SIMDSP = 0b0001];
    MVFR1_write() = [MVFR1_read() with SIMDInt = 0b0001];
    MVFR1_write() = [MVFR1_read() with SIMDLS = 0b0001];
    MVFR1_write() = [MVFR1_read() with FPDNaN = 0b0001];
    MVFR1_write() = [MVFR1_read() with FPFtZ = 0b0001];
    MVFR2_write() = [MVFR2_read() with FPMisc = 0b0100];
    MVFR2_write() = [MVFR2_read() with SIMDMisc = 0b0011];
    TLBTR[nU] = 0b0;
    HSCTLR_write() = [HSCTLR_read() with EE = 0b0];
    SCTLR_write() = [SCTLR_read__2() with TE = _ConfigReg[ExceptInit]];
    SCTLR_write() = [SCTLR_read__2() with EE = _ConfigReg[CFGEND]];
    SCTLR_write() = [SCTLR_read__2() with SPAN = 0b0];
    SCTLR_write() = [SCTLR_read__2() with V = 0b0];
    SCTLR_write() = [SCTLR_read__2() with UNK = 0b0];
    FPEXC_write() = [FPEXC_read() with EX = 0b0];
    FPEXC_write() = [FPEXC_read() with FP2V = 0b0];
    FPEXC_write() = [FPEXC_read() with VV = 0b0];
    FPEXC_write() = [FPEXC_read() with TFV = 0b0];
    FPEXC_write() = [FPEXC_read() with VECITR = 0b111];
    HTCR_write() = [HTCR_read() with HWU62 = 0b0];
    HTCR_write() = [HTCR_read() with HWU61 = 0b0];
    HTCR_write() = [HTCR_read() with HWU60 = 0b0];
    HTCR_write() = [HTCR_read() with HWU59 = 0b0];
    HTCR_write() = [HTCR_read() with HPD = 0b0];
    HTCR_write() = [HTCR_read() with SH0 = 0b00];
    HTCR_write() = [HTCR_read() with ORGN0 = 0b00];
    HTCR_write() = [HTCR_read() with IRGN0 = 0b00];
    HTCR_write() = [HTCR_read() with T0SZ = 0b000];
    NMRR_write() = Mk_NMRR_Type([NMRR_read().bits with 31 .. 16 = 0b0100010011100000]);
    NMRR_write() = Mk_NMRR_Type([NMRR_read().bits with 15 .. 0 = 0b0100100011100000]);
    NSACR[cp11] = 0b0;
    NSACR[cp10] = 0b0;
    PRRR_write() = Mk_PRRR_Type([PRRR_read().bits with 31 .. 24 = Zeros(8)]);
    PRRR_write() = [PRRR_read() with NS1 = 0b1];
    PRRR_write() = [PRRR_read() with NS0 = 0b0];
    PRRR_write() = [PRRR_read() with DS1 = 0b0];
    PRRR_write() = [PRRR_read() with DS0 = 0b1];
    PRRR_write() = Mk_PRRR_Type([PRRR_read().bits with 15 .. 0 = 0b1000101010100100]);
    DBGDIDR[WRPs] = (NUM_WATCHPOINTS - 1)[3 .. 0];
    DBGDIDR[BRPs] = (NUM_BREAKPOINTS - 1)[3 .. 0];
    DBGDIDR[CTX_CMPs] = (__num_ctx_breakpoints - 1)[3 .. 0];
    if HasArchVersion(v8Ap2) then {
        DBGDIDR[Version] = 0b1000
    };
    if HasArchVersion(v8Ap4) then {
        DBGDIDR[Version] = 0b1001
    };
    if HasArchVersion(v8Ap8) then {
        DBGDIDR[Version] = 0b1010;
        ID_DFR0_write() = [ID_DFR0_read() with PerfMon = 0b1000]
    };
    DBGDIDR[nSUHD_imp] = 0b1;
    DBGDIDR[SE_imp] = 0b1;
    DBGDEVID[WPAddrMask] = 0b0001;
    DBGDEVID[BPAddrMask] = 0b1111;
    DBGDEVID[VectorCatch] = 0b0000;
    DBGDEVID[VirtExtns] = 0b0001;
    DBGDEVID[AuxRegs] = 0b0001;
    HDCR_write() = [HDCR_read() with HPMN = PMCR_read()[N]];
    ICC_MSRE[SRE] = 0b1;
    ICC_HSRE_write() = [ICC_HSRE_read() with SRE = 0b1];
    JMCR = Zeros(32);
    JOSCR = Zeros(32);
    JIDR = Zeros(32);
    DBGOSLSR_write() = [DBGOSLSR_read() with OSLM = 0b10];
    DBGOSLSR_write() = [DBGOSLSR_read() with OSLK = 0b1];
    HCPTR_write() = [HCPTR_read() with TCPAC = 0b0];
    HCPTR_write() = [HCPTR_read() with TTA = 0b0];
    HCPTR_write() = [HCPTR_read() with TASE = 0b0];
    HCPTR_write() = [HCPTR_read() with TCP11 = 0b0];
    HCPTR_write() = [HCPTR_read() with TCP10 = 0b0];
    if HasArchVersion(v9Ap4) then {
        ID_DFR0_write() = [ID_DFR0_read() with CopSDbg = 0b1011];
        ID_DFR0_write() = [ID_DFR0_read() with CopDbg = 0b1011];
        ID_DFR0_write() = [ID_DFR0_read() with PerfMon = 0b1001];
        ID_ISAR6_write() = [ID_ISAR6_read() with SPECRES = 0b0010];
        ID_ISAR6_write() = Mk_ID_ISAR6_Type([ID_ISAR6_read().bits with 31 .. 28 = 0b0001]);
        DBGDIDR[Version] = 0b1011;
        EDDEVID1[HSR] = 0b0010
    };
    return()
}

function AArch64_IMPDEFResets () = {
    DCZID_EL0[DZP] = 0b0;
    DCZID_EL0[BS] = __dczid_log2_block_size[3 .. 0];
    ERRIDR_EL1[NUM] = ZeroExtend(0x4, 16);
    foreach (i from 0 to (UInt(ERRIDR_EL1[NUM]) - 1) by 1 in inc) {
        assert(constraint((0 <= 'loop_i & 'loop_i < 4)));
        ERRnFR[i][CE] = 0b11;
        ERRnFR[i][DE] = 0b1;
        ERRnFR[i][UEO] = 0b1;
        ERRnFR[i][UER] = 0b1;
        ERRnFR[i][UEU] = 0b1;
        ERRnFR[i][UC] = 0b1;
        ERRnFR[i][FRX] = 0b1
    };
    ERRnFR[0][TS] = 0b01;
    ERRnFR[0][CI] = 0b10;
    ERRnFR[0][INJ] = 0b01;
    ERRnFR[0][CEO] = 0b01;
    ERRnFR[0][DUI] = 0b10;
    ERRnFR[0][RP] = 0b1;
    ERRnFR[0][CEC] = 0b100;
    ERRnFR[0][CFI] = 0b10;
    ERRnFR[0][UE] = 0b11;
    ERRnFR[0][FI] = 0b10;
    ERRnFR[0][UI] = 0b11;
    ERRnFR[0][ED] = 0b10;
    PMCR_EL0[IMP] = Zeros(8);
    PMCR_EL0[IDCODE] = if IsZero(PMCR_EL0[IMP]) then Zeros(8) else
      CFG_PMCR_IDCODE;
    PMCR_EL0[N] = NUM_PMU_COUNTERS[4 .. 0];
    PMCR_EL0[C] = 0b0;
    PMCR_EL0[P] = 0b0;
    PMCEID0_EL0 = Mk_PMCEID0_EL0_Type(ZeroExtend(0b111101001000000000100000000100000001, 64));
    PMCEID1_EL0 = Mk_PMCEID1_EL0_Type(Zeros(64));
    PMCFGR[NCG] = 0b0000;
    PMCFGR[FZO] = 0b1;
    PMCFGR[UEN] = 0b0;
    PMCFGR[WT] = 0b0;
    PMCFGR[NA] = 0b0;
    PMCFGR[EX] = 0b0;
    PMCFGR[CCD] = 0b1;
    PMCFGR[CC] = 0b1;
    PMCFGR[SIZE] = 0b111111;
    PMCFGR[N] = 0b000 @ NUM_PMU_COUNTERS[4 .. 0];
    PMDEVTYPE[SUB] = 0b0001;
    PMDEVTYPE[MAJOR] = 0b0110;
    PMPIDR0[PART_0] = 0b00001111;
    PMPIDR1[DES_0] = 0b1011;
    PMPIDR1[PART_1] = 0b1101;
    PMPIDR2[REVISION] = 0b0000;
    PMPIDR2[JEDEC] = 0b1;
    PMPIDR2[DES_1] = 0b011;
    PMPIDR3[REVAND] = 0b0000;
    PMPIDR3[CMOD] = 0b0000;
    PMPIDR4[SIZE] = 0b0000;
    PMPIDR4[DES_2] = 0b0100;
    PMCIDR0[PRMBL_0] = 0b00001101;
    PMCIDR1[CLASS] = 0b1001;
    PMCIDR1[PRMBL_1] = 0b0000;
    PMCIDR2[PRMBL_2] = 0b00000101;
    PMCIDR3[PRMBL_3] = 0b10110001;
    CNTFID0 = Mk_CNTFID0_Type(__CNTbase_frequency);
    ID_AA64MMFR1_EL1[nTLBPA] = 0b0001;
    ID_AA64DFR0_EL1[DoubleLock] = 0b1111;
    ID_AA64DFR0_EL1[PMSVer] = 0b0010;
    ID_AA64DFR0_EL1[TraceFilt] = 0b0001;
    ID_AA64DFR0_EL1[CTX_CMPs] = (__num_ctx_breakpoints - 1)[3 .. 0];
    ID_AA64DFR0_EL1[WRPs] = (NUM_WATCHPOINTS - 1)[3 .. 0];
    ID_AA64DFR0_EL1[BRPs] = (NUM_BREAKPOINTS - 1)[3 .. 0];
    ID_AA64DFR0_EL1[TraceVer] = 0b0001;
    ID_AA64DFR0_EL1[DebugVer] = 0b1001;
    if IsFeatureImplemented(FEAT_RME) then {
        ID_AA64PFR0_EL1[RME] = 0b0001;
        GPCCR_EL3[L0GPTSZ] = __rme_l0gptsz
    } else {
        ID_AA64PFR0_EL1[RME] = 0b0000
    };
    if IsFeatureImplemented(FEAT_BRBE) then {
        ID_AA64DFR0_EL1[BRBE] = 0b0010;
        BRBIDR0_EL1[CC] = 0b0101;
        BRBIDR0_EL1[FORMAT] = 0b0000;
        BRBIDR0_EL1[NUMREC] = NUM_BRBE_RECORDS[7 .. 0]
    };
    ID_AA64ISAR0_EL1[DP] = 0b0000;
    ID_AA64ISAR0_EL1[SM4] = 0b0000;
    ID_AA64ISAR0_EL1[SM3] = 0b0000;
    ID_AA64ISAR0_EL1[SHA3] = 0b0000;
    ID_AA64ISAR0_EL1[RDM] = 0b0000;
    ID_AA64ISAR0_EL1[Atomic] = 0b0000;
    ID_AA64ISAR0_EL1[CRC32] = 0b0000;
    ID_AA64ISAR0_EL1[SHA2] = 0b0001;
    ID_AA64ISAR0_EL1[SHA1] = 0b0001;
    ID_AA64ISAR0_EL1[AES] = 0b0010;
    ID_AA64ISAR1_EL1[DPB] = 0b0000;
    ID_AA64MMFR0_EL1[TGran4_2] = 0b0011;
    ID_AA64MMFR0_EL1[TGran16_2] = 0b0011;
    ID_AA64MMFR0_EL1[TGran64_2] = 0b0010;
    ID_AA64MMFR0_EL1[ExS] = 0b0001;
    ID_AA64MMFR0_EL1[FGT] = 0b0001;
    ID_AA64MMFR0_EL1[ECV] = 0b0010;
    ID_AA64MMFR0_EL1[TGran4] = 0b0001;
    ID_AA64MMFR0_EL1[TGran16] = 0b0010;
    ID_AA64MMFR0_EL1[TGran64] = 0b0000;
    ID_AA64MMFR0_EL1[BigEndEL0] = 0b0000;
    ID_AA64MMFR0_EL1[SNSMem] = 0b0001;
    ID_AA64MMFR0_EL1[BigEnd] = 0b0001;
    ID_AA64MMFR0_EL1[ASIDBits] = 0b0010;
    ID_AA64MMFR0_EL1[PARange] = EncodePARange();
    ID_AA64MMFR2_EL1[VARange] = EncodeVARange();
    ID_AA64MMFR1_EL1[XNX] = 0b0000;
    ID_AA64MMFR1_EL1[SpecSEI] = 0b0000;
    ID_AA64MMFR1_EL1[PAN] = 0b0000;
    ID_AA64MMFR1_EL1[LO] = 0b0000;
    ID_AA64MMFR1_EL1[VH] = 0b0000;
    ID_AA64MMFR1_EL1[HPDS] = 0b0000;
    ID_AA64MMFR1_EL1[VMIDBits] = 0b0000;
    ID_AA64MMFR1_EL1[HAFDBS] = 0b0000;
    ID_AA64PFR0_EL1[SVE] = 0b0001;
    ID_AA64PFR0_EL1[EL3] = 0b0001;
    ID_AA64PFR0_EL1[EL2] = 0b0001;
    ID_AA64PFR0_EL1[EL1] = 0b0001;
    ID_AA64PFR0_EL1[EL0] = 0b0010;
    ID_AA64PFR0_EL1[CSV3] = 0b0001;
    ID_AA64PFR0_EL1[CSV2] = 0b0010;
    ID_PFR2_EL1[CSV3] = 0b0001;
    ID_PFR2_EL1[SSBS] = 0b0001;
    if HaveCNTSCExt() then {
        CNTID[CNTSC] = 0b0001
    };
    ID_AA64PFR0_EL1[AMU] = 0b0001;
    AMCIDR0[PRMBL_0] = 0b00001101;
    AMCIDR1[CLASS] = 0b1001;
    AMCIDR2[PRMBL_2] = 0b00000101;
    AMCIDR3[PRMBL_3] = 0b10110001;
    AMCFGR_EL0[N] = 0b00010011;
    AMCFGR_EL0[SIZE] = 0b111111;
    AMCFGR_EL0[HDBG] = 0b1;
    AMCFGR_EL0[NCG] = (NUM_AMU_COUNTER_GROUPS - 1)[3 .. 0];
    AMCGCR_EL0[CG0NC] = NUM_AMU_CG0_MONITORS[7 .. 0];
    AMCGCR_EL0[CG1NC] = NUM_AMU_CG1_MONITORS[7 .. 0];
    AMDEVARCH[ARCHITECT] = 0b0100 @ 0b0111011;
    AMDEVARCH[PRESENT] = 0b1;
    AMDEVARCH[ARCHID] = 0b0000 @ 0b101001100110;
    AMDEVTYPE[SUB] = 0b0001;
    AMDEVTYPE[MAJOR] = 0b0110;
    AMEVTYPER0_EL0[0][evtCount] = 0b0000000000010001;
    AMEVTYPER0_EL0[1][evtCount] = 0b0100000000000100;
    AMEVTYPER0_EL0[2][evtCount] = 0b0000000000001000;
    AMEVTYPER0_EL0[3][evtCount] = 0b0100000000000101;
    AMIIDR[Implementer] = 0b010000111011;
    AMPIDR1[DES_0] = 0b1011;
    AMPIDR2[JEDEC] = 0b1;
    AMPIDR2[DES_1] = 0b011;
    AMPIDR4[DES_2] = 0b0100;
    ID_AA64PFR0_EL1[DIT] = 0b0001;
    ID_AA64PFR0_EL1[RAS] = 0b0000;
    ID_AA64PFR0_EL1[GIC] = 0b0000; // In this model, no system register interface to the GIC is supported
    ID_AA64PFR0_EL1[AdvSIMD] = 0b0000;
    ID_AA64PFR0_EL1[FP] = 0b0000;
    MPIDR_EL1.bits[31 .. 0] = CFG_MPIDR;
    VMPIDR_EL2[Aff3] = 0b00000000;
    VMPIDR_EL2[U] = 0b0;
    VMPIDR_EL2[MT] = 0b0;
    VMPIDR_EL2[Aff2] = 0b00000000;
    VMPIDR_EL2[Aff1] = 0b00000000;
    VMPIDR_EL2[Aff0] = 0b00000000;
    VMPIDR_write() = [VMPIDR_read() with M = 0b1];
    if HasArchVersion(v8Ap1) then {
        ID_ISAR5_EL1[RDM] = 0b0001;
        ID_AA64ISAR0_EL1[Atomic] = 0b0010;
        ID_AA64ISAR0_EL1[RDM] = 0b0001;
        ID_AA64MMFR1_EL1[LO] = 0b0001;
        ID_AA64MMFR1_EL1[VH] = 0b0001;
        ID_AA64MMFR1_EL1[HPDS] = 0b0001;
        ID_AA64MMFR1_EL1[HAFDBS] = 0b0010
    };
    if IsFeatureImplemented(FEAT_CRC32) then {
        ID_ISAR5_EL1[CRC32] = 0b0001;
        ID_AA64ISAR0_EL1[CRC32] = 0b0001
    };
    if IsFeatureImplemented(FEAT_VMID16) then {
        ID_AA64MMFR1_EL1[VMIDBits] = 0b0010
    };
    if IsFeatureImplemented(FEAT_PAN) then {
        ID_AA64MMFR1_EL1[PAN] = 0b0001;
        ID_MMFR3_EL1[PAN] = 0b0001
    };
    if not_bool(IsFeatureImplemented(FEAT_AES)) then {
        ID_AA64ISAR0_EL1[AES] = 0b0000
    };
    if IsFeatureImplemented(FEAT_AES) then {
        ID_AA64ISAR0_EL1[AES] = 0b0001
    };
    if IsFeatureImplemented(FEAT_AES) & IsFeatureImplemented(FEAT_PMULL) then {
        ID_AA64ISAR0_EL1[AES] = 0b0010
    };
    if not_bool(IsFeatureImplemented(FEAT_SHA1)) then {
        ID_AA64ISAR0_EL1[SHA1] = 0b0000
    };
    if not_bool(IsFeatureImplemented(FEAT_SHA256)) then {
        ID_AA64ISAR0_EL1[SHA2] = 0b0000
    };
    if HasArchVersion(v8Ap2) then {
        ID_AA64MMFR1_EL1[XNX] = 0b0001;
        ID_AA64MMFR1_EL1[PAN] = 0b0010;
        ID_AA64MMFR2_EL1[CnP] = 0b0001;
        ID_AA64MMFR2_EL1[UAO] = 0b0001;
        ID_AA64MMFR2_EL1[LSM] = 0b0001;
        ID_AA64MMFR2_EL1[IESB] = 0b0001;
        ID_MMFR3_EL1[PAN] = 0b0010;
        ID_AA64MMFR2_EL1[IDS] = 0b0001;
        ID_MMFR4_EL1[XNX] = 0b0001;
        ID_MMFR4_EL1[CnP] = 0b0001;
        ID_MMFR4_EL1[LSM] = 0b0001;
        ID_MMFR4_EL1[AC2] = 0b0001;
        if HaveEL(EL2) then {
            ID_MMFR4_EL1[EVT] = 0b0010;
            ID_AA64MMFR2_EL1[EVT] = 0b0010
        } else {
            ID_MMFR4_EL1[EVT] = 0b0000;
            ID_AA64MMFR2_EL1[EVT] = 0b0000
        };
        ID_MMFR4_EL1[EVT] = 0b0000;
        ID_AA64SMFR0_EL1[FA64] = 0b1;
        ID_AA64SMFR0_EL1[F32F32] = 0b1;
        ID_AA64SMFR0_EL1[B16F32] = 0b1;
        ID_AA64SMFR0_EL1[F16F32] = 0b1;
        ID_AA64SMFR0_EL1[I8I32] = 0b1111;
        ID_AA64SMFR0_EL1[F64F64] = 0b1;
        ID_AA64SMFR0_EL1[I16I64] = 0b1111;
        ID_AA64ISAR1_EL1[SPECRES] = 0b0001;
        ID_AA64ISAR1_EL1[SB] = 0b0001;
        ID_AA64ISAR1_EL1[DPB] = 0b0010;
        ID_ISAR6_EL1[DP] = 0b0001;
        if HaveDoPD() then {
            EDDEVID[DebugPower] = 0b0001;
            CTIDEVARCH[REVISION] = 0b0001
        } else {
            EDDEVID[DebugPower] = 0b0000;
            CTIDEVARCH[REVISION] = 0b0000
        };
        ID_AA64ZFR0_EL1[SM4] = 0b0001;
        ID_AA64ZFR0_EL1[SHA3] = 0b0001;
        ID_AA64ZFR0_EL1[BitPerm] = 0b0001;
        ID_AA64ZFR0_EL1[AES] = 0b0010;
        ID_AA64ZFR0_EL1[SVEver] = 0b0001;
        ID_AA64ZFR0_EL1[BF16] = 0b0001;
        ID_AA64ISAR1_EL1[BF16] = 0b0001;
        ID_AA64ZFR0_EL1[BF16] = 0b0010;
        ID_AA64ISAR1_EL1[BF16] = 0b0010;
        ID_AA64ISAR1_EL1[DGH] = 0b0001;
        ID_ISAR6_EL1[BF16] = 0b0001;
        ID_AA64ZFR0_EL1[I8MM] = 0b0001;
        ID_AA64ISAR1_EL1[I8MM] = 0b0001;
        ID_ISAR6_EL1[I8MM] = 0b0001
    };
    if HasArchVersion(v8Ap6) then {
        ID_AA64PFR0_EL1[AMU] = 0b0010;
        ID_PFR0_EL1[AMU] = 0b0010;
        ID_AA64ZFR0_EL1[F32MM] = 0b0001;
        ID_AA64ZFR0_EL1[F64MM] = 0b0001
    };
    if IsFeatureImplemented(FEAT_DotProd) then {
        ID_AA64ISAR0_EL1[DP] = 0b0001
    };
    if IsFeatureImplemented(FEAT_FP16) then {
        ID_AA64PFR0_EL1[FP] = 0b0001;
        ID_AA64PFR0_EL1[AdvSIMD] = 0b0001
    };
    if IsFeatureImplemented(FEAT_AA32HPD) then {
        ID_AA64MMFR1_EL1[HPDS] = 0b0010;
        ID_MMFR4_EL1[HPDS] = 0b0010
    };
    if HaveMPAMExt() then {
        if __empam_force_ns_implemented then {
            __mpam_major = CFG_MPAM_v0p1;
            __mpam_frac = CFG_MPAM_frac_v0p1;
            MPAMIDR_EL1[HAS_FORCE_NS] = 0b1
        } else {
            __mpam_major = CFG_MPAM_v1p1;
            __mpam_frac = CFG_MPAM_frac_v1p1
        };
        ID_AA64PFR0_EL1[MPAM] = __mpam_major;
        MPAMIDR_EL1[PARTID_MAX] = __mpam_partid_max;
        MPAMIDR_EL1[PMG_MAX] = __mpam_pmg_max;
        if __mpam_has_hcr then {
            MPAMIDR_EL1[HAS_HCR] = 0b1;
            MPAMIDR_EL1[VPMR_MAX] = __mpam_vpmr_max
        };
        ID_AA64PFR1_EL1[MPAM_frac] = __mpam_frac;
        assert(UInt(ID_AA64PFR0_EL1[MPAM]) > 1 | (match ID_AA64PFR0_EL1[MPAM] {
          [bitzero, bitzero, bitzero, _] => true,
          _ => false
        }) : bool & ID_AA64PFR1_EL1[MPAM_frac] == 0b0001);
        if __empam_sdeflt_implemented then {
            MPAMIDR_EL1[HAS_SDEFLT] = 0b1
        };
        if __empam_tidr_implemented then {
            MPAMIDR_EL1[HAS_TIDR] = 0b1
        };
        ()
    };
    if HasArchVersion(v9Ap2) & HaveRME() then {
        MPAMIDR_EL1[SP4] = 0b1;
        if __mpam_has_altsp then {
            MPAMIDR_EL1[HAS_ALTSP] = 0b1
        };
        ()
    };
    if HasArchVersion(v8Ap3) then {
        if IsFeatureImplemented(FEAT_PACQARMA3) then {
            ID_AA64ISAR2_EL1[GPA3] = 0b0001;
            ID_AA64ISAR2_EL1[APA3] = 0b0101;
            ID_AA64ISAR1_EL1[APA] = 0b0000;
            ID_AA64ISAR1_EL1[GPA] = 0b0000
        };
        if IsFeatureImplemented(FEAT_PACQARMA5) then {
            ID_AA64ISAR2_EL1[GPA3] = 0b0000;
            ID_AA64ISAR2_EL1[APA3] = 0b0000;
            ID_AA64ISAR1_EL1[APA] = 0b0101;
            ID_AA64ISAR1_EL1[GPA] = 0b0001
        };
        if IsFeatureImplemented(FEAT_CONSTPACFIELD) then {
            ID_AA64ISAR2_EL1[PAC_frac] = 0b0001
        } else {
            ID_AA64ISAR2_EL1[PAC_frac] = 0b0000
        };
        ID_AA64ISAR1_EL1[JSCVT] = 0b0001;
        ID_AA64ISAR1_EL1[FCMA] = 0b0001;
        ID_ISAR6_EL1[JSCVT] = 0b0001;
        ID_MMFR4_EL1[CCIDX] = 0b0001;
        ID_AA64MMFR2_EL1[NV] = 0b0001;
        ID_DFR0_EL1[TraceFilt] = 0b0001;
        ID_AA64MMFR2_EL1[CCIDX] = 0b0001;
        ID_AA64ISAR1_EL1[LRCPC] = 0b0001
    };
    if HasArchVersion(v8Ap4) then {
        ID_AA64ISAR1_EL1[LRCPC] = 0b0010;
        ID_AA64MMFR2_EL1[ST] = 0b0001;
        ID_AA64MMFR2_EL1[AT] = 0b0001;
        ID_AA64MMFR2_EL1[TTL] = 0b0001;
        ID_AA64MMFR2_EL1[FWB] = 0b0001;
        ID_AA64MMFR2_EL1[NV] = 0b0010;
        ID_DFR0_EL1[CopDbg] = 0b1001;
        if not_bool(HaveEL(EL3)) & SCR[NS] == 0b1 then {
            ID_DFR0_EL1[CopSDbg] = 0b0000
        } else {
            ID_DFR0_EL1[CopSDbg] = ID_DFR0_EL1[CopDbg]
        };
        ID_AA64PFR0_EL1[SEL2] = 0b0001;
        ID_AA64ISAR0_EL1[TLB] = 0b0010;
        ID_AA64ISAR0_EL1[TS] = 0b0000;
        ID_AA64ISAR0_EL1[FHM] = 0b0001;
        ID_ISAR6_EL1[FHM] = 0b0001;
        ID_AA64PFR0_EL1[RAS] = 0b0010;
        ID_AA64MMFR2_EL1[BBM] = __block_bbm_implemented[3 .. 0];
        if IsFeatureImplemented(FEAT_SHA512) then {
            ID_AA64ISAR0_EL1[SHA2] = 0b0010
        };
        if IsFeatureImplemented(FEAT_SHA3) then {
            ID_AA64ISAR0_EL1[SHA3] = 0b0001
        };
        if IsFeatureImplemented(FEAT_SM3) then {
            ID_AA64ISAR0_EL1[SM3] = 0b0001
        };
        if IsFeatureImplemented(FEAT_SM4) then {
            ID_AA64ISAR0_EL1[SM4] = 0b0001
        };
        if HavePMUv3p4() then {
            if HavePMUv3TH() then {
                PMMIR_EL1[THWIDTH] = 0b1100
            };
            PMMIR_EL1[BUS_WIDTH] = 0b0100;
            PMMIR_EL1[BUS_SLOTS] = 0b00000011
        };
        ()
    };
    ID_AA64PFR1_EL1[SSBS] = 0b0010;
    if HasArchVersion(v8Ap5) then {
        ID_AA64ISAR0_EL1[TS] = 0b0010;
        ID_AA64ISAR1_EL1[FRINTTS] = 0b0001;
        ID_AA64PFR1_EL1[BT] = 0b0001;
        ID_DFR0_EL1[PerfMon] = 0b0110;
        ID_AA64MMFR2_EL1[E0PD] = 0b0001;
        ID_AA64ISAR0_EL1[RNDR] = 0b0001;
        if HaveMTE2Ext() then {
            ID_AA64PFR1_EL1[MTE] = 0b0010
        };
        ID_AA64DFR0_EL1[PMUVer] = 0b0110;
        EDDFR[PMUVer] = 0b0000;
        ID_ISAR6_EL1[SB] = 0b0001;
        ID_ISAR6_EL1[SPECRES] = 0b0001
    };
    ID_DFR0_EL1[MProfDbg] = 0b0000;
    ID_DFR0_EL1[MMapDbg] = 0b0000;
    if HasArchVersion(v8Ap6) then {
        ID_AA64MMFR1_EL1[TWED] = 0b0001
    };
    ID_PFR1_EL1[GenTimer] = 0b0010;
    ID_AA64DFR0_EL1[MTPMU] = 0b0001;
    ID_DFR1_EL1[MTPMU] = 0b0001;
    if HasArchVersion(v8Ap7) then {
        ID_AA64MMFR1_EL1[HCX] = 0b0001;
        if not_bool(HaveEL(EL3)) & HaveEL(EL2) then {
            HCRX_EL2 = Mk_HCRX_EL2_Type(Zeros(64))
        };
        ID_AA64MMFR1_EL1[AFP] = 0b0001;
        ID_AA64DFR0_EL1[PMUVer] = 0b0111;
        ID_DFR0_EL1[PerfMon] = 0b0111;
        ID_AA64DFR0_EL1[PMSVer] = 0b0011;
        if __feat_rpres then {
            ID_AA64ISAR2_EL1[RPRES] = 0b0001
        };
        if Have52BitIPAAndPASpaceExt() then {
            ID_AA64MMFR0_EL1[TGran4] = 0b0001;
            ID_AA64MMFR0_EL1[TGran4_2] = 0b0011;
            ID_AA64MMFR0_EL1[TGran16] = 0b0010;
            ID_AA64MMFR0_EL1[TGran16_2] = 0b0011
        };
        ID_AA64ISAR1_EL1[XS] = 0b0001;
        ID_AA64ISAR2_EL1[WFxT] = 0b0010;
        ID_AA64MMFR1_EL1[PAN] = 0b0011;
        ID_AA64PFR1_EL1[MTE] = 0b0011;
        if HaveFeatLS64_ACCDATA() then {
            ID_AA64ISAR1_EL1[LS64] = 0b0011
        } else if HaveFeatLS64_V() then {
            ID_AA64ISAR1_EL1[LS64] = 0b0010
        } else if HaveFeatLS64() then {
            ID_AA64ISAR1_EL1[LS64] = 0b0001
        } else {
            ID_AA64ISAR1_EL1[LS64] = 0b0000
        }
    };
    GICD_TYPER.bits[9] = Bit(0b1);
    GICD_TYPER[ESPI_range] = 0b11111;
    GICD_TYPER[DVIS] = 0b1;
    GICD_TYPER[LPIS] = 0b1;
    GICD_TYPER[MBIS] = 0b1;
    GICD_TYPER[ESPI] = 0b1;
    GICD_TYPER[SecurityExtn] = 0b1;
    GICD_TYPER[ITLinesNumber] = 0b00111;
    GICD_TYPER[IDbits] = 0b01111;
    PMBIDR_EL1[F] = 0b1;
    PMBIDR_EL1[P] = 0b0;
    PMBIDR_EL1[Align] = 0b0000;
    PMCR_EL0[FZS] = 0b0;
    if IsFeatureImplemented(FEAT_SME) then {
        SMIDR_EL1[Implementer] = 0b01000001;
        SMIDR_EL1[SMPS] = 0b1;
        ID_AA64PFR1_EL1[SME] = 0b0001;
        EDDEVID1[HSR] = 0b0001
    };
    if HasArchVersion(v9Ap3) then {
        if IsFeatureImplemented(FEAT_MEC) then {
            MECIDR_EL2[MECIDWidthm1] = __mecid_width;
            ID_AA64MMFR3_EL1[MEC] = 0b0001
        };
        ()
    };
    if IsFeatureImplemented(FEAT_SME2) then {
        ID_AA64PFR1_EL1[SME] = 0b0010;
        ID_AA64SMFR0_EL1[SMEver] = 0b0001;
        ID_AA64SMFR0_EL1[I16I32] = 0b0101;
        ID_AA64SMFR0_EL1[BI32I32] = 0b1
    };
    if HasArchVersion(v8Ap8) then {
        ID_AA64MMFR1_EL1[ETS] = 0b0010;
        ID_MMFR5_EL1[ETS] = 0b0010;
        ID_AA64PFR1_EL1[NMI] = 0b0001;
        ID_AA64PFR1_EL1[RNDR_trap] = 0b0001;
        ID_AA64ISAR2_EL1[MOPS] = 0b0001;
        ID_AA64ISAR2_EL1[BC] = 0b0001;
        if HaveStatisticalProfiling() then {
            ID_AA64DFR0_EL1[PMSVer] = 0b0100
        };
        ID_AA64DFR0_EL1[HPMN0] = 0b0001;
        ID_DFR1_EL1[HPMN0] = 0b0001;
        ID_AA64DFR0_EL1[DebugVer] = 0b1010;
        ID_DFR0_EL1[CopDbg] = 0b1010;
        if not_bool(HaveEL(EL3)) & SCR[NS] == 0b1 then {
            ID_DFR0_EL1[CopSDbg] = 0b0000
        } else {
            ID_DFR0_EL1[CopSDbg] = ID_DFR0_EL1[CopDbg]
        };
        ID_AA64MMFR1_EL1[TIDCP1] = 0b0001;
        ID_AA64MMFR1_EL1[TIDCP1] = 0b0001;
        ID_AA64MMFR1_EL1[CMOW] = 0b0001;
        ID_AA64DFR0_EL1[PMUVer] = 0b1000;
        ID_DFR0_EL1[PerfMon] = 0b1000
    };
    ID_AA64ISAR0_EL1[TME] = 0b0001;
    ID_DFR0_EL1[MMapTrc] = 0b0001;
    ID_DFR0_EL1[CopTrc] = 0b0001;
    SCR_EL3[EEL2] = 0b0;
    SCR_EL3[API] = 0b0;
    SCR_EL3[APK] = 0b0;
    SCR_EL3[TERR] = 0b0;
    SCR_EL3[TLOR] = 0b0;
    SCR_EL3[TWE] = 0b0;
    SCR_EL3[TWI] = 0b0;
    SCR_EL3[ST] = 0b0;
    SCR_EL3[RW] = 0b0;
    SCR_EL3[SIF] = 0b0;
    SCR_EL3[HCE] = 0b0;
    SCR_EL3[SMD] = 0b0;
    SCR_EL3[EA] = 0b0;
    SCR_EL3[FIQ] = 0b0;
    SCR_EL3[IRQ] = 0b0;
    SCR_EL3[NS] = 0b0;
    CPTR_EL2[TCPAC] = 0b0;
    CPTR_EL2.bits[if IsFeatureImplemented(FEAT_VHE) & HCR_EL2[E2H] == 0b1 then
      28
    else
      20] = Bit(0b0);
    HCR_EL2[TID4] = 0b0;
    HCR_EL2[TOCU] = 0b0;
    HCR_EL2[TICAB] = 0b0;
    HCR_EL2[AT] = 0b0;
    HCR_EL2[NV1] = 0b0;
    HCR_EL2[NV] = 0b0;
    HCR_EL2[API] = 0b0;
    HCR_EL2[APK] = 0b0;
    HCR_EL2[MIOCNCE] = 0b0;
    HCR_EL2[TEA] = 0b0;
    HCR_EL2[TERR] = 0b0;
    HCR_EL2[ID] = 0b0;
    HCR_EL2[CD] = 0b0;
    HCR_EL2[RW] = 0b0;
    HCR_EL2[TRVM] = 0b0;
    HCR_EL2[HCD] = 0b0;
    HCR_EL2[TDZ] = 0b0;
    HCR_EL2[TGE] = 0b0;
    HCR_EL2[TVM] = 0b0;
    HCR_EL2[TTLB] = 0b0;
    HCR_EL2[TPU] = 0b0;
    HCR_EL2[TPCP] = 0b0;
    HCR_EL2[TSW] = 0b0;
    HCR_EL2[TACR] = 0b0;
    HCR_EL2[TIDCP] = 0b0;
    HCR_EL2[TSC] = 0b0;
    HCR_EL2[TID3] = 0b0;
    HCR_EL2[TID2] = 0b0;
    HCR_EL2[TID1] = 0b0;
    HCR_EL2[TID0] = 0b0;
    HCR_EL2[TWE] = 0b0;
    HCR_EL2[TWI] = 0b0;
    HCR_EL2[DC] = 0b0;
    HCR_EL2[BSU] = 0b00;
    HCR_EL2[FB] = 0b0;
    HCR_EL2[VSE] = 0b0;
    HCR_EL2[VI] = 0b0;
    HCR_EL2[VF] = 0b0;
    HCR_EL2[AMO] = 0b0;
    HCR_EL2[IMO] = 0b0;
    HCR_EL2[FMO] = 0b0;
    HCR_EL2[PTW] = 0b0;
    HCR_EL2[SWIO] = 0b0;
    HCR_EL2[VM] = 0b0;
    HSTR_EL2.bits[15 .. 0] = Zeros(16);
    SCTLR_EL2[EnIA] = 0b0;
    SCTLR_EL2[EnIB] = 0b0;
    SCTLR_EL2[EnDA] = 0b0;
    SCTLR_EL2[EE] = 0b0;
    SCTLR_EL2[EnDB] = 0b0;
    SCTLR_EL2[EnIA] = 0b0;
    SCTLR_EL2[EnIB] = 0b0;
    SCTLR_EL2[EnDA] = 0b0;
    SCTLR_EL2[EE] = 0b0;
    SCTLR_EL2[EnDB] = 0b0;
    CPACR_EL1[TTA] = 0b0;
    CPACR_EL1[FPEN] = 0b00;
    SCTLR_EL1[EnIA] = 0b0;
    SCTLR_EL1[EnIB] = 0b0;
    SCTLR_EL1[EnDA] = 0b0;
    SCTLR_EL1[EE] = 0b0;
    SCTLR_EL1[EnDB] = 0b0;
    SCTLR_EL3[EnIA] = 0b0;
    SCTLR_EL3[EnIB] = 0b0;
    SCTLR_EL3[EnDA] = 0b0;
    SCTLR_EL3[EE] = 0b0;
    SCTLR_EL3[EnDB] = 0b0;
    PMSIDR_EL1[PBT] = 0b1;
    PMSIDR_EL1[FnE] = 0b1;
    PMSIDR_EL1[CountSize] = 0b0011;
    match SPEMaxRecordSize {
      64 => {
          PMSIDR_EL1[MaxSize] = 0b0110
      },
      128 => {
          PMSIDR_EL1[MaxSize] = 0b0111
      },
      256 => {
          PMSIDR_EL1[MaxSize] = 0b1000
      },
      512 => {
          PMSIDR_EL1[MaxSize] = 0b1001
      },
      1024 => {
          PMSIDR_EL1[MaxSize] = 0b1010
      },
      2048 => {
          PMSIDR_EL1[MaxSize] = 0b1011
      },
      _ => {
          Unreachable()
      }
    };
    PMSIDR_EL1[ArchInst] = 0b1;
    PMSIDR_EL1[FL] = 0b1;
    PMSIDR_EL1[FT] = 0b1;
    PMSIDR_EL1[FE] = 0b1;
    if EL2Enabled() then {
        MDCR_EL2[TPMS] = 0b0;
        MDCR_EL2[E2PB] = 0b10
    };
    MDCR_EL2[HPMN] = PMCR_EL0[N];
    ICC_SRE_EL3[SRE] = 0b1;
    ICC_SRE_EL3[Enable] = 0b1;
    ICC_SRE_EL1_S[SRE] = 0b1;
    ICC_SRE_EL1_NS[SRE] = 0b1;
    ICC_SRE_EL2[SRE] = 0b1;
    CTR_EL0[CWG] = 0b0100;
    CTR_EL0[ERG] = __exclusive_granule_size;
    CTR_EL0[DminLine] = 0b0100;
    CTR_EL0[L1Ip] = 0b10;
    CTR_EL0[IminLine] = 0b0100;
    if HaveMTE2Ext() then {
        CTR_EL0[TminLine] = 0b000100
    };
    if HaveMTE2Ext() then {
        GMID_EL1[BS] = __gmid_log2_block_size[3 .. 0]
    };
    ICH_VMCR_EL2[VBPR0] = 0b010;
    ICH_VMCR_EL2[VBPR1] = 0b011;
    ICC_CTLR_EL1_write() = [ICC_CTLR_EL1_read() with ExtRange = 0b1];
    ICC_CTLR_EL1_write() = [ICC_CTLR_EL1_read() with PRIbits = 0b100];
    ICC_CTLR_EL1_write() = [ICC_CTLR_EL1_read() with A3V = 0b1];
    ICC_CTLR_EL1_write() = [ICC_CTLR_EL1_read() with IDbits = 0b001];
    ICV_CTLR_EL1[ExtRange] = 0b1;
    ICV_CTLR_EL1[PRIbits] = 0b100;
    ICV_CTLR_EL1[IDbits] = 0b001;
    ICV_CTLR_EL1[A3V] = 0b1;
    ICH_VTR_EL2[PRIbits] = 0b100;
    ICH_VTR_EL2[PREbits] = 0b100;
    ICH_VTR_EL2[IDbits] = 0b001;
    ICH_VTR_EL2[A3V] = 0b1;
    CCSIDR_EL1 = Mk_CCSIDR_EL1_Type(SetSlice(24, CCSIDR_EL1.bits, if IsFeatureImplemented(FEAT_CCIDX) then
      32
    else
      13, ZeroExtend(0xFF, 24)));
    CCSIDR_EL1[Associativity] = ZeroExtend(0x1, 21);
    CCSIDR_EL1[LineSize] = 0b010;
    CCSIDR2_EL1[NumSets] = ZeroExtend(0xFF, 24);
    ID_PFR1_EL1[ProgMod] = 0b0000;
    ID_PFR1_EL1[Security] = 0b0000;
    ID_PFR1_EL1[Virtualization] = 0b0000;
    OSLSR_EL1[OSLM] = 0b10;
    MDRAR_EL1[Valid] = 0b11;
    MDRAR_EL1[ROMADDR] = ZeroExtend(0x22000, 44);
    EDDFR[PMUVer] = ID_AA64DFR0_EL1[PMUVer];
    EDDEVARCH[ARCHPART] = 0xA15;
    EDDEVID1[HSR] = 0b0010;
    EDDEVARCH[ARCHVER] = 0b1011;
    EDDEVARCH[PRESENT] = 0b1;
    EDDEVARCH[ARCHITECT] = 0b01000111011;
    EDDEVID[AuxRegs] = 0b0001;
    EDDEVTYPE[MAJOR] = 0b0101;
    EDDEVTYPE[SUB] = 0b0001;
    EDPIDR0[PART_0] = ZeroExtend(0xf, 8);
    EDPIDR1[PART_1] = 0xd;
    EDPIDR1[DES_0] = truncate(0x0b, 4);
    EDPIDR2[DES_1] = 0b011;
    EDPIDR2[JEDEC] = 0b1;
    EDCIDR0[PRMBL_0] = 0x0D;
    EDCIDR1[CLASS] = 0b1001;
    EDCIDR2[PRMBL_2] = 0x05;
    EDCIDR3[PRMBL_3] = 0xb1;
    EDDFR[TraceVer] = ID_AA64DFR0_EL1[TraceVer];
    EDDFR[BRPs] = ID_AA64DFR0_EL1[BRPs];
    EDDFR[WRPs] = ID_AA64DFR0_EL1[WRPs];
    EDDFR[CTX_CMPs] = ID_AA64DFR0_EL1[CTX_CMPs];
    EDDFR[TraceFilt] = ID_AA64DFR0_EL1[TraceFilt];
    EDPRSR[PU] = 0b1;
    EDPFR[EL0] = ID_AA64PFR0_EL1[EL0];
    EDPFR[EL1] = ID_AA64PFR0_EL1[EL1];
    EDPFR[EL2] = ID_AA64PFR0_EL1[EL2];
    EDPFR[EL3] = ID_AA64PFR0_EL1[EL3];
    EDPFR[AdvSIMD] = ID_AA64PFR0_EL1[AdvSIMD];
    EDPFR[GIC] = ID_AA64PFR0_EL1[GIC];
    CTIDEVID[NUMTRIG] = 0b100000;
    CTIDEVID[NUMCHAN] = 0b100000;
    CTIDEVID[INOUT] = 0b01;
    CTIDEVARCH[ARCHITECT] = 0b01000111011;
    CTIDEVARCH[PRESENT] = 0b1;
    CTIDEVARCH[ARCHID] = 0b0001101000010100;
    CTIDEVTYPE[SUB] = 0b0001;
    CTIDEVTYPE[MAJOR] = 0b0100;
    CTIPIDR4[SIZE] = 0b0000;
    CTIPIDR4[DES_2] = 0b0100;
    CTIPIDR2[JEDEC] = 0b1;
    CTIPIDR2[DES_1] = 0b011;
    CTIPIDR1[DES_0] = 0b1011;
    CTIPIDR1[PART_1] = 0b1101;
    CTIPIDR0[PART_0] = 0b00001111;
    CTICIDR3[PRMBL_3] = 0b10110001;
    CTICIDR2[PRMBL_2] = 0b00000101;
    CTICIDR1[CLASS] = 0b1001;
    CTICIDR1[PRMBL_1] = 0b0000;
    CTICIDR0[PRMBL_0] = 0b00001101;
    ICH_VTR_EL2[PREbits] = (NUM_GIC_PREEMPTION_BITS - 1)[2 .. 0];
    ICH_VTR_EL2[ListRegs] = (NUM_GIC_LIST_REGS - 1)[4 .. 0];
    ICH_VTR_EL2[PRIbits] = (NUM_GIC_PRIORITY_BITS - 1)[2 .. 0];
    AMCG1IDR_EL0[AMEVCNTR10_EL0] = if IsG1ActivityMonitorImplemented(0) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR11_EL0] = if IsG1ActivityMonitorImplemented(1) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR12_EL0] = if IsG1ActivityMonitorImplemented(2) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR13_EL0] = if IsG1ActivityMonitorImplemented(3) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR14_EL0] = if IsG1ActivityMonitorImplemented(4) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR15_EL0] = if IsG1ActivityMonitorImplemented(5) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR16_EL0] = if IsG1ActivityMonitorImplemented(6) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR17_EL0] = if IsG1ActivityMonitorImplemented(7) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR18_EL0] = if IsG1ActivityMonitorImplemented(8) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR19_EL0] = if IsG1ActivityMonitorImplemented(9) then 0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR110_EL0] = if IsG1ActivityMonitorImplemented(10) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR111_EL0] = if IsG1ActivityMonitorImplemented(11) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR112_EL0] = if IsG1ActivityMonitorImplemented(12) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR113_EL0] = if IsG1ActivityMonitorImplemented(13) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR114_EL0] = if IsG1ActivityMonitorImplemented(14) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTR115_EL0] = if IsG1ActivityMonitorImplemented(15) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF10_EL2] = if IsG1ActivityMonitorOffsetImplemented(0) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF11_EL2] = if IsG1ActivityMonitorOffsetImplemented(1) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF12_EL2] = if IsG1ActivityMonitorOffsetImplemented(2) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF13_EL2] = if IsG1ActivityMonitorOffsetImplemented(3) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF14_EL2] = if IsG1ActivityMonitorOffsetImplemented(4) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF15_EL2] = if IsG1ActivityMonitorOffsetImplemented(5) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF16_EL2] = if IsG1ActivityMonitorOffsetImplemented(6) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF17_EL2] = if IsG1ActivityMonitorOffsetImplemented(7) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF18_EL2] = if IsG1ActivityMonitorOffsetImplemented(8) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF19_EL2] = if IsG1ActivityMonitorOffsetImplemented(9) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF110_EL2] = if IsG1ActivityMonitorOffsetImplemented(10) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF111_EL2] = if IsG1ActivityMonitorOffsetImplemented(11) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF112_EL2] = if IsG1ActivityMonitorOffsetImplemented(12) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF113_EL2] = if IsG1ActivityMonitorOffsetImplemented(13) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF114_EL2] = if IsG1ActivityMonitorOffsetImplemented(14) then
      0b1
    else
      0b0;
    AMCG1IDR_EL0[AMEVCNTOFF115_EL2] = if IsG1ActivityMonitorOffsetImplemented(15) then
      0b1
    else
      0b0;
    if HasArchVersion(v9Ap4) then {
        ID_AA64DFR1_EL1[ABL_CMPs] = 0x3f;
        ID_AA64DFR1_EL1[ABLE] = 0b0001;
        ID_AA64ISAR2_EL1[SYSREG_128] = 0b0001;
        ID_AA64ISAR2_EL1[SYSINSTR_128] = 0b0001;
        if HaveLSE128() then {
            ID_AA64ISAR0_EL1[Atomic] = 0b0011
        };
        if HaveGCS() then {
            ID_AA64PFR1_EL1[GCS] = 0b0001
        };
        ID_AA64ZFR0_EL1[SVEver] = 0b0010;
        ID_AA64DFR1_EL1[ITE] = 0b0001;
        ID_AA64SMFR0_EL1[SMEver] = 0b0010;
        if HaveSVE2p1() | HaveSME2p1() then {
            ID_AA64SMFR0_EL1[B16B16] = 0b1;
            ID_AA64ZFR0_EL1[B16B16] = 0b0001
        };
        ID_AA64SMFR0_EL1[F16F16] = 0b1;
        PMDEVID.bits[7 .. 4] = 0b0001;
        ID_AA64DFR0_EL1[SEBEP] = 0b0001;
        ID_AA64PFR1_EL1[MTE] = 0b0011;
        if HaveFeatEBEP() then {
            ID_AA64DFR1_EL1[EBEP] = 0b0001
        };
        ID_AA64MMFR2_EL1[VARange] = 0b0010;
        ID_AA64MMFR0_EL1[PARange] = 0b0111;
        ID_AA64MMFR3_EL1[D128] = 0b0001;
        ID_AA64MMFR3_EL1[D128_2] = 0b0001;
        EDDEVID1[HSR] = 0b0010;
        if HaveMTEPermExt() then {
            ID_AA64PFR2_EL1[MTEPERM] = 0b0001
        };
        if HavePFAR() then {
            ID_AA64PFR1_EL1[PFAR] = 0b0001
        };
        if HaveDoubleFault2Ext() then {
            ID_AA64PFR1_EL1[DF2] = 0b0001
        };
        if HaveTHExt() then {
            ID_AA64PFR1_EL1[THE] = 0b0001
        };
        if HaveMTE4Ext() then {
            ID_AA64PFR1_EL1[MTEX] = 0b0001;
            ID_AA64PFR2_EL1[MTESTOREONLY] = 0b0001;
            ID_AA64PFR2_EL1[MTEFAR] = 0b0001
        };
        ID_AA64MMFR4_EL1[EIESB] = 0b0001;
        if HaveRASv2Ext() then {
            ID_AA64PFR0_EL1[RAS] = 0b0011;
            ID_PFR0_EL1[RAS] = 0b0011
        };
        ID_AA64MMFR3_EL1[SNERR] = 0b0010;
        ID_AA64MMFR3_EL1[ANERR] = 0b0010;
        ID_AA64MMFR3_EL1[SDERR] = 0b0010;
        ID_AA64MMFR3_EL1[ADERR] = 0b0010;
        ID_AA64DFR1_EL1[PMICNTR] = 0b0001;
        ID_AA64DFR1_EL1[SPMU] = 0b0001;
        ID_AA64DFR1_EL1[CTX_CMPs] = 0x3f;
        ID_AA64DFR1_EL1[WRPs] = 0x3f;
        ID_AA64DFR1_EL1[BRPs] = 0x3f;
        ID_AA64DFR1_EL1[SYSPMUID] = 0x1f;
        ID_AA64PFR1_EL1[MTEX] = 0b0001;
        ID_AA64ISAR1_EL1[BF16] = 0b0010;
        ID_AA64ZFR0_EL1[BF16] = 0b0010;
        ID_AA64ISAR1_EL1[SPECRES] = 0b0010;
        ID_AA64ISAR1_EL1[LRCPC] = 0b0011;
        ID_AA64ISAR2_EL1[CLRBHB] = 0b0001;
        ID_AA64ISAR2_EL1[CSSC] = 0b0001;
        ID_AA64ISAR2_EL1[RPRFM] = 0b0001;
        ID_AA64ISAR2_EL1[PRFMSLC] = 0b0001;
        ID_AA64MMFR1_EL1[HAFDBS] = 0b0011;
        ID_AA64PFR0_EL1[CSV2] = 0b0011;
        ID_AA64MMFR1_EL1[ECBHB] = 0b0001;
        ID_AA64MMFR3_EL1[TCRX] = 0b0001;
        ID_AA64MMFR3_EL1[S1PIE] = 0b0001;
        ID_AA64MMFR3_EL1[S1POE] = 0b0001;
        ID_AA64MMFR3_EL1[S2PIE] = 0b0001;
        ID_AA64MMFR3_EL1[S2POE] = 0b0001;
        ID_AA64MMFR3_EL1[AIE] = 0b0001;
        ID_AA64MMFR3_EL1[SCTLRX] = 0b0001;
        ID_AA64MMFR3_EL1[Spec_FPACC] = 0b0001;
        ID_AA64DFR0_EL1[DebugVer] = 0b1011;
        ID_AA64DFR0_EL1[PMUVer] = 0b1001;
        ID_AA64DFR0_EL1[PMSVer] = 0b0101;
        ID_AA64DFR0_EL1.bits[59 .. 56] = 0b0001;
        ID_AA64DFR0_EL1.bits[19 .. 16] = 0b0001;
        PMDEVID[PCSample] = 0b0010;
        PMMIR_EL1.bits[27 .. 24] = 0b0001;
        PMCFGR.bits[22] = Bit(0b1);
        ID_AA64MMFR0_EL1[FGT] = 0b0010;
        ID_DFR0_EL1[CopSDbg] = 0b1011;
        ID_DFR0_EL1[CopDbg] = 0b1011;
        ID_DFR0_EL1[PerfMon] = 0b1001;
        ID_ISAR6_EL1[SPECRES] = 0b0010;
        ID_ISAR6_EL1.bits[31 .. 28] = 0b0001;
        ID_AA64DFR0_EL1[WRPs] = if NUM_WATCHPOINTS >= 16 then 0b1111 else
          (NUM_WATCHPOINTS - 1)[3 .. 0];
        ID_AA64DFR0_EL1[BRPs] = if NUM_BREAKPOINTS >= 16 then 0b1111 else
          (NUM_BREAKPOINTS - 1)[3 .. 0]
    };
    return()
}

function ResetControlRegisters cold = {
    if HaveAArch64() then {
        AArch64_AutoGen_ArchitectureReset(cold)
    } else {
        AArch32_AutoGen_ArchitectureReset(cold)
    };
    AArch32_IMPDEFResets();
    AArch64_IMPDEFResets();
    __Reset(cold);
    return()
}

function AArch32_ResetControlRegisters cold_reset = {
    PSTATE.SS = 0b0;
    ResetControlRegisters(cold_reset);
    _TLBInvalidate()
}

function AArch64_ResetControlRegisters cold_reset = {
    PSTATE.ZA = 0b0;
    PSTATE.SM = 0b0;
    PSTATE.ALLINT = 0b0;
    PSTATE.EXLOCK = 0b0;
    ResetControlRegisters(cold_reset);
    _TLBInvalidate()
}

function ResetExternalDebugRegisters cold_reset = {
    EDPRSR[PU] = 0b1;
    EDPRSR[SR] = 0b1;
    EDPRSR[OSLK] = 0b1;
    if cold_reset then {
        EDSCR_write() = [EDSCR_read() with STATUS = 0b000010];
        EDSCR_write() = [EDSCR_read() with RW = 0b1111]
    };
    return()
}

function TakeReset cold = {
    assert(HighestEL() == EL1 | HighestEL() == EL2 | HighestEL() == EL3);
    FEAT_DoubleLock_IMPLEMENTED = false;
    FEAT_EPAC_IMPLEMENTED = false;
    InitVariantImplemented();
    InitFeatureImpl();
    if cold then {
        ID_AA64PFR0_EL1[EL3] = CFG_ID_AA64PFR0_EL1_EL3;
        ID_AA64PFR0_EL1[EL2] = CFG_ID_AA64PFR0_EL1_EL2;
        ID_AA64PFR0_EL1[EL1] = CFG_ID_AA64PFR0_EL1_EL1;
        ID_AA64PFR0_EL1[EL0] = CFG_ID_AA64PFR0_EL1_EL0;
        OSLSR_EL1[OSLK] = 0b1;
        RMR_EL3[AA64] = CFG_RMR_AA64
    };
    if RMR_EL3[AA64] == 0b1 then {
        __highest_el_aarch32 = false;
        SetResetVector(CFG_RVBAR);
        AArch64_TakeReset(cold)
    } else {
        match HighestEL() {
          ? if ? == EL3 => {
              assert(ID_AA64PFR0_EL1[EL3] == 0b0010)
          },
          ? if ? == EL2 => {
              assert(ID_AA64PFR0_EL1[EL2] == 0b0010)
          },
          ? if ? == EL1 => {
              assert(ID_AA64PFR0_EL1[EL1] == 0b0010)
          },
          _ => PatternMatchFailure("TakeReset")
        };
        __highest_el_aarch32 = true;
        FeatureImpl[num_of_Feature(FEAT_AA64EL0)] = false;
        FeatureImpl[num_of_Feature(FEAT_AA64EL1)] = false;
        FeatureImpl[num_of_Feature(FEAT_AA64EL2)] = false;
        FeatureImpl[num_of_Feature(FEAT_AA64EL3)] = false;
        if __ignore_rvbar_in_aarch32 then {
            SetResetVector(ZeroExtend(0x0, 64))
        } else {
            SetResetVector(CFG_RVBAR)
        };
        if HaveEL(EL3) then {
            SCR[NS] = 0b0
        };
        AArch32_TakeReset(cold)
    };
    if ZCR_EL3_LEN_VALUE != negate(1) then {
        ZCR_EL3[LEN] = ZCR_EL3_LEN_VALUE[3 .. 0]
    };
    if CPTR_EL3_EZ_VALUE != negate(1) then {
        CPTR_EL3[EZ] = [CPTR_EL3_EZ_VALUE[0]]
    };
    if CPTR_EL3_ESM_VALUE != negate(1) then {
        CPTR_EL3[ESM] = [CPTR_EL3_ESM_VALUE[0]]
    };
    if SMCR_EL3_LEN_VALUE != negate(1) then {
        SMCR_EL3[LEN] = SMCR_EL3_LEN_VALUE[3 .. 0]
    };
    ()
}

val __InitSystem : unit -> unit

function __InitSystem () = {
    DBGEN = Signal_Low;
    TakeReset(true);
    CNTCR[EN] = 0b1
}
