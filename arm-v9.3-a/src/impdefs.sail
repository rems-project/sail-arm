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

function HasArchVersion(version) = true
function HaveAArch32() = true
function HaveAArch32EL(el) = (el == EL0)
function HaveEL(el) = true
function HaveFP16Ext() = true

function MaxImplementedVL() = MAX_VL
function MaxImplementedSVL() = __max_implemented_smeveclen

function ProcessorID() = 0
function IsExclusiveGlobal(paddress, processorid, size) = true
function IsExclusiveLocal(paddress, processorid, size) = true
function AArch64_IsExclusiveVA(address, processorid, size) = true
function AArch64_MarkExclusiveVA(address, processorid, size) = ()
function ExclusiveMonitorsStatus() = 0b0

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
      _ => {
          return(undefined : bits(4))
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
      _ => {
          return(undefined : bits(4))
      }
    }
}

val AArch32_IMPDEFResets : unit -> unit effect {rreg, wreg}

function AArch32_IMPDEFResets () = {
    PMCR_write() = SetSlice(8, PMCR_read(), 24, Zeros());
    PMCR_write() = SetSlice(8, PMCR_read(), 16, if IsZero(Slice(PMCR_read(), 24, 8)) then
      Zeros()
    else
      CFG_PMCR_IDCODE);
    PMCR_write() = SetSlice(5, PMCR_read(), 11, __num_event_counters[4 .. 0]);
    PMCR_write() = SetSlice(1, PMCR_read(), 2, 0b0);
    PMCR_write() = SetSlice(1, PMCR_read(), 1, 0b0);
    PMCEID0_write() = 0b01001000000000100000000100000001;
    PMCEID2_write() = ZeroExtend(0b1111, 32);
    PMCEID1_write() = Zeros();
    PMCEID3_write() = Zeros();
    PMCFGR = SetSlice(4, PMCFGR, 28, 0b0000);
    PMCFGR = SetSlice(1, PMCFGR, 21, 0b1);
    PMCFGR = SetSlice(1, PMCFGR, 19, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 18, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 17, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 16, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 15, 0b1);
    PMCFGR = SetSlice(1, PMCFGR, 14, 0b1);
    PMCFGR = SetSlice(6, PMCFGR, 8, 0b111111);
    PMCFGR = SetSlice(8, PMCFGR, 0, 0b000 @ __num_event_counters[4 .. 0]);
    PMDEVTYPE = SetSlice(4, PMDEVTYPE, 4, 0b0001);
    PMDEVTYPE = SetSlice(4, PMDEVTYPE, 0, 0b0110);
    PMPIDR0 = SetSlice(8, PMPIDR0, 0, 0b00001111);
    PMPIDR1 = SetSlice(4, PMPIDR1, 4, 0b1011);
    PMPIDR1 = SetSlice(4, PMPIDR1, 0, 0b1101);
    PMPIDR2 = SetSlice(4, PMPIDR2, 4, 0b0000);
    PMPIDR2 = SetSlice(1, PMPIDR2, 3, 0b1);
    PMPIDR2 = SetSlice(3, PMPIDR2, 0, 0b011);
    PMPIDR3 = SetSlice(4, PMPIDR3, 4, 0b0000);
    PMPIDR3 = SetSlice(4, PMPIDR3, 0, 0b0000);
    PMPIDR4 = SetSlice(4, PMPIDR4, 4, 0b0000);
    PMPIDR4 = SetSlice(4, PMPIDR4, 0, 0b0100);
    PMCIDR0 = SetSlice(8, PMCIDR0, 0, 0b00001101);
    PMCIDR1 = SetSlice(4, PMCIDR1, 4, 0b1001);
    PMCIDR1 = SetSlice(4, PMCIDR1, 0, 0b0000);
    PMCIDR2 = SetSlice(8, PMCIDR2, 0, 0b00000101);
    PMCIDR3 = SetSlice(8, PMCIDR3, 0, 0b10110001);
    VBAR_S[31 .. 5] = Zeros();
    CCSIDR_write() = SetSlice(21, CCSIDR_read(), 3, ZeroExtend(0x1, 21));
    CCSIDR_write() = SetSlice(3, CCSIDR_read(), 0, 0b010);
    CLIDR_write() = SetSlice(2, CLIDR_read(), 30, 0b00);
    CLIDR_write() = SetSlice(3, CLIDR_read(), 27, 0b000);
    CLIDR_write() = SetSlice(3, CLIDR_read(), 24, 0b010);
    CLIDR_write() = SetSlice(3, CLIDR_read(), 21, 0b000);
    CLIDR_write() = [CLIDR_read() with 20 .. 0 = 0b000000000000000100011];
    CTR_write() = SetSlice(1, CTR_read(), 29, 0b0);
    CTR_write() = SetSlice(1, CTR_read(), 28, 0b0);
    CTR_write() = SetSlice(4, CTR_read(), 24, 0b0100);
    CTR_write() = SetSlice(4, CTR_read(), 20, __exclusive_granule_size);
    CTR_write() = SetSlice(4, CTR_read(), 16, 0b0100);
    CTR_write() = SetSlice(2, CTR_read(), 14, 0b10);
    CTR_write() = SetSlice(4, CTR_read(), 0, 0b0100);
    FPSID = SetSlice(8, FPSID, 24, 0b01000001);
    FPSID = SetSlice(1, FPSID, 23, 0b0);
    FPSID = SetSlice(7, FPSID, 16, 0b0000100);
    FPSID = SetSlice(8, FPSID, 8, 0b00110000);
    FPSID = SetSlice(4, FPSID, 4, 0b0111);
    FPSID = SetSlice(4, FPSID, 0, 0b0000);
    ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 20, 0b0000);
    ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 8, 0b0000);
    if not_bool(HaveEL(EL3)) & Slice(SCR, 0, 1) == 0b1 then {
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 4, 0b0000)
    } else {
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 4, Slice(ID_DFR0_read(), 0, 4))
    };
    ID_ISAR0_write() = SetSlice(4, ID_ISAR0_read(), 24, 0b0010);
    ID_ISAR0_write() = SetSlice(4, ID_ISAR0_read(), 20, 0b0001);
    ID_ISAR0_write() = SetSlice(4, ID_ISAR0_read(), 16, 0b0000);
    ID_ISAR0_write() = SetSlice(4, ID_ISAR0_read(), 12, 0b0001);
    ID_ISAR0_write() = SetSlice(4, ID_ISAR0_read(), 8, 0b0001);
    ID_ISAR0_write() = SetSlice(4, ID_ISAR0_read(), 4, 0b0001);
    ID_ISAR0_write() = SetSlice(4, ID_ISAR0_read(), 0, 0b0000);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 28, 0b0001);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 24, 0b0011);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 20, 0b0001);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 16, 0b0001);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 12, 0b0010);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 8, 0b0001);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 4, 0b0001);
    ID_ISAR1_write() = SetSlice(4, ID_ISAR1_read(), 0, 0b0001);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 28, 0b0010);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 24, 0b0001);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 20, 0b0010);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 16, 0b0011);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 12, 0b0010);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 8, 0b0000);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 4, 0b0100);
    ID_ISAR2_write() = SetSlice(4, ID_ISAR2_read(), 0, 0b0010);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 28, 0b0000);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 24, 0b0001);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 20, 0b0001);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 16, 0b0001);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 12, 0b0010);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 8, 0b0001);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 4, 0b0011);
    ID_ISAR3_write() = SetSlice(4, ID_ISAR3_read(), 0, 0b0001);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 28, 0b0000);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 24, 0b0000);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 20, 0b0000);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 16, 0b0001);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 12, 0b0000);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 8, 0b0001);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 4, 0b0100);
    ID_ISAR4_write() = SetSlice(4, ID_ISAR4_read(), 0, 0b0010);
    ID_MMFR5_EL1 = SetSlice(4, ID_MMFR5_EL1, 4, 0b0001);
    ID_ISAR5_write() = SetSlice(4, ID_ISAR5_read(), 28, 0b0001);
    ID_ISAR5_write() = SetSlice(4, ID_ISAR5_read(), 24, 0b0001);
    ID_ISAR5_write() = SetSlice(4, ID_ISAR5_read(), 16, 0b0000);
    ID_ISAR5_write() = SetSlice(4, ID_ISAR5_read(), 12, 0b0001);
    ID_ISAR5_write() = SetSlice(4, ID_ISAR5_read(), 8, 0b0001);
    ID_ISAR5_write() = SetSlice(4, ID_ISAR5_read(), 4, 0b0010);
    ID_ISAR5_write() = SetSlice(4, ID_ISAR5_read(), 0, 0b0001);
    ID_ISAR6_write() = SetSlice(4, ID_ISAR6_read(), 4, 0b0001);
    ID_ISAR6_write() = SetSlice(4, ID_ISAR6_read(), 20, 0b0001);
    ID_ISAR6_write() = SetSlice(4, ID_ISAR6_read(), 24, 0b0001);
    if __fp16_implemented then {
        MVFR1_write() = SetSlice(4, MVFR1_read(), 24, 0b0011);
        MVFR1_write() = SetSlice(4, MVFR1_read(), 20, 0b0010)
    } else {
        MVFR1_write() = SetSlice(4, MVFR1_read(), 24, 0b0010);
        MVFR1_write() = SetSlice(4, MVFR1_read(), 20, 0b0001)
    };
    if HasArchVersion(ARMv8p3) then {
        ID_MMFR4_write() = SetSlice(4, ID_MMFR4_read(), 24, 0b0001);
        ID_ISAR6_write() = SetSlice(4, ID_ISAR6_read(), 0, 0b0001);
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 28, 0b0001)
    };
    if HasArchVersion(ARMv8p4) then {
        EDPFR = SetSlice(4, EDPFR, 36, 0b0001);
        ID_ISAR6_write() = SetSlice(4, ID_ISAR6_read(), 8, 0b0001);
        ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 20, 0b0001);
        ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 24, 0b0001);
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 0, 0b1001);
        if not_bool(HaveEL(EL3)) & Slice(SCR, 0, 1) == 0b1 then {
            ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 4, 0b0000)
        } else {
            ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 4, Slice(ID_DFR0_EL1, 0, 4))
        }
    };
    if HasArchVersion(ARMv8p7) then {
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 24, 0b0111);
        ID_MMFR5_write() = SetSlice(4, ID_MMFR5_read(), 0, 0b0001)
    };
    if HasArchVersion(ARMv8p8) then {
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 0, 0b1010);
        if not_bool(HaveEL(EL3)) & Slice(SCR, 0, 1) == 0b1 then {
            ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 4, 0b0000)
        } else {
            ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 4, Slice(ID_DFR0_read(), 0, 4))
        }
    };
    if HasArchVersion(ARMv8p6) then {
        ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 16, 0b0010);
        ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 20, 0b0010)
    };
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 28, 0b0001);
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 24, 0b0000);
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 20, 0b0010);
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 16, 0b0000);
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 12, 0b0001);
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 8, 0b0001);
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 4, 0b0000);
    ID_MMFR0_write() = SetSlice(4, ID_MMFR0_read(), 0, 0b0101);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 28, 0b0010);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 24, 0b0000);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 20, 0b0000);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 16, 0b0000);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 12, 0b0000);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 8, 0b0000);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 4, 0b0000);
    ID_MMFR1_write() = SetSlice(4, ID_MMFR1_read(), 0, 0b0000);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 28, 0b0000);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 24, 0b0001);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 20, 0b0010);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 16, 0b0110);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 12, 0b0000);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 8, 0b0000);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 4, 0b0000);
    ID_MMFR2_write() = SetSlice(4, ID_MMFR2_read(), 0, 0b0000);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 28, 0b0000);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 24, 0b0010);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 20, 0b0001);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 16, 0b0001);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 12, 0b0010);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 8, 0b0010);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 4, 0b0001);
    ID_MMFR3_write() = SetSlice(4, ID_MMFR3_read(), 0, 0b0001);
    ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 28, 0b0010);
    ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 12, 0b0000);
    ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 8, 0b0001);
    ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 4, 0b0011);
    ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 0, 0b0001);
    ID_DFR1_write() = SetSlice(4, ID_DFR1_read(), 0, 0b0001);
    if HasArchVersion(ARMv8p5) then {
        ID_PFR0_write() = SetSlice(4, ID_PFR0_read(), 16, 0b0001);
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 24, 0b0110)
    };
    ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 16, 0b0001);
    ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 12, 0b0001);
    ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 28, 0b0011);
    ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 24, 0b0000);
    ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 20, 0b0000);
    ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 8, 0b0000);
    ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 0, 0b0000);
    ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 4, 0b0000);
    ID_PFR1_write() = SetSlice(4, ID_PFR1_read(), 12, 0b0000);
    MIDR_write() = SetSlice(8, MIDR_read(), 24, 0b01000001);
    MIDR_write() = SetSlice(4, MIDR_read(), 20, 0b0000);
    MIDR_write() = SetSlice(4, MIDR_read(), 16, 0b1111);
    MIDR_write() = SetSlice(12, MIDR_read(), 4, 0b110100001111);
    MIDR_write() = SetSlice(4, MIDR_read(), 0, 0b0000);
    VPIDR_write() = SetSlice(8, VPIDR_read(), 24, 0b01000001);
    VPIDR_write() = SetSlice(4, VPIDR_read(), 20, 0b0000);
    VPIDR_write() = SetSlice(4, VPIDR_read(), 16, 0b1111);
    VPIDR_write() = SetSlice(12, VPIDR_read(), 4, 0b110100001111);
    VPIDR_write() = SetSlice(4, VPIDR_read(), 0, 0b0000);
    MPIDR_write() = SetSlice(1, MPIDR_read(), 31, 0b1);
    MPIDR_write() = SetSlice(1, MPIDR_read(), 30, 0b0);
    MPIDR_write() = SetSlice(1, MPIDR_read(), 24, 0b0);
    MPIDR_write() = SetSlice(8, MPIDR_read(), 16, 0b00000000);
    MPIDR_write() = SetSlice(8, MPIDR_read(), 8, 0b00000000);
    MPIDR_write() = SetSlice(8, MPIDR_read(), 0, 0b00000000);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 28, 0b0001);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 24, 0b0000);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 20, 0b0001);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 16, 0b0001);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 12, 0b0001);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 8, 0b0010);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 4, 0b0010);
    MVFR0_write() = SetSlice(4, MVFR0_read(), 0, 0b0010);
    MVFR1_write() = SetSlice(4, MVFR1_read(), 28, 0b0001);
    MVFR1_write() = SetSlice(4, MVFR1_read(), 16, 0b0001);
    MVFR1_write() = SetSlice(4, MVFR1_read(), 12, 0b0001);
    MVFR1_write() = SetSlice(4, MVFR1_read(), 8, 0b0001);
    MVFR1_write() = SetSlice(4, MVFR1_read(), 4, 0b0001);
    MVFR1_write() = SetSlice(4, MVFR1_read(), 0, 0b0001);
    MVFR2_write() = SetSlice(4, MVFR2_read(), 4, 0b0100);
    MVFR2_write() = SetSlice(4, MVFR2_read(), 0, 0b0011);
    TLBTR = SetSlice(1, TLBTR, 0, 0b0);
    HSCTLR_write() = SetSlice(1, HSCTLR_read(), 25, 0b0);
    SCTLR_write() = SetSlice(1, SCTLR_read__2(), 30, [_ConfigReg[22]]);
    SCTLR_write() = SetSlice(1, SCTLR_read__2(), 25, [_ConfigReg[2]]);
    SCTLR_write() = SetSlice(1, SCTLR_read__2(), 23, 0b0);
    SCTLR_write() = SetSlice(1, SCTLR_read__2(), 13, 0b0);
    SCTLR_write() = SetSlice(1, SCTLR_read__2(), 6, 0b0);
    FPEXC_write() = SetSlice(1, FPEXC_read(), 31, 0b0);
    FPEXC_write() = SetSlice(1, FPEXC_read(), 28, 0b0);
    FPEXC_write() = SetSlice(1, FPEXC_read(), 27, 0b0);
    FPEXC_write() = SetSlice(1, FPEXC_read(), 26, 0b0);
    FPEXC_write() = SetSlice(3, FPEXC_read(), 8, 0b111);
    HTCR_write() = SetSlice(1, HTCR_read(), 28, 0b0);
    HTCR_write() = SetSlice(1, HTCR_read(), 27, 0b0);
    HTCR_write() = SetSlice(1, HTCR_read(), 26, 0b0);
    HTCR_write() = SetSlice(1, HTCR_read(), 25, 0b0);
    HTCR_write() = SetSlice(1, HTCR_read(), 24, 0b0);
    HTCR_write() = SetSlice(2, HTCR_read(), 12, 0b00);
    HTCR_write() = SetSlice(2, HTCR_read(), 10, 0b00);
    HTCR_write() = SetSlice(2, HTCR_read(), 8, 0b00);
    HTCR_write() = SetSlice(3, HTCR_read(), 0, 0b000);
    NMRR_write() = [NMRR_read() with 31 .. 16 = 0b0100010011100000];
    NMRR_write() = [NMRR_read() with 15 .. 0 = 0b0100100011100000];
    NSACR = SetSlice(1, NSACR, 11, 0b0);
    NSACR = SetSlice(1, NSACR, 10, 0b0);
    PRRR_write() = [PRRR_read() with 31 .. 24 = Zeros()];
    PRRR_write() = SetSlice(1, PRRR_read(), 19, 0b1);
    PRRR_write() = SetSlice(1, PRRR_read(), 18, 0b0);
    PRRR_write() = SetSlice(1, PRRR_read(), 17, 0b0);
    PRRR_write() = SetSlice(1, PRRR_read(), 16, 0b1);
    PRRR_write() = [PRRR_read() with 15 .. 0 = 0b1000101010100100];
    DBGDIDR = SetSlice(4, DBGDIDR, 28, (__num_watchpoints - 1)[3 .. 0]);
    DBGDIDR = SetSlice(4, DBGDIDR, 24, (__num_breakpoints - 1)[3 .. 0]);
    DBGDIDR = SetSlice(4, DBGDIDR, 20, (__num_ctx_breakpoints - 1)[3 .. 0]);
    if HasArchVersion(ARMv8p2) then {
        DBGDIDR = SetSlice(4, DBGDIDR, 16, 0b1000)
    };
    if HasArchVersion(ARMv8p4) then {
        DBGDIDR = SetSlice(4, DBGDIDR, 16, 0b1001)
    };
    if HasArchVersion(ARMv8p8) then {
        DBGDIDR = SetSlice(4, DBGDIDR, 16, 0b1010);
        ID_DFR0_write() = SetSlice(4, ID_DFR0_read(), 24, 0b1000)
    };
    DBGDIDR = SetSlice(1, DBGDIDR, 14, 0b1);
    DBGDIDR = SetSlice(1, DBGDIDR, 12, 0b1);
    DBGDEVID = SetSlice(4, DBGDEVID, 4, 0b0001);
    DBGDEVID = SetSlice(4, DBGDEVID, 8, 0b1111);
    DBGDEVID = SetSlice(4, DBGDEVID, 12, 0b0000);
    DBGDEVID = SetSlice(4, DBGDEVID, 16, 0b0001);
    DBGDEVID = SetSlice(4, DBGDEVID, 24, 0b0001);
    HDCR_write() = SetSlice(5, HDCR_read(), 0, Slice(PMCR_read(), 11, 5));
    ICC_MSRE = SetSlice(1, ICC_MSRE, 0, 0b1);
    ICC_HSRE_write() = SetSlice(1, ICC_HSRE_read(), 0, 0b1);
    JMCR = Zeros();
    JOSCR = Zeros();
    JIDR = Zeros();
    DBGOSLSR_write() = SetSlice(1, DBGOSLSR_read(), 3, Slice(0b10, 1, 1));
    DBGOSLSR_write() = SetSlice(1, DBGOSLSR_read(), 0, Slice(0b10, 0, 1));
    HCPTR_write() = SetSlice(1, HCPTR_read(), 31, 0b0);
    HCPTR_write() = SetSlice(1, HCPTR_read(), 20, 0b0);
    HCPTR_write() = SetSlice(1, HCPTR_read(), 15, 0b0);
    HCPTR_write() = SetSlice(1, HCPTR_read(), 11, 0b0);
    HCPTR_write() = SetSlice(1, HCPTR_read(), 10, 0b0);
    return()
}

val AArch64_IMPDEFResets : unit -> unit effect {rreg, wreg}

function AArch64_IMPDEFResets () = {
    DCZID_EL0 = SetSlice(1, DCZID_EL0, 4, 0b0);
    DCZID_EL0 = SetSlice(4, DCZID_EL0, 0, __dczid_log2_block_size[3 .. 0]);
    ERRIDR_EL1 = SetSlice(16, ERRIDR_EL1, 0, ZeroExtend(0x4, 16));
    foreach (i from 0 to (UInt(Slice(ERRIDR_EL1, 0, 16)) - 1) by 1 in inc) {
        assert(constraint((0 <= 'loop_i & 'loop_i < 4)));
        ERRnFR[i][54 .. 53] = 0b11;
        ERRnFR[i][52 .. 52] = 0b1;
        ERRnFR[i][51 .. 51] = 0b1;
        ERRnFR[i][50 .. 50] = 0b1;
        ERRnFR[i][49 .. 49] = 0b1;
        ERRnFR[i][48 .. 48] = 0b1;
        ERRnFR[i][31 .. 31] = 0b1
    };
    ERRnFR[0][25 .. 24] = 0b01;
    ERRnFR[0][23 .. 22] = 0b10;
    ERRnFR[0][21 .. 20] = 0b01;
    ERRnFR[0][19 .. 18] = 0b01;
    ERRnFR[0][17 .. 16] = 0b10;
    ERRnFR[0][15 .. 15] = 0b1;
    ERRnFR[0][14 .. 12] = 0b100;
    ERRnFR[0][11 .. 10] = 0b10;
    ERRnFR[0][9 .. 8] = 0b11;
    ERRnFR[0][7 .. 6] = 0b10;
    ERRnFR[0][5 .. 4] = 0b11;
    ERRnFR[0][1 .. 0] = 0b10;
    PMCR_EL0 = SetSlice(8, PMCR_EL0, 24, Zeros());
    PMCR_EL0 = SetSlice(8, PMCR_EL0, 16, if IsZero(Slice(PMCR_EL0, 24, 8)) then
      Zeros()
    else
      CFG_PMCR_IDCODE);
    PMCR_EL0 = SetSlice(5, PMCR_EL0, 11, __num_event_counters[4 .. 0]);
    PMCR_EL0 = SetSlice(1, PMCR_EL0, 2, 0b0);
    PMCR_EL0 = SetSlice(1, PMCR_EL0, 1, 0b0);
    PMCEID0_EL0 = ZeroExtend(0b111101001000000000100000000100000001, 64);
    PMCEID1_EL0 = Zeros();
    PMCFGR = SetSlice(4, PMCFGR, 28, 0b0000);
    PMCFGR = SetSlice(1, PMCFGR, 21, 0b1);
    PMCFGR = SetSlice(1, PMCFGR, 19, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 18, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 17, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 16, 0b0);
    PMCFGR = SetSlice(1, PMCFGR, 15, 0b1);
    PMCFGR = SetSlice(1, PMCFGR, 14, 0b1);
    PMCFGR = SetSlice(6, PMCFGR, 8, 0b111111);
    PMCFGR = SetSlice(8, PMCFGR, 0, 0b000 @ __num_event_counters[4 .. 0]);
    PMDEVTYPE = SetSlice(4, PMDEVTYPE, 4, 0b0001);
    PMDEVTYPE = SetSlice(4, PMDEVTYPE, 0, 0b0110);
    PMPIDR0 = SetSlice(8, PMPIDR0, 0, 0b00001111);
    PMPIDR1 = SetSlice(4, PMPIDR1, 4, 0b1011);
    PMPIDR1 = SetSlice(4, PMPIDR1, 0, 0b1101);
    PMPIDR2 = SetSlice(4, PMPIDR2, 4, 0b0000);
    PMPIDR2 = SetSlice(1, PMPIDR2, 3, 0b1);
    PMPIDR2 = SetSlice(3, PMPIDR2, 0, 0b011);
    PMPIDR3 = SetSlice(4, PMPIDR3, 4, 0b0000);
    PMPIDR3 = SetSlice(4, PMPIDR3, 0, 0b0000);
    PMPIDR4 = SetSlice(4, PMPIDR4, 4, 0b0000);
    PMPIDR4 = SetSlice(4, PMPIDR4, 0, 0b0100);
    PMCIDR0 = SetSlice(8, PMCIDR0, 0, 0b00001101);
    PMCIDR1 = SetSlice(4, PMCIDR1, 4, 0b1001);
    PMCIDR1 = SetSlice(4, PMCIDR1, 0, 0b0000);
    PMCIDR2 = SetSlice(8, PMCIDR2, 0, 0b00000101);
    PMCIDR3 = SetSlice(8, PMCIDR3, 0, 0b10110001);
    CNTFID0 = __CNTbase_frequency;
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 48, 0b0001);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 36, 0b1111);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 32, 0b0000);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 40, 0b0000);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 28, (__num_ctx_breakpoints - 1)[3 .. 0]);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 20, (__num_watchpoints - 1)[3 .. 0]);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 12, (__num_breakpoints - 1)[3 .. 0]);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 4, 0b0000);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 0, 0b1001);
    if __rme_implemented then {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 52, 0b0001);
        GPCCR_EL3 = SetSlice(4, GPCCR_EL3, 20, __rme_l0gptsz)
    } else {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 52, 0b0000)
    };
    if __brbe_implemented then {
        ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 52, 0b0010);
        BRBIDR0_EL1 = SetSlice(4, BRBIDR0_EL1, 12, 0b0101);
        BRBIDR0_EL1 = SetSlice(4, BRBIDR0_EL1, 8, 0b0000);
        BRBIDR0_EL1 = SetSlice(8, BRBIDR0_EL1, 0, __num_brb_records[7 .. 0])
    };
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 44, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 40, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 36, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 32, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 28, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 20, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 16, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 12, 0b0001);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 8, 0b0001);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 4, 0b0010);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 28, 0b0000);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 24, 0b0000);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 20, 0b0000);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 16, 0b0000);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 12, 0b0000);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 8, 0b0000);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 4, 0b0000);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 0, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 32, 0b0010);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 36, 0b0010);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 40, 0b0010);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 44, 0b0001);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 56, 0b0001);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 60, 0b0010);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 28, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 24, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 20, 0b0001);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 16, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 12, 0b0001);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 8, 0b0001);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 4, 0b0010);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 0, EncodePARange());
    ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 16, EncodeVARange());
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 28, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 24, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 20, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 16, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 8, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 12, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 4, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 0, 0b0000);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 32, 0b0001);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 12, 0b0001);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 8, 0b0001);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 4, 0b0001);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 0, 0b0010);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 60, 0b0001);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 56, 0b0010);
    ID_PFR2_EL1 = SetSlice(4, ID_PFR2_EL1, 0, 0b0001);
    ID_PFR2_EL1 = SetSlice(4, ID_PFR2_EL1, 4, 0b0001);
    if HaveCNTSCExt() then {
        CNTID = SetSlice(4, CNTID, 0, 0b0001)
    };
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 44, 0b0001);
    AMCIDR0 = SetSlice(8, AMCIDR0, 0, 0b00001101);
    AMCIDR1 = SetSlice(4, AMCIDR1, 4, 0b1001);
    AMCIDR2 = SetSlice(8, AMCIDR2, 0, 0b00000101);
    AMCIDR3 = SetSlice(8, AMCIDR3, 0, 0b10110001);
    AMCFGR_EL0 = SetSlice(8, AMCFGR_EL0, 0, 0b00010011);
    AMCFGR_EL0 = SetSlice(6, AMCFGR_EL0, 8, 0b111111);
    AMCFGR_EL0 = SetSlice(1, AMCFGR_EL0, 24, 0b1);
    AMCFGR_EL0 = SetSlice(4, AMCFGR_EL0, 28, 0b0001);
    AMCGCR_EL0 = SetSlice(8, AMCGCR_EL0, 0, 0b00000100);
    AMCGCR_EL0 = SetSlice(8, AMCGCR_EL0, 8, 0b00010000);
    AMDEVARCH = SetSlice(11, AMDEVARCH, 21, 0b0100 @ 0b0111011);
    AMDEVARCH = SetSlice(1, AMDEVARCH, 20, 0b1);
    AMDEVARCH = SetSlice(16, AMDEVARCH, 0, 0b0000 @ 0b101001100110);
    AMDEVTYPE = SetSlice(4, AMDEVTYPE, 4, 0b0001);
    AMDEVTYPE = SetSlice(4, AMDEVTYPE, 0, 0b0110);
    AMEVTYPER0_EL0[0][15 .. 0] = 0b0000000000010001;
    AMEVTYPER0_EL0[1][15 .. 0] = 0b0100000000000100;
    AMEVTYPER0_EL0[2][15 .. 0] = 0b0000000000001000;
    AMEVTYPER0_EL0[3][15 .. 0] = 0b0100000000000101;
    AMIIDR = SetSlice(12, AMIIDR, 0, 0b010000111011);
    AMPIDR1 = SetSlice(4, AMPIDR1, 4, 0b1011);
    AMPIDR2 = SetSlice(1, AMPIDR2, 3, 0b1);
    AMPIDR2 = SetSlice(3, AMPIDR2, 0, 0b011);
    AMPIDR4 = SetSlice(4, AMPIDR4, 0, 0b0100);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 48, 0b0001);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 28, 0b0000);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 24, 0b0000); // In this model, no system register interface to the GIC is supported
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 20, 0b0000);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 16, 0b0000);
    MPIDR_EL1[31 .. 0] = CFG_MPIDR;
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 32, 0b00000000);
    VMPIDR_EL2 = SetSlice(1, VMPIDR_EL2, 30, 0b0);
    VMPIDR_EL2 = SetSlice(1, VMPIDR_EL2, 24, 0b0);
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 16, 0b00000000);
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 8, 0b00000000);
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 0, 0b00000000);
    VMPIDR_write() = SetSlice(1, VMPIDR_read(), 31, 0b1);
    if HasArchVersion(ARMv8p1) then {
        ID_ISAR5_EL1 = SetSlice(4, ID_ISAR5_EL1, 24, 0b0001);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 20, 0b0010);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 28, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 16, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 8, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 12, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 0, 0b0010)
    };
    if __crc32_implemented then {
        ID_ISAR5_EL1 = SetSlice(4, ID_ISAR5_EL1, 16, 0b0001);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 16, 0b0001)
    };
    if __vmid16_implemented then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 4, 0b0010)
    };
    if __pan_implemented then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 20, 0b0001);
        ID_MMFR3_EL1 = SetSlice(4, ID_MMFR3_EL1, 16, 0b0001)
    };
    if __crypto_aes_implemented == 0 then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 4, 0b0000)
    };
    if __crypto_aes_implemented == 1 then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 4, 0b0001)
    };
    if not_bool(__crypto_sha1_implemented) then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 8, 0b0000)
    };
    if not_bool(__crypto_sha256_implemented) then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 12, 0b0000)
    };
    if HasArchVersion(ARMv8p2) then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 28, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 20, 0b0010);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 0, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 4, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 8, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 12, 0b0001);
        ID_MMFR3_EL1 = SetSlice(4, ID_MMFR3_EL1, 16, 0b0010);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 36, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 8, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 12, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 20, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 4, 0b0001);
        if HaveEL(EL2) then {
            ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 28, 0b0010);
            ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 56, 0b0010)
        } else {
            ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 28, 0b0000);
            ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 56, 0b0000)
        };
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 28, 0b0000);
        ID_AA64SMFR0_EL1 = SetSlice(1, ID_AA64SMFR0_EL1, 32, 0b1);
        ID_AA64SMFR0_EL1 = SetSlice(1, ID_AA64SMFR0_EL1, 34, 0b1);
        ID_AA64SMFR0_EL1 = SetSlice(1, ID_AA64SMFR0_EL1, 35, 0b1);
        ID_AA64SMFR0_EL1 = SetSlice(4, ID_AA64SMFR0_EL1, 36, 0b1111);
        ID_AA64SMFR0_EL1 = SetSlice(1, ID_AA64SMFR0_EL1, 48, 0b1);
        ID_AA64SMFR0_EL1 = SetSlice(4, ID_AA64SMFR0_EL1, 52, 0b1111);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 40, 0b0001);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 36, 0b0001);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 0, 0b0010);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 4, 0b0001);
        EDDEVID = SetSlice(4, EDDEVID, 4, 0b0000);
        CTIDEVARCH = SetSlice(4, CTIDEVARCH, 16, 0b0000);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 40, 0b0001);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 32, 0b0001);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 16, 0b0001);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 4, 0b0010);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 0, 0b0001);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 20, 0b0001);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 44, 0b0001);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 20, 0b0010);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 44, 0b0010);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 48, 0b0001);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 20, 0b0001);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 44, 0b0001);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 52, 0b0001);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 24, 0b0001)
    };
    if HasArchVersion(ARMv8p6) then {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 44, 0b0010);
        ID_PFR0_EL1 = SetSlice(4, ID_PFR0_EL1, 20, 0b0010);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 52, 0b0001);
        ID_AA64ZFR0_EL1 = SetSlice(4, ID_AA64ZFR0_EL1, 56, 0b0001)
    };
    if __dot_product_implemented then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 44, 0b0001)
    };
    if __fp16_implemented then {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 16, 0b0001);
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 20, 0b0001)
    };
    if __aa32_hpd_implemented then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 12, 0b0010);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 16, 0b0010)
    };
    if __mpam_implemented then {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 40, CFG_ID_AA64PFR0_EL1_MPAM);
        MPAMIDR_EL1 = SetSlice(16, MPAMIDR_EL1, 0, __mpam_partid_max);
        MPAMIDR_EL1 = SetSlice(8, MPAMIDR_EL1, 32, __mpam_pmg_max);
        if __mpam_has_hcr then {
            MPAMIDR_EL1 = SetSlice(1, MPAMIDR_EL1, 17, 0b1);
            MPAMIDR_EL1 = SetSlice(3, MPAMIDR_EL1, 18, __mpam_vpmr_max)
        };
        ()
    };
    if __empam_implemented then {
        ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 16, __empam_frac);
        assert(UInt(Slice(ID_AA64PFR0_EL1, 40, 4)) > 1 | (match Slice(ID_AA64PFR0_EL1, 40, 4) {
          [bitzero, bitzero, bitzero, _] => true,
          _ => false
        }) : bool & Slice(ID_AA64PFR1_EL1, 16, 4) == 0b0001);
        if __empam_sdeflt_implemented then {
            MPAMIDR_EL1 = SetSlice(1, MPAMIDR_EL1, 61, 0b1)
        };
        if __empam_tidr_implemented then {
            MPAMIDR_EL1 = SetSlice(1, MPAMIDR_EL1, 58, 0b1)
        };
        if __empam_force_ns_implemented then {
            assert(Slice(ID_AA64PFR0_EL1, 40, 4) == 0b0000 & Slice(ID_AA64PFR1_EL1, 16, 4) == 0b0001);
            MPAMIDR_EL1 = SetSlice(1, MPAMIDR_EL1, 60, 0b1)
        };
        ()
    };
    if HasArchVersion(ARMv9p2) & HaveRME() then {
        MPAMIDR_EL1 = SetSlice(1, MPAMIDR_EL1, 59, 0b1);
        if __mpam_has_altsp then {
            MPAMIDR_EL1 = SetSlice(1, MPAMIDR_EL1, 57, 0b1)
        };
        ()
    };
    if HasArchVersion(ARMv8p3) then {
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 4, 0b0101);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 8, 0b0000);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 24, 0b0001);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 28, 0b0000);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 12, 0b0001);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 0, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 24, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 24, 0b0001);
        ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 28, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 20, 0b0001);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 20, 0b0001);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 16, 0b0001)
    };
    if HasArchVersion(ARMv8p4) then {
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 20, 0b0010);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 28, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 32, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 48, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 40, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 24, 0b0010);
        ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 0, 0b1001);
        if not_bool(HaveEL(EL3)) & Slice(SCR, 0, 1) == 0b1 then {
            ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 4, 0b0000)
        } else {
            ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 4, Slice(ID_DFR0_EL1, 0, 4))
        };
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 36, 0b0001);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 56, 0b0010);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 52, 0b0000);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 48, 0b0001);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 8, 0b0001);
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 28, 0b0010);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 52, __block_bbm_implemented[3 .. 0]);
        if __crypto_sha512_implemented then {
            ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 12, 0b0010)
        };
        if __crypto_sha3_implemented then {
            ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 32, 0b0001)
        };
        if __crypto_sm3_implemented then {
            ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 36, 0b0001)
        };
        if __crypto_sm4_implemented then {
            ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 40, 0b0001)
        };
        if HavePMUv3p4() then {
            if HavePMUv3TH() then {
                PMMIR_EL1 = SetSlice(4, PMMIR_EL1, 20, 0b1100)
            };
            PMMIR_EL1 = SetSlice(4, PMMIR_EL1, 16, 0b0100);
            PMMIR_EL1 = SetSlice(8, PMMIR_EL1, 8, 0b00000011)
        };
        ()
    };
    ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 4, 0b0010);
    if HasArchVersion(ARMv8p5) then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 52, 0b0010);
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 32, 0b0001);
        ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 0, 0b0001);
        ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 24, 0b0110);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 60, 0b0001);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 60, 0b0001);
        if HaveMTE2Ext() then {
            ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 8, 0b0010)
        };
        ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 8, 0b0110);
        EDDFR = SetSlice(4, EDDFR, 8, 0b0000);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 12, 0b0001);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 16, 0b0001)
    };
    ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 20, 0b0000);
    ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 8, 0b0000);
    if HasArchVersion(ARMv8p6) then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 32, 0b0001)
    };
    ID_PFR1_EL1 = SetSlice(4, ID_PFR1_EL1, 16, 0b0010);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 48, 0b0001);
    ID_DFR1_EL1 = SetSlice(4, ID_DFR1_EL1, 0, 0b0001);
    if HasArchVersion(ARMv8p7) then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 40, 0b0001);
        if not_bool(HaveEL(EL3)) & HaveEL(EL2) then {
            HCRX_EL2 = Zeros()
        };
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 44, 0b0001);
        ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 8, 0b0111);
        ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 24, 0b0111);
        ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 32, 0b0011);
        ID_AA64ISAR2_EL1 = SetSlice(4, ID_AA64ISAR2_EL1, 4, 0b0001);
        if Have52BitIPAAndPASpaceExt() then {
            ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 28, 0b0001);
            ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 40, 0b0011);
            ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 20, 0b0010);
            ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 32, 0b0011)
        };
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 56, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 36, 0b0001);
        ID_MMFR5_EL1 = SetSlice(4, ID_MMFR5_EL1, 0, 0b0001);
        ID_AA64ISAR2_EL1 = SetSlice(4, ID_AA64ISAR2_EL1, 0, 0b0010);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 20, 0b0011);
        ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 8, 0b0011);
        if HaveFeatLS64_ACCDATA() then {
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 60, 0b0011)
        } else if HaveFeatLS64_V() then {
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 60, 0b0010)
        } else if HaveFeatLS64() then {
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 60, 0b0001)
        } else {
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 60, 0b0000)
        }
    };
    GICD_TYPER[9 .. 9] = 0b1;
    GICD_TYPER = SetSlice(5, GICD_TYPER, 27, 0b11111);
    GICD_TYPER = SetSlice(1, GICD_TYPER, 18, 0b1);
    GICD_TYPER = SetSlice(1, GICD_TYPER, 17, 0b1);
    GICD_TYPER = SetSlice(1, GICD_TYPER, 16, 0b1);
    GICD_TYPER = SetSlice(1, GICD_TYPER, 8, 0b1);
    GICD_TYPER = SetSlice(1, GICD_TYPER, 10, 0b1);
    GICD_TYPER = SetSlice(5, GICD_TYPER, 0, 0b00111);
    GICD_TYPER = SetSlice(5, GICD_TYPER, 19, 0b01111);
    PMBIDR_EL1 = SetSlice(1, PMBIDR_EL1, 5, 0b1);
    PMBIDR_EL1 = SetSlice(1, PMBIDR_EL1, 4, 0b0);
    PMBIDR_EL1 = SetSlice(4, PMBIDR_EL1, 0, 0b0000);
    if HasArchVersion(ARMv8p8) then {
        ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 24, 0b1000);
        if __pacqarma3_implemented then {
            ID_AA64ISAR2_EL1[11 .. 8] = 0b0001;
            ID_AA64ISAR2_EL1[15 .. 12] = 0b0101;
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 4, 0b0000);
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 24, 0b0000)
        } else {
            ID_AA64ISAR2_EL1[11 .. 8] = 0b0000;
            ID_AA64ISAR2_EL1[15 .. 12] = 0b0000;
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 4, 0b0101);
            ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 24, 0b0001)
        };
        if __pac_frac_implemented then {
            ID_AA64ISAR2_EL1[27 .. 24] = 0b0001
        } else {
            ID_AA64ISAR2_EL1[27 .. 24] = 0b0000
        }
    };
    if HasArchVersion(ARMv9p2) then {
        SMIDR_EL1[31 .. 24] = 0b01000001;
        SMIDR_EL1[15 .. 15] = 0b1;
        ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 24, 0b0001)
    };
    if HasArchVersion(ARMv8p8) then {
        ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 36, 0b0001);
        ID_AA64PFR1_EL1 = SetSlice(4, ID_AA64PFR1_EL1, 28, 0b0001);
        ID_AA64ISAR2_EL1 = SetSlice(4, ID_AA64ISAR2_EL1, 16, 0b0001);
        ID_AA64ISAR2_EL1 = SetSlice(4, ID_AA64ISAR2_EL1, 20, 0b0001);
        if HaveStatisticalProfiling() then {
            ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 32, 0b0100)
        };
        ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 60, 0b0001);
        ID_DFR1_EL1 = SetSlice(4, ID_DFR1_EL1, 4, 0b0001);
        ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 0, 0b1010);
        ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 0, 0b1010);
        if not_bool(HaveEL(EL3)) & Slice(SCR, 0, 1) == 0b1 then {
            ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 4, 0b0000)
        } else {
            ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 4, Slice(ID_DFR0_EL1, 0, 4))
        };
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 52, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 52, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 56, 0b0001);
        ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 8, 0b1000);
        ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 24, 0b1000)
    };
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 24, 0b0001);
    ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 16, 0b0001);
    ID_DFR0_EL1 = SetSlice(4, ID_DFR0_EL1, 12, 0b0001);
    SCR_EL3 = SetSlice(1, SCR_EL3, 18, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 17, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 16, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 15, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 14, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 13, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 12, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 11, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 10, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 9, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 8, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 7, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 3, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 2, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 1, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 0, 0b0);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, 31, 0b0);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, if HaveVirtHostExt() & Slice(HCR_EL2, 34, 1) == 0b1 then
      28
    else
      20, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 49, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 52, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 50, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 44, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 43, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 42, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 41, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 40, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 38, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 37, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 36, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 33, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 32, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 31, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 30, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 29, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 28, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 27, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 26, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 25, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 24, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 23, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 22, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 21, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 20, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 19, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 18, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 17, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 16, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 15, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 14, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 13, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 12, 0b0);
    HCR_EL2 = SetSlice(2, HCR_EL2, 10, 0b00);
    HCR_EL2 = SetSlice(1, HCR_EL2, 9, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 8, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 7, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 6, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 5, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 4, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 3, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 2, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 1, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 0, 0b0);
    HSTR_EL2 = SetSlice(16, HSTR_EL2, 0, Zeros());
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 31, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 30, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 27, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 25, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 13, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 31, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 30, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 27, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 25, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 13, 0b0);
    CPACR_EL1 = SetSlice(1, CPACR_EL1, 28, 0b0);
    CPACR_EL1 = SetSlice(2, CPACR_EL1, 20, 0b00);
    CPACR_EL1 = SetSlice(2, CPACR_EL1, 16, 0b00);
    SCTLR_EL1 = SetSlice(1, SCTLR_EL1, 31, 0b0);
    SCTLR_EL1 = SetSlice(1, SCTLR_EL1, 30, 0b0);
    SCTLR_EL1 = SetSlice(1, SCTLR_EL1, 27, 0b0);
    SCTLR_EL1 = SetSlice(1, SCTLR_EL1, 25, 0b0);
    SCTLR_EL1 = SetSlice(1, SCTLR_EL1, 13, 0b0);
    SCTLR_EL3 = SetSlice(1, SCTLR_EL3, 31, 0b0);
    SCTLR_EL3 = SetSlice(1, SCTLR_EL3, 30, 0b0);
    SCTLR_EL3 = SetSlice(1, SCTLR_EL3, 27, 0b0);
    SCTLR_EL3 = SetSlice(1, SCTLR_EL3, 25, 0b0);
    SCTLR_EL3 = SetSlice(1, SCTLR_EL3, 13, 0b0);
    PMSIDR_EL1 = SetSlice(1, PMSIDR_EL1, 24, 0b1);
    PMSIDR_EL1 = SetSlice(1, PMSIDR_EL1, 6, 0b1);
    PMSIDR_EL1 = SetSlice(4, PMSIDR_EL1, 16, 0b0011);
    PMSIDR_EL1 = SetSlice(4, PMSIDR_EL1, 12, 0b0110);
    PMSIDR_EL1 = SetSlice(1, PMSIDR_EL1, 3, 0b1);
    PMSIDR_EL1 = SetSlice(1, PMSIDR_EL1, 2, 0b1);
    PMSIDR_EL1 = SetSlice(1, PMSIDR_EL1, 1, 0b1);
    PMSIDR_EL1 = SetSlice(1, PMSIDR_EL1, 0, 0b1);
    if EL2Enabled() then {
        MDCR_EL2 = SetSlice(1, MDCR_EL2, 14, 0b0);
        MDCR_EL2 = SetSlice(2, MDCR_EL2, 12, 0b10)
    };
    MDCR_EL2 = SetSlice(5, MDCR_EL2, 0, Slice(PMCR_EL0, 11, 5));
    ICC_SRE_EL3 = SetSlice(1, ICC_SRE_EL3, 0, 0b1);
    ICC_SRE_EL3 = SetSlice(1, ICC_SRE_EL3, 3, 0b1);
    ICC_SRE_EL1_S = SetSlice(1, ICC_SRE_EL1_S, 0, 0b1);
    ICC_SRE_EL1_NS = SetSlice(1, ICC_SRE_EL1_NS, 0, 0b1);
    ICC_SRE_EL2 = SetSlice(1, ICC_SRE_EL2, 0, 0b1);
    CTR_EL0 = SetSlice(4, CTR_EL0, 24, 0b0100);
    CTR_EL0 = SetSlice(4, CTR_EL0, 20, __exclusive_granule_size);
    CTR_EL0 = SetSlice(4, CTR_EL0, 16, 0b0100);
    CTR_EL0 = SetSlice(2, CTR_EL0, 14, 0b10);
    CTR_EL0 = SetSlice(4, CTR_EL0, 0, 0b0100);
    if HaveMTE2Ext() then {
        CTR_EL0 = SetSlice(6, CTR_EL0, 32, 0b000100)
    };
    if HaveMTE2Ext() then {
        GMID_EL1 = SetSlice(4, GMID_EL1, 0, __gmid_log2_block_size[3 .. 0])
    };
    ICH_VMCR_EL2 = SetSlice(3, ICH_VMCR_EL2, 21, 0b010);
    ICH_VMCR_EL2 = SetSlice(3, ICH_VMCR_EL2, 18, 0b011);
    ICC_CTLR_EL1_write() = SetSlice(1, ICC_CTLR_EL1_read(), 19, 0b1);
    ICC_CTLR_EL1_write() = SetSlice(3, ICC_CTLR_EL1_read(), 8, 0b100);
    ICC_CTLR_EL1_write() = SetSlice(1, ICC_CTLR_EL1_read(), 15, 0b1);
    ICC_CTLR_EL1_write() = SetSlice(3, ICC_CTLR_EL1_read(), 11, 0b001);
    ICV_CTLR_EL1 = SetSlice(1, ICV_CTLR_EL1, 19, 0b1);
    ICV_CTLR_EL1 = SetSlice(3, ICV_CTLR_EL1, 8, 0b100);
    ICV_CTLR_EL1 = SetSlice(3, ICV_CTLR_EL1, 11, 0b001);
    ICV_CTLR_EL1 = SetSlice(1, ICV_CTLR_EL1, 15, 0b1);
    ICH_VTR_EL2 = SetSlice(3, ICH_VTR_EL2, 29, 0b100);
    ICH_VTR_EL2 = SetSlice(3, ICH_VTR_EL2, 26, 0b100);
    ICH_VTR_EL2 = SetSlice(3, ICH_VTR_EL2, 23, 0b001);
    ICH_VTR_EL2 = SetSlice(1, ICH_VTR_EL2, 21, 0b1);
    CCSIDR_EL1 = SetSlice(24, CCSIDR_EL1, if HaveExtendedCacheSets() then 32 else 13, ZeroExtend(0xFF, 24));
    CCSIDR_EL1 = SetSlice(21, CCSIDR_EL1, 3, ZeroExtend(0x1, 21));
    CCSIDR_EL1 = SetSlice(3, CCSIDR_EL1, 0, 0b010);
    CCSIDR2_EL1 = SetSlice(24, CCSIDR2_EL1, 0, ZeroExtend(0xFF, 24));
    ID_PFR1_EL1 = SetSlice(4, ID_PFR1_EL1, 0, 0b0000);
    ID_PFR1_EL1 = SetSlice(4, ID_PFR1_EL1, 4, 0b0000);
    ID_PFR1_EL1 = SetSlice(4, ID_PFR1_EL1, 12, 0b0000);
    (OSLSR_EL1[3 .. 3] @ OSLSR_EL1[0 .. 0]) = 0b10;
    MDRAR_EL1 = SetSlice(2, MDRAR_EL1, 0, 0b11);
    MDRAR_EL1 = SetSlice(40, MDRAR_EL1, 12, ZeroExtend(0x22000, 40));
    EDDFR = SetSlice(4, EDDFR, 8, Slice(ID_AA64DFR0_EL1, 8, 4));
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
    return()
}

function AArch32_ResetControlRegisters cold_reset = {
    PSTATE.SS = 0b0;
    ResetControlRegisters(cold_reset);
}

function AArch64_ResetControlRegisters cold_reset = {
    PSTATE.ZA = 0b0;
    PSTATE.SM = 0b0;
    PSTATE.ALLINT = 0b0;
    ResetControlRegisters(cold_reset);
}

function SetResetVector value_name = {
    if not_bool(HaveAArch64()) then {
        if HaveEL(EL3) then {
            MVBAR = value_name[31 .. 1] @ 0b1
        } else {
            RVBAR = value_name[31 .. 1] @ 0b1
        }
    } else if HighestEL() == EL3 then {
        RVBAR_EL3 = value_name
    } else if HighestEL() == EL2 then {
        RVBAR_EL2 = value_name
    } else {
        RVBAR_EL1 = value_name
    };
    return()
}

function TakeReset(cold) = {
    assert(HighestEL() == EL1 | HighestEL() == EL2 | HighestEL() == EL3);
    EDSCR_write() = SetSlice(6, EDSCR_read(), 0, 0b000010); // Non-debug state
    if cold then {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 12, CFG_ID_AA64PFR0_EL1_EL3);
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 8, CFG_ID_AA64PFR0_EL1_EL2);
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 4, CFG_ID_AA64PFR0_EL1_EL1);
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 0, CFG_ID_AA64PFR0_EL1_EL0);
        RMR_EL3 = SetSlice(1, RMR_EL3, 0, CFG_RMR_AA64)
    };
    if Slice(RMR_EL3, 0, 1) == 0b1 then {
        __highest_el_aarch32 = false;
        SetResetVector(CFG_RVBAR);
        AArch64_TakeReset(cold)
    } else {
        match HighestEL() {
          ? if ? == EL3 => {
              assert(Slice(ID_AA64PFR0_EL1, 12, 4) == 0b0010)
          },
          ? if ? == EL2 => {
              assert(Slice(ID_AA64PFR0_EL1, 8, 4) == 0b0010)
          },
          ? if ? == EL1 => {
              assert(Slice(ID_AA64PFR0_EL1, 4, 4) == 0b0010)
          },
          _ => ()
        };
        __highest_el_aarch32 = true;
        if __ignore_rvbar_in_aarch32 then {
            SetResetVector(ZeroExtend(0x0, 64))
        } else {
            SetResetVector(CFG_RVBAR)
        };
        if HaveEL(EL3) then {
            SCR = SetSlice(1, SCR, 0, 0b0)
        };
        AArch32_TakeReset(cold)
    }
}
