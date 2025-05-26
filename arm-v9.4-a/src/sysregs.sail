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

function SPMEVCNTR_EL0_read (s, n) = {
    return(Zeros(64))
}

function SPMEVCNTR_EL0_set (s, n, value_name) = {
    return()
}

function SPMEVTYPER_EL0_read (s, n) = {
    return(Zeros(64))
}

function SPMEVTYPER_EL0_set (s, n, value_name) = {
    return()
}

function SPMEVFILTR_EL0_read (s, n) = {
    return(Zeros(64))
}

function SPMEVFILTR_EL0_set (s, n, value_name) = {
    return()
}

function SPMEVFILT2R_EL0_read (s, n) = {
    return(Zeros(64))
}

function SPMEVFILT2R_EL0_set (s, n, value_name) = {
    return()
}

function SPMOVSCLR_EL0_read s = {
    return(Zeros(64))
}

function SPMOVSCLR_EL0_set (s, value_name) = {
    return()
}

function SPMCFGR_EL1_read s = {
    return(Zeros(64))
}

function SPMCGCR_EL1_read s = {
    return(Zeros(64))
}

function SPMCNTENCLR_EL0_read s = {
    return(Zeros(64))
}

function SPMCNTENCLR_EL0_set (s, value_name) = {
    return()
}

function SPMCNTENSET_EL0_read s = {
    return(Zeros(64))
}

function SPMCNTENSET_EL0_set (s, value_name) = {
    return()
}

function SPMCR_EL0_read s = {
    return(Zeros(64))
}

function SPMCR_EL0_set (s, value_name) = {
    return()
}

function SPMDEVAFF_EL1_read s = {
    return(Zeros(64))
}

function SPMDEVARCH_EL1_read s = {
    return(Zeros(64))
}

function SPMIIDR_EL1_read s = {
    return(Zeros(64))
}

function SPMINTENCLR_EL1_read s = {
    return(Zeros(64))
}

function SPMINTENCLR_EL1_set (s, value_name) = {
    return()
}

function SPMINTENSET_EL1_read s = {
    return(Zeros(64))
}

function SPMINTENSET_EL1_set (s, value_name) = {
    return()
}

function SPMOVSSET_EL0_read s = {
    return(Zeros(64))
}

function SPMOVSSET_EL0_set (s, value_name) = {
    return()
}

function SPMROOTCR_EL3_read s = {
    return(Zeros(64))
}

function SPMROOTCR_EL3_set (s, value_name) = {
    return()
}

function SPMSCR_EL1_read s = {
    return(Zeros(64))
}

function SPMSCR_EL1_set (s, value_name) = {
    return()
}

function getISR () = {
    fiq_nmi : bool = undefined;
    fiq_pending : bool = undefined;
    irq_nmi : bool = undefined;
    irq_pending : bool = undefined;
    value_name : bits(32) = Zeros(32);
    value_name[8] = Bit(if IsPhysicalSErrorPending() then 0b1 else 0b0);
    (irq_pending, irq_nmi) = IRQPending();
    (fiq_pending, fiq_nmi) = FIQPending();
    if HaveFeatNMI() & not_bool(UsingAArch32()) then {
        value_name[10] = Bit(if irq_pending & irq_nmi then 0b1 else 0b0);
        value_name[9] = Bit(if fiq_pending & fiq_nmi then 0b1 else 0b0)
    };
    value_name[7] = Bit(if irq_pending then 0b1 else 0b0);
    value_name[6] = Bit(if fiq_pending then 0b1 else 0b0);
    if (PSTATE.EL == EL1 & EL2Enabled()) & HCR_EL2[TGE] == 0b0 then {
        if (HaveFeatNMI() & not_bool(UsingAArch32())) & IsHCRXEL2Enabled() then {
            if (HCR_EL2[IMO] & HCR_EL2[VI]) == 0b1 then {
                value_name[10] = Bit(HCRX_EL2[VINMI])
            };
            if (HCR_EL2[FMO] & HCR_EL2[VF]) == 0b1 then {
                value_name[9] = Bit(HCRX_EL2[VFNMI])
            };
            ()
        };
        if HCR_EL2[AMO] == 0b1 then {
            value_name[8] = Bit([value_name[8]] | HCR_EL2[VSE])
        };
        if HCR_EL2[IMO] == 0b1 then {
            value_name[7] = Bit(HCR_EL2[VI])
        };
        if HCR_EL2[FMO] == 0b1 then {
            value_name[6] = Bit(HCR_EL2[VF])
        };
        ()
    };
    return(value_name)
}

function genRandomNum isRNDRRS = {
    (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = 0b0000;
    let x : bits(128) = __cycle_count[127 .. 0];
    let y : bits(128) = (__cycle_count + 1)[127 .. 0];
    let w : bits(128) = (__cycle_count + 2)[127 .. 0];
    return(SHA256hash(x, y, w, true)[63 .. 0])
}

function getCacheID (level, data_cache) = {
    let 'range_min = level * 3;
    let cache_type : bits(3) = Slice(CLIDR_EL1.bits, range_min, 3);
    ccsidr_val : bits(64) = undefined;
    match cache_type {
      0b000 => {
          ccsidr_val = __UNKNOWN_bits(64)
      },
      0b001 => {
          ccsidr_val = if data_cache then __UNKNOWN_bits(64) else {
              assert(constraint((0 <= 'level & 'level < 7)));
              __ICACHE_CCSIDR_RESET[level]
          }
      },
      0b010 => {
          ccsidr_val = if not_bool(data_cache) then __UNKNOWN_bits(64) else {
              assert(constraint((0 <= 'level & 'level < 7)));
              __DCACHE_CCSIDR_RESET[level]
          }
      },
      0b011 => {
          ccsidr_val = if data_cache then {
              assert(constraint((0 <= 'level & 'level < 7)));
              __DCACHE_CCSIDR_RESET[level]
          } else {
              assert(constraint((0 <= 'level & 'level < 7)));
              __ICACHE_CCSIDR_RESET[level]
          }
      },
      0b100 => {
          assert(constraint((0 <= 'level & 'level < 7)));
          ccsidr_val = __DCACHE_CCSIDR_RESET[level]
      },
      _ => PatternMatchFailure("getCacheID")
    };
    return(ccsidr_val)
}

function CacheConfigRead cache_sel = {
    let data_cache : bool = if [cache_sel[0]] == 0b0 then true else false;
    let 'level = UInt(cache_sel[3 .. 1]);
    assert(level < 7);
    return(getCacheID(level, data_cache))
}

function AArch64_SysRegRead (op0, op1, crn, crm, op2, t) = {
    index : int = undefined;
    n : int = undefined;
    if (op0 == 3 & op1 == 3) & crn == 13 then {
        let 'n = UInt([crm[0]] @ op2[2 .. 0]);
        if crm[3 .. 1] == 0b010 | crm[3 .. 1] == 0b011 then {
            if n >= UInt(AMCGCR_EL0[CG0NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else if crm[3 .. 1] == 0b110 | crm[3 .. 1] == 0b111 then {
            if n >= UInt(AMCGCR_EL0[CG1NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else ()
    };
    if (((op0 == 3 & op1 == 3) & crn == 14) & (crm[3 .. 2] == 0b10 | crm[3 .. 2] == 0b11)) & (crm[1 .. 0] @ op2[2 .. 0]) != 0b11111 then {
        if UInt(crm[1 .. 0] @ op2[2 .. 0]) > GetNumEventCounters() - 1 | (EL2Enabled() & (PSTATE.EL == EL1 | PSTATE.EL == EL0 & (crm[3 .. 2] == 0b10 & (PMUSERENR_EL0[ER] @ PMUSERENR_EL0[EN]) != 0b00 | crm[3 .. 2] == 0b11 & PMUSERENR_EL0[EN] == 0b1))) & UInt(crm[1 .. 0] @ op2[2 .. 0]) > AArch64_GetNumEventCountersAccessible() - 1 then {
            if UInt(crm[1 .. 0] @ op2[2 .. 0]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            }
        };
        ()
    };
    if ((((op0 == 3 & op1 == 3) & crn == 9) & crm == 13) & (op2 == 1 | op2 == 2)) & PMSELR_EL0[SEL] != 0b11111 then {
        if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 | (EL2Enabled() & (PSTATE.EL == EL1 | PSTATE.EL == EL0 & (op2 == 2 & (PMUSERENR_EL0[ER] @ PMUSERENR_EL0[EN]) != 0b00 | op2 == 1 & PMUSERENR_EL0[EN] == 0b1))) & UInt(PMSELR_EL0[SEL]) > AArch64_GetNumEventCountersAccessible() - 1 then {
            if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            }
        };
        ()
    };
    let temp : bits(64) = X_read(t, 64);
    AArch64_AutoGen_SysRegRead(PSTATE.EL, op0[1 .. 0], op1[2 .. 0], crn[3 .. 0], op2[2 .. 0], crm[3 .. 0], t);
    if (((op0 == 3 & crn == 10) & crm == 5) & op2 == 0) & (op1 == 0 | op1 == 5) then {
        if HaveRME() & MPAMIDR_EL1[HAS_ALTSP] == 0b1 then {
            X_set(t, 64) = [X_read(t, 64) with 54 .. 54 = if not_bool(UsePrimarySpaceEL10()) then
              0b1
            else
              0b0]
        };
        ()
    };
    if (((op0 == 3 & crn == 10) & crm == 5) & op2 == 0) & op1 == 4 then {
        if HaveRME() & MPAMIDR_EL1[HAS_ALTSP] == 0b1 then {
            X_set(t, 64) = [X_read(t, 64) with 54 .. 54 = if not_bool(UsePrimarySpaceEL2()) then
              0b1
            else
              0b0]
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 0) & op2 == 7) & crm == 10 then {
        X_set(t, 64) = [X_read(t, 64) with 4 .. 4 = SPE_PMBIDR_P_Read()]
    };
    if (op0 == 3 & crn == 9) & (((op1 == 3 & op2 == 3) & (crm == 12 | crm == 14) | (op1 == 3 & (op2 == 1 | op2 == 2)) & crm == 12) | (op1 == 0 & (op2 == 1 | op2 == 2)) & crm == 14) then {
        let mask : bits(64) = PMUCounterMask();
        X_set(t, 64) = X_read(t, 64) & mask
    };
    if (((op0 == 3 & op1 == 3) & crn == 9) & crm == 13) & (op2 == 1 | op2 == 2) then {
        if op2 == 1 then {
            if ((EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & PMSELR_EL0[SEL] != 0b11111) & UInt(PMSELR_EL0[SEL]) > AArch64_GetNumEventCountersAccessible() - 1 then {
                if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 then {
                    X_set(t, 64) = temp;
                    throw(Error_Undefined())
                } else {
                    X_set(t, 64) = temp;
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                }
            } else if PMSELR_EL0[SEL] == 0b11111 then {
                X_set(t, 64) = PMCCFILTR_EL0.bits
            } else {
                let 'pmselr_el0 = UInt(PMSELR_EL0[SEL]);
                assert(pmselr_el0 < 31);
                X_set(t, 64) = PMEVTYPER_EL0[pmselr_el0].bits
            }
        };
        if op2 == 2 then {
            if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 & PMSELR_EL0[SEL] != 0b11111 | (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & UInt(PMSELR_EL0[SEL]) > AArch64_GetNumEventCountersAccessible() - 1 then {
                if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 then {
                    X_set(t, 64) = temp;
                    throw(Error_Undefined())
                } else {
                    X_set(t, 64) = temp;
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                }
            } else {
                let 'pmselr_el0 = UInt(PMSELR_EL0[SEL]);
                assert(pmselr_el0 < 31);
                X_set(t, 64) = PMEVCNTR_EL0[pmselr_el0]
            }
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 3) & op2 == 0) & crm == 12 then {
        X_set(t, 64) = [X_read(t, 64) with 15 .. 11 = AArch64_GetNumEventCountersAccessible()[4 .. 0]]
    };
    if ((op0 == 3 & crn == 14) & op1 == 3) & (crm[3 .. 2] == 0b10 | crm[3 .. 2] == 0b11 & (crm[1 .. 0] @ op2[2 .. 0]) != 0b11111) then {
        if UInt(crm[1 .. 0] @ op2[2 .. 0]) > GetNumEventCounters() - 1 & (crm[1 .. 0] @ op2[2 .. 0]) != 0b11111 | (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & UInt(crm[1 .. 0] @ op2[2 .. 0]) > AArch64_GetNumEventCountersAccessible() - 1 then {
            if UInt(crm[1 .. 0] @ op2[2 .. 0]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else {
                X_set(t, 64) = temp;
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            }
        };
        ()
    };
    if ((op0 == 2 & op1 == 0) & crn == 7) & op2 == 6 then {
        if crm == 8 then {
            X_set(t, 64) = [X_read(t, 64) with 7 .. 0 = 0b11111111];
            return()
        };
        if crm == 9 then {
            X_set(t, 64) = [X_read(t, 64) with 7 .. 0 = DBGCLAIMCLR_EL1.bits[7 .. 0]];
            return()
        };
        ()
    };
    if ((op0 == 2 & op1 == 1) & crn == 7) & op2 == 6 then {
        if crm == 8 then {
            X_set(t, 64) = [X_read(t, 64) with 31 .. 0 = __trcclaim_tags];
            return()
        };
        if crm == 9 then {
            X_set(t, 64) = [X_read(t, 64) with 31 .. 0 = __trcclaim_tags];
            return()
        };
        ()
    };
    if (((op0 == 3 & op1 == 0) & crn == UInt(0xa)) & op2 == 0) & crm == 5 then {
        if CurrentSecurityState() == SS_Secure then {
            X_set(t, 64) = [X_read(t, 64) with 60 .. 60 = MPAM3_EL3_read()[FORCE_NS]]
        };
        return()
    };
    if (((op0 == 3 & crn == UInt(0xc)) & op1 == 0) & op2 == 0) & crm == 1 then {
        X_set(t, 64) = ZeroExtend(getISR(), 64);
        return()
    };
    if (((op0 == 3 & crn == 0) & op1 == 1) & (op2 == 0 | op2 == 2)) & crm == 0 then {
        if op2 == 0 then {
            X_set(t, 64) = CacheConfigRead(CSSELR_EL1.bits[3 .. 0]);
            return()
        } else if op2 == 2 then {
            X_set(t, 64) = ZeroExtend(CacheConfigRead(CSSELR_EL1.bits[3 .. 0])[63 .. 32], 64);
            return()
        } else ()
    };
    if (((op0 == 3 & crn == 0) & op1 == 3) & op2 == 7) & crm == 0 then {
        if PSTATE.EL == EL0 then {
            if IsInHost() then {
                X_set(t, 64) = [X_read(t, 64) with 4 .. 4 = if SCTLR_EL2[DZE] == 0b0 then
                  0b1
                else
                  0b0]
            } else {
                X_set(t, 64) = [X_read(t, 64) with 4 .. 4 = if SCTLR_EL1[DZE] == 0b0 | EL2Enabled() & HCR_EL2[TDZ] == 0b1 then
                  0b1
                else
                  0b0]
            }
        } else if PSTATE.EL == EL1 then {
            X_set(t, 64) = [X_read(t, 64) with 4 .. 4 = if EL2Enabled() & HCR_EL2[TDZ] == 0b1 then
              0b1
            else
              0b0]
        } else ();
        return()
    };
    if AArch64_CheckNVCondsIfCurrentEL(op0, op1, crn, crm, op2) then {
        X_set(t, 64) = [X_read(t, 64) with 3 .. 2 = 0b10]
    };
    if (((op0 == 3 & crn == 2) & crm == 4) & op1 == 3) & (op2 == 0 | op2 == 1) then {
        X_set(t, 64) = if op2 == 0 then genRandomNum(false) else
          genRandomNum(true)
    };
    if ((op0 == 2 & op1 == 1) & crn == 8) & (op2 == 0 | op2 == 1 | op2 == 2 | op2 == 4 | op2 == 5 | op2 == 6) then {
        let 'recordIdx = UInt((BRBFCR_EL1[BANK] @ [op2[2]]) @ crm[3 .. 0]);
        if recordIdx < GetBRBENumRecords() then {
            if op2 == 0 | op2 == 4 then {
                assert(constraint((0 <= 'recordIdx & 'recordIdx < 64)));
                X_set(t, 64) = Records_INF[recordIdx].bits
            };
            if op2 == 1 | op2 == 5 then {
                assert(constraint((0 <= 'recordIdx & 'recordIdx < 64)));
                X_set(t, 64) = Records_SRC[recordIdx].bits
            };
            if op2 == 2 | op2 == 6 then {
                assert(constraint((0 <= 'recordIdx & 'recordIdx < 64)));
                X_set(t, 64) = Records_TGT[recordIdx].bits
            };
            ()
        } else {
            X_set(t, 64) = Zeros(64)
        }
    };
    if (((op0 == 3 & crn == 5) & op1 == 0) & op2 == 0) & crm == 4 then {
        if UInt(ERRIDR_EL1[NUM]) == UInt(0x0) | UInt(ERRSELR_EL1[SEL]) >= UInt(ERRIDR_EL1[NUM]) then {
            X_set(t, 64) = Zeros(64)
        } else {
            let 'index = UInt(ERRSELR_EL1[SEL]);
            assert(constraint((0 <= 'index & 'index < 4)));
            X_set(t, 64) = ERRnFR[index].bits
        }
    };
    if (((op0 == 2 & crn == 7) & op1 == 0) & op2 == 6) & crm == 14 then {
        if HaveEL(EL3) then {
            if ExternalInvasiveDebugEnabled() then {
                X_set(t, 64) = [X_read(t, 64) with 1 .. 0 = 0b11]
            } else {
                X_set(t, 64) = [X_read(t, 64) with 1 .. 0 = 0b10]
            };
            X_set(t, 64) = [X_read(t, 64) with 3 .. 2 = 0b11];
            if ExternalSecureInvasiveDebugEnabled() then {
                X_set(t, 64) = [X_read(t, 64) with 5 .. 4 = 0b11]
            } else {
                X_set(t, 64) = [X_read(t, 64) with 5 .. 4 = 0b10]
            };
            X_set(t, 64) = [X_read(t, 64) with 7 .. 6 = X_read(t, 64)[5 .. 4]]
        };
        return()
    };
    if (((op0 == 2 & crn == 0) & op1 == 3) & op2 == 0) & crm == 5 then {
        DBGDSCRint_write() = [DBGDSCRint_read() with RXfull = 0b0];
        MDCCSR_EL0[RXfull] = 0b0;
        DBGDSCRext_write() = [DBGDSCRext_read() with RXfull = 0b0];
        EDSCR_write() = [EDSCR_read() with RXfull = 0b0]
    };
    if (((op0 == 2 & crn == 0) & op1 == 3) & op2 == 0) & crm == 4 then {
        DBGDSCRint_write() = [DBGDSCRint_read() with RXfull = 0b0];
        MDCCSR_EL0[RXfull] = 0b0;
        DBGDSCRext_write() = [DBGDSCRext_read() with RXfull = 0b0];
        EDSCR_write() = [EDSCR_read() with RXfull = 0b0];
        X_set(t, 64) = SetSlice(32, X_read(t, 64), 32, Slice(DBGDTRTX_EL0, 0, 32));
        X_set(t, 64) = SetSlice(32, X_read(t, 64), 0, Slice(DBGDTRRX_EL0, 0, 32))
    };
    if (((op0 == 3 & crn == 12) & op1 == 4) & op2 == 7) & crm == 11 then {
        if PSTATE.EL == EL2 | PSTATE.EL == EL3 then {
            X_set(t, 64) = [X_read(t, 64) with 26 .. 24 = 0b000]
        };
        ()
    };
    if (((op0 == 3 & crn == 4) & op1 == 0) & op2 == 0) & crm == 6 then {
        X_set(t, 64) = [X_read(t, 64) with 2 .. 0 = 0b000]
    };
    if (((op0 == 3 & crn == 1) & op1 == 4) & op2 == 0) & crm == 1 then {
        if not_bool(ELUsingAArch32(EL1)) & PSTATE.EL != EL1 then {
            X_set(t, 64) = [X_read(t, 64) with 31 .. 31 = 0b1]
        };
        ()
    };
    if (((op0 == 3 & crn == 12) & op1 == 6) & op2 == 2) & crm == 0 then {
        if ID_AA64PFR0_EL1[EL3] == 0b0001 then {
            X_set(t, 64) = [X_read(t, 64) with 0 .. 0 = 0b1]
        };
        ()
    };
    return()
}

function AArch64_SysRegWrite (op0, op1, crn, crm, op2, t) = {
    n : int = undefined;
    tempxt : bits(64) = X_read(t, 64);
    if ((op0 == 2 & crn == 0) & op1 == 0) & op2 == 5 then {
        tempxt[8] = Bit([tempxt[7]]);
        tempxt[6] = Bit([tempxt[5]])
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 4) & crm == 12 then {
        tempxt[19] = Bit(ICV_CTLR_EL1[ExtRange]);
        tempxt[13 .. 11] = ICV_CTLR_EL1[IDbits];
        tempxt[10 .. 8] = ICV_CTLR_EL1[PRIbits];
        tempxt[15] = Bit(ICV_CTLR_EL1[A3V]);
        tempxt[14] = Bit(ICV_CTLR_EL1[SEIS])
    };
    if (((op0 == 3 & crn == 12) & op1 == 6) & op2 == 4) & crm == 12 then {
        tempxt[19] = Bit(ICC_CTLR_EL3[ExtRange]);
        tempxt[13 .. 11] = ICC_CTLR_EL3[IDbits];
        tempxt[10 .. 8] = ICC_CTLR_EL3[PRIbits];
        tempxt[17] = Bit(ICC_CTLR_EL3[nDS]);
        tempxt[15] = Bit(ICC_CTLR_EL3[A3V]);
        tempxt[14] = Bit(ICC_CTLR_EL3[SEIS])
    };
    if (((op0 == 3 & crn == 12) & op1 == 4) & op2 == 7) & crm == 11 then {
        if PSTATE.EL == EL2 | PSTATE.EL == EL3 then {
            if UInt(tempxt[23 .. 21]) < 6 - UInt(ICH_VTR_EL2[PREbits]) then {
                tempxt[23 .. 21] = (6 - UInt(ICH_VTR_EL2[PREbits]))[2 .. 0]
            };
            if CurrentSecurityState() == SS_Secure then {
                if UInt(tempxt[20 .. 18]) < 6 - UInt(ICH_VTR_EL2[PREbits]) then {
                    tempxt[20 .. 18] = (6 - UInt(ICH_VTR_EL2[PREbits]))[2 .. 0]
                };
                ()
            } else {
                if UInt(tempxt[20 .. 18]) < 7 - UInt(ICH_VTR_EL2[PREbits]) then {
                    tempxt[20 .. 18] = (7 - UInt(ICH_VTR_EL2[PREbits]))[2 .. 0]
                };
                ()
            };
            if ICC_SRE_EL1_NS[SRE] == 0b1 then {
                tempxt[3 .. 2] = 0b10
            };
            ()
        };
        ()
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 3) & crm == 8 then {
        if UInt(tempxt[2 .. 0]) < 6 - UInt(ICH_VTR_EL2[PREbits]) then {
            tempxt[2 .. 0] = (6 - UInt(ICH_VTR_EL2[PREbits]))[2 .. 0]
        };
        ()
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 3) & crm == 12 then {
        if ICV_CTLR_EL1[CBPR] == 0b0 then {
            if CurrentSecurityState() == SS_Secure then {
                if UInt(tempxt[2 .. 0]) < 6 - UInt(ICH_VTR_EL2[PREbits]) then {
                    tempxt[2 .. 0] = (6 - UInt(ICH_VTR_EL2[PREbits]))[2 .. 0]
                };
                ()
            } else {
                if UInt(tempxt[2 .. 0]) < 7 - UInt(ICH_VTR_EL2[PREbits]) then {
                    tempxt[2 .. 0] = (7 - UInt(ICH_VTR_EL2[PREbits]))[2 .. 0]
                };
                ()
            }
        } else {
            tempxt[2 .. 0] = ICV_BPR1_EL1[BinaryPoint]
        }
    };
    if (op0 == 3 & op1 == 3) & crn == 13 then {
        let 'n = UInt([crm[0]] @ op2[2 .. 0]);
        if crm[3 .. 1] == 0b010 | crm[3 .. 1] == 0b011 then {
            if n >= UInt(AMCGCR_EL0[CG0NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else if crm[3 .. 1] == 0b110 | crm[3 .. 1] == 0b111 then {
            if n >= UInt(AMCGCR_EL0[CG1NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else ()
    };
    let mask : bits(64) = PMUCounterMask();
    if (((op0 == 3 & crn == 9) & op1 == 3) & op2 == 3) & (crm == 12 | crm == 14) then {
        if crm == 12 then {
            tempxt = PMOVSSET_EL0.bits & not_vec(tempxt & mask)
        };
        if crm == 14 then {
            tempxt = PMOVSSET_EL0.bits | tempxt & mask
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 3) & (op2 == 1 | op2 == 2)) & crm == 12 then {
        if op2 == 2 then {
            tempxt = PMCNTENSET_EL0.bits & not_vec(tempxt & mask)
        };
        if op2 == 1 then {
            tempxt = PMCNTENSET_EL0.bits | tempxt & mask
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 0) & (op2 == 1 | op2 == 2)) & crm == 14 then {
        if op2 == 2 then {
            tempxt = PMINTENSET_EL1.bits & not_vec(tempxt & mask)
        };
        if op2 == 1 then {
            tempxt = PMINTENSET_EL1.bits | tempxt & mask
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 3) & op2 == 0) & crm == 12 then {
        if [tempxt[3]] == 0b1 & PMCR_EL0[D] == 0b0 then {
            __clock_divider = 63
        };
        ()
    };
    if ((op0 == 3 & crn == 14) & op1 == 3) & (crm[3 .. 2] == 0b10 | crm[3 .. 2] == 0b11 & (crm[1 .. 0] @ op2[2 .. 0]) != 0b11111) then {
        if UInt(crm[1 .. 0] @ op2[2 .. 0]) > GetNumEventCounters() - 1 & (crm[1 .. 0] @ op2[2 .. 0]) != 0b11111 | ((EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & PMUSERENR_EL0[EN] == 0b1) & UInt(crm[1 .. 0] @ op2[2 .. 0]) > AArch64_GetNumEventCountersAccessible() - 1 then {
            if UInt(crm[1 .. 0] @ op2[2 .. 0]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            }
        };
        ()
    };
    if (((op0 == 3 & op1 == 3) & crn == 9) & crm == 13) & (op2 == 2 | op2 == 1 & PMSELR_EL0[SEL] != 0b11111) then {
        if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 & PMSELR_EL0[SEL] != 0b11111 | ((EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & PMUSERENR_EL0[EN] == 0b1) & UInt(PMSELR_EL0[SEL]) > AArch64_GetNumEventCountersAccessible() - 1 then {
            if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            }
        };
        ()
    };
    if ((op0 == 2 & op1 == 0) & crn == 7) & op2 == 6 then {
        if crm == 8 then {
            tempxt[7 .. 0] = DBGCLAIMCLR_EL1.bits[7 .. 0] | tempxt[7 .. 0]
        };
        if crm == 9 then {
            tempxt[7 .. 0] = DBGCLAIMCLR_EL1.bits[7 .. 0] & not_vec(tempxt[7 .. 0])
        };
        ()
    };
    tempxt2 : bits(64) = undefined;
    restore_xt : bool = undefined;
    if tempxt != X_read(t, 64) then {
        tempxt2 = X_read(t, 64);
        X_set(t, 64) = tempxt;
        restore_xt = true
    } else {
        restore_xt = false
    };
    AArch64_AutoGen_SysRegWrite(PSTATE.EL, op0[1 .. 0], op1[2 .. 0], crn[3 .. 0], op2[2 .. 0], crm[3 .. 0], t);
    if restore_xt then {
        X_set(t, 64) = tempxt2
    };
    if (((op0 == 2 & op1 == 0) & crn == 7) & op2 == 6) & crm == 8 then {
        DBGCLAIMCLR_EL1.bits[7 .. 0] = tempxt[7 .. 0]
    };
    if (((crm == 0 & crn == 1) & op0 == 2) & op1 == 0) & op2 == 4 then {
        if OSLSR_EL1[OSLK] == 0b1 & OSLAR_EL1[OSLK] == 0b0 then {
            CheckOSUnlockCatch()
        };
        OSLSR_EL1[OSLK] = OSLAR_EL1[OSLK];
        EDPRSR[OSLK] = OSLSR_EL1[OSLK];
        DBGOSLSR_write() = [DBGOSLSR_read() with OSLK = OSLSR_EL1[OSLK]]
    };
    if ((op0 == 2 & op1 == 1) & crn == 7) & op2 == 6 then {
        if crm == 8 then {
            __trcclaim_tags = __trcclaim_tags | tempxt[31 .. 0];
            return()
        };
        if crm == 9 then {
            __trcclaim_tags = __trcclaim_tags & not_vec(tempxt[31 .. 0]);
            return()
        };
        ()
    };
    if ((((op0 == 3 & crn == UInt(0xc)) & ((op1 == 6 | op1 == 4) | op1 == 0)) & op2 == 2) & crm == 0) & [tempxt[1]] == 0b1 then {
        TakeReset(false)
    };
    if (((op0 == 3 & crn == 9) & op1 == 3) & op2 == 3) & (crm == 12 | crm == 14) then {
        if crm == 12 then {
            PMOVSSET_EL0 = Mk_PMOVSSET_EL0_Type(tempxt)
        };
        if crm == 14 then {
            PMOVSCLR_EL0 = Mk_PMOVSCLR_EL0_Type(tempxt)
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 3) & (op2 == 1 | op2 == 2)) & crm == 12 then {
        if op2 == 2 then {
            PMCNTENSET_EL0 = Mk_PMCNTENSET_EL0_Type(tempxt)
        };
        if op2 == 1 then {
            PMCNTENCLR_EL0 = Mk_PMCNTENCLR_EL0_Type(tempxt)
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 0) & (op2 == 1 | op2 == 2)) & crm == 14 then {
        if op2 == 2 then {
            PMINTENSET_EL1 = Mk_PMINTENSET_EL1_Type(tempxt)
        };
        if op2 == 1 then {
            PMINTENCLR_EL1 = Mk_PMINTENCLR_EL1_Type(tempxt)
        };
        ()
    };
    if (((op0 == 3 & crn == 9) & op1 == 3) & op2 == 0) & crm == 12 then {
        if [tempxt[2]] == 0b1 then {
            PMCCNTR_EL0 = Mk_PMCCNTR_EL0_Type(Zeros(64))
        };
        if [tempxt[1]] == 0b1 then {
            AArch64_ClearEventCounters()
        };
        ()
    };
    if (((op0 == 3 & op1 == 3) & crn == 9) & crm == 13) & (op2 == 1 | op2 == 2) then {
        if op2 == 1 then {
            if PMSELR_EL0[SEL] == 0b11111 then {
                PMCCFILTR_EL0 = __get_PMCCFILTR_EL0(Mk_PMCCFILTR_EL0_Type(tempxt))
            } else {
                let 'pmselr_el0 = UInt(PMSELR_EL0[SEL]);
                assert(pmselr_el0 < 31);
                PMEVTYPER_EL0[pmselr_el0] = __get_PMEVTYPER_EL0(Mk_PMEVTYPER_EL0_Type(tempxt))
            }
        };
        if op2 == 2 then {
            let 'pmselr_el0 = UInt(PMSELR_EL0[SEL]);
            assert(pmselr_el0 < 31);
            PMEVCNTR_EL0[pmselr_el0] = tempxt
        };
        ()
    };
    if ((op0 == 3 & op1 == 3) & crn == 14) & crm[3 .. 2] == 0b11 then {
        let 'index = UInt(crm[1 .. 0] @ op2[2 .. 0]);
        if index == 31 then {
            PMCCFILTR_EL0 = __get_PMCCFILTR_EL0(Mk_PMCCFILTR_EL0_Type(tempxt))
        } else {
            PMEVTYPER_EL0[index] = __get_PMEVTYPER_EL0(Mk_PMEVTYPER_EL0_Type(tempxt))
        }
    };
    if (((op0 == 3 & crn == 9) & op1 == 3) & op2 == 4) & crm == 12 then {
        AArch64_PMUSwIncrement(tempxt[31 .. 0])
    };
    if (((op0 == 2 & crn == 0) & op1 == 3) & op2 == 0) & crm == 5 then {
        DBGDSCRint_write() = [DBGDSCRint_read() with TXfull = 0b1];
        MDCCSR_EL0[TXfull] = 0b1;
        DBGDSCRext_write() = [DBGDSCRext_read() with TXfull = 0b1];
        EDSCR_write() = [EDSCR_read() with TXfull = 0b1]
    };
    if (((op0 == 2 & crn == 0) & op1 == 3) & op2 == 0) & crm == 4 then {
        DBGDSCRint_write() = [DBGDSCRint_read() with TXfull = 0b1];
        MDCCSR_EL0[TXfull] = 0b1;
        DBGDSCRext_write() = [DBGDSCRext_read() with TXfull = 0b1];
        EDSCR_write() = [EDSCR_read() with TXfull = 0b1];
        DBGDTRTX_EL0[31 .. 0] = Slice(DBGDTR_EL0_read__1().bits, 0, 32);
        DBGDTRRX_EL0[31 .. 0] = Slice(DBGDTR_EL0_read__1().bits, 32, 32)
    };
    if (((op0 == 3 & crn == 12) & op1 == 4) & op2 == 7) & crm == 11 then {
        ICV_PMR_EL1[Priority] = ICH_VMCR_EL2[VPMR];
        ICV_BPR0_EL1[BinaryPoint] = ICH_VMCR_EL2[VBPR0];
        ICV_BPR1_EL1[BinaryPoint] = ICH_VMCR_EL2[VBPR1];
        ICV_IGRPEN0_EL1[Enable] = ICH_VMCR_EL2[VENG0];
        ICV_IGRPEN1_EL1[Enable] = ICH_VMCR_EL2[VENG1];
        ICV_CTLR_EL1[EOImode] = ICH_VMCR_EL2[VEOIM];
        ICV_CTLR_EL1[CBPR] = ICH_VMCR_EL2[VCBPR]
    };
    if (((op0 == 3 & crn == 4) & op1 == 0) & op2 == 0) & crm == 6 then {
        ICH_VMCR_EL2[VPMR] = ICV_PMR_EL1[Priority]
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 3) & crm == 8 then {
        ICH_VMCR_EL2[VBPR0] = ICV_BPR0_EL1[BinaryPoint]
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 3) & crm == 12 then {
        ICH_VMCR_EL2[VBPR1] = ICV_BPR1_EL1[BinaryPoint]
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 4) & crm == 12 then {
        ICH_VMCR_EL2[VEOIM] = ICV_CTLR_EL1[EOImode];
        ICH_VMCR_EL2[VCBPR] = ICV_CTLR_EL1[CBPR]
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 6) & crm == 12 then {
        ICH_VMCR_EL2[VENG0] = ICV_IGRPEN0_EL1[Enable]
    };
    if (((op0 == 3 & crn == 12) & op1 == 0) & op2 == 7) & crm == 12 then {
        ICH_VMCR_EL2[VENG1] = ICV_IGRPEN1_EL1[Enable]
    };
    return()
}

function AArch64_SysInstr (op0, op1, crn, crm, op2, t) = {
    AArch64_AutoGen_SysOpsWrite(PSTATE.EL, op0[1 .. 0], op1[2 .. 0], crn[3 .. 0], op2[2 .. 0], crm[3 .. 0], t)
}

function AArch64_SysInstrWithResult (op0, op1, crn, crm, op2, t) = {
    AArch64_AutoGen_SysInstrWithResult(PSTATE.EL, op0[1 .. 0], op1[2 .. 0], crn[3 .. 0], op2[2 .. 0], crm[3 .. 0], t)
}

function AArch64_UnallocatedSysRegAccess (op0, op1, crn, op2, crm, read, t) = {
    rcs_el0_trap : bool = undefined;
    tid3_trap : bool = false;
    if ((PSTATE.EL == EL1 & read) & EL2Enabled()) & HCR_EL2[TID3] == 0b1 then {
        tid3_trap = if HaveFGTExt() then true else
          __IMPDEF_boolean("Unallocated encodings trapped by HCR_EL2.TID3")
    };
    if (PSTATE.EL == EL1 | PSTATE.EL == EL2 | PSTATE.EL == EL3) & read then {
        if (op0 == 0b11 & op1 == 0b000) & crn == 0b0000 then {
            if crm == 0b0010 & op2 == 0b111 then {
                if tid3_trap then {
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                } else {
                    X_set(t, 64) = Zeros(64);
                    return()
                }
            } else if crm == 0b0011 & (op2 == 0b011 | op2 == 0b101 | op2 == 0b110 | op2 == 0b111) then {
                if tid3_trap then {
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                } else {
                    X_set(t, 64) = Zeros(64);
                    return()
                }
            } else if crm == 0b0100 & (op2 == 0b010 | op2 == 0b011 | op2 == 0b101 | op2 == 0b110 | op2 == 0b111) then {
                if tid3_trap then {
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                } else {
                    X_set(t, 64) = Zeros(64);
                    return()
                }
            } else if crm == 0b0101 & (op2 == 0b010 | op2 == 0b011 | op2 == 0b110 | op2 == 0b111) then {
                if tid3_trap then {
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                } else {
                    X_set(t, 64) = Zeros(64);
                    return()
                }
            } else if crm == 0b0110 & (op2 == 0b010 | op2 == 0b011 | op2 == 0b100 | op2 == 0b101 | op2 == 0b110 | op2 == 0b111) then {
                if tid3_trap then {
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                } else {
                    X_set(t, 64) = Zeros(64);
                    return()
                }
            } else if crm == 0b0111 & (op2 == 0b011 | op2 == 0b100 | op2 == 0b101 | op2 == 0b110 | op2 == 0b111) then {
                if tid3_trap then {
                    AArch64_SystemAccessTrap(EL2, UInt(0x18))
                } else {
                    X_set(t, 64) = Zeros(64);
                    return()
                }
            } else ()
        };
        ()
    };
    let in_feature_space : bool = ((op0 == 0b11 & (match op1 {
      [bitzero, bitzero, _] => true,
      0b011 => true,
      _ => false
    }) : bool) & crn == 0b0000) & (match crm {
      [bitzero, _, _, _] => true,
      _ => false
    }) : bool;
    ec_val : int = UInt(0x0);
    if HaveIDSExt() then {
        ec_val = UInt(0x18)
    };
    let 'ec_val = ec_val;
    if in_feature_space & read then {
        if PSTATE.EL == EL0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & HCR_EL2[TGE] == 0b1 then {
                AArch64_SystemAccessTrap(EL2, ec_val)
            } else {
                AArch64_SystemAccessTrap(EL1, ec_val)
            }
        } else if PSTATE.EL == EL1 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & HCR_EL2[TID3] == 0b1 then {
                AArch64_SystemAccessTrap(EL2, ec_val)
            } else {
                AArch64_SystemAccessTrap(EL1, ec_val)
            }
        } else if PSTATE.EL == EL2 then {
            AArch64_SystemAccessTrap(EL2, ec_val)
        } else if PSTATE.EL == EL3 then {
            AArch64_SystemAccessTrap(EL3, ec_val)
        } else ()
    };
    if (HaveFeatTIDCP1() & PSTATE.EL == EL0) & (match crn {
      [bitone, _, bitone, bitone] => true,
      _ => false
    }) : bool then {
        if not_bool(IsInHost()) & SCTLR_EL1[TIDCP] == 0b1 then {
            if EL2Enabled() & HCR_EL2[TGE] == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        };
        if IsInHost() & SCTLR_EL2[TIDCP] == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        };
        ()
    };
    if ((((PSTATE.EL == EL0 | PSTATE.EL == EL1) & EL2Enabled()) & HCR_EL2[TIDCP] == 0b1) & (op0 == 0b01 | op0 == 0b11)) & (crn == 0b1011 | crn == 0b1111) then {
        let rcs_el0_trap : bool = __IMPDEF_boolean("Reserved Control Space EL0 Trapped");
        if PSTATE.EL == EL1 | rcs_el0_trap then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        };
        ()
    };
    if (Slice(op0, 0, 2) == 0b01 | Slice(op0, 0, 2) == 0b11) & (Slice(crn, 0, 4) == 0b1011 | Slice(crn, 0, 4) == 0b1111) then {
        throw(Error_ImplementationDefined(""))
    };
    let rcs_el0_trap = rcs_el0_trap;
    throw(Error_Undefined())
}

function AArch64_SysRegRead128 (op0, op1, crn, crm, op2, t, t2) = {
    AArch64_AutoGen_SysRegRead128(PSTATE.EL, op0[1 .. 0], op1[2 .. 0], crn[3 .. 0], op2[2 .. 0], crm[3 .. 0], t, t2);
    return()
}

function AArch64_SysRegWrite128 (op0, op1, crn, crm, op2, t, t2) = {
    AArch64_AutoGen_SysRegWrite128(PSTATE.EL, op0[1 .. 0], op1[2 .. 0], crn[3 .. 0], op2[2 .. 0], crm[3 .. 0], t, t2);
    return()
}

function AArch64_SysInstr128 (op0, op1, crn, crm, op2, t, t2) = {
    AArch64_AutoGen_SysOpsWrite128(PSTATE.EL, op0[1 .. 0], op1[2 .. 0], crn[3 .. 0], op2[2 .. 0], crm[3 .. 0], t, t2);
    return()
}

function AArch32_SysRegRead (cp_num, instr, address) = {
    let CRd : bits(4) = instr[15 .. 12];
    if CRd == 0b0101 & cp_num == UInt(0xE) then {
        AArch32_STC(cp_num[3 .. 0], CRd, address)
    };
    ()
}

function AArch32_SysRegRead__1 (cp_num, instr, t) = {
    el : bits(2) = undefined;
    index : int = undefined;
    n : int = undefined;
    let (_, __tup_1 : bits(2)) = ELFromM32(PSTATE.M) in
      {
          el = __tup_1
      };
    let opc1 : bits(3) = Slice(instr, 21, 3);
    let CRn : bits(4) = Slice(instr, 16, 4);
    let CRm : bits(4) = Slice(instr, 0, 4);
    opc2 : bits(3) = Slice(instr, 5, 3);
    if (((cp_num == 15 & opc1 == 0b000) & (opc2 == 0b100 | opc2 == 0b111)) & CRn == 0b0000) & CRm == 0b0000 then {
        opc2 = 0b000
    };
    if (cp_num == 15 & opc1 == 0b000) & CRn == 0b1101 then {
        let 'n = UInt([CRm[0]] @ opc2);
        if CRm[3 .. 1] == 0b011 then {
            if n >= UInt(AMCGCR_read()[CG0NC]) then {
                throw(Error_Undefined())
            };
            ()
        };
        if CRm[3 .. 1] == 0b111 then {
            if n >= UInt(AMCGCR_read()[CG1NC]) then {
                throw(Error_Undefined())
            };
            ()
        };
        ()
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b1110) & (CRm[3 .. 2] == 0b10 | CRm[3 .. 2] == 0b11)) & (CRm[1 .. 0] @ opc2[2 .. 0]) != 0b11111 then {
        if UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > GetNumEventCounters() - 1 | (EL2Enabled() & (PSTATE.EL == EL1 | PSTATE.EL == EL0 & (CRm[3 .. 2] == 0b10 & (PMUSERENR_EL0[ER] @ PMUSERENR_EL0[EN]) != 0b00 | CRm[3 .. 2] == 0b11 & PMUSERENR_EL0[EN] == 0b1))) & UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > AArch32_GetNumEventCountersAccessible() - 1 then {
            if UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else if ELUsingAArch32(EL2) then {
                AArch32_TakeHypTrapException(UInt(0x03))
            } else {
                AArch64_AArch32SystemAccessTrap(EL2, UInt(0x03))
            }
        };
        ()
    };
    if ((((cp_num == 15 & opc1 == 0b000) & CRn == 0b1001) & CRm == 0b1101) & (opc2 == 0b001 | opc2 == 0b010)) & PMSELR_EL0[SEL] != 0b11111 then {
        if UInt(PMSELR_EL0[SEL]) > GetNumEventCounters() - 1 | (EL2Enabled() & (PSTATE.EL == EL1 | PSTATE.EL == EL0 & (opc2 == 0b010 & (PMUSERENR_EL0[ER] @ PMUSERENR_EL0[EN]) != 0b00 | opc2 == 0b001 & PMUSERENR_EL0[EN] == 0b1))) & UInt(PMSELR_read()[SEL]) > AArch32_GetNumEventCountersAccessible() - 1 then {
            if UInt(PMSELR_read()[SEL]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else if ELUsingAArch32(EL2) then {
                AArch32_TakeHypTrapException(UInt(0x03))
            } else {
                AArch64_AArch32SystemAccessTrap(EL2, UInt(0x03))
            }
        };
        ()
    };
    let temp : bits(32) = R_read(t);
    AArch32_AutoGen_SysRegRead32(el, cp_num[3 .. 0], opc1, CRn, opc2, CRm, t);
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b1001) & (CRm == 0b1100 | CRm == 0b1110)) & (opc2 == 0b001 | opc2 == 0b010 | opc2 == 0b011) then {
        let mask : bits(32) = PMUCounterMask()[31 .. 0];
        R_set(t) = R_read(t) & mask
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b1001) & CRm == 0b1101) & (opc2 == 0b001 | opc2 == 0b010) then {
        if opc2 == 0b001 then {
            let 'pmselr = UInt(PMSELR_read()[SEL]);
            if ((EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & PMSELR_read()[SEL] != 0b11111) & UInt(PMSELR_read()[SEL]) > AArch32_GetNumEventCountersAccessible() - 1 then {
                if UInt(PMSELR_read()[SEL]) > GetNumEventCounters() - 1 then {
                    R_set(t) = temp;
                    throw(Error_Undefined())
                } else if ELUsingAArch32(EL2) then {
                    R_set(t) = temp;
                    AArch32_TakeHypTrapException(UInt(0x03))
                } else {
                    R_set(t) = temp;
                    AArch64_AArch32SystemAccessTrap(EL2, UInt(0x03))
                }
            } else if pmselr == 31 then {
                R_set(t) = PMCCFILTR_read().bits
            } else {
                R_set(t) = PMEVTYPER_read(pmselr).bits
            }
        };
        if opc2 == 0b010 then {
            if UInt(PMSELR_read()[SEL]) > GetNumEventCounters() - 1 | (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & UInt(PMSELR_read()[SEL]) > AArch32_GetNumEventCountersAccessible() - 1 then {
                if UInt(PMSELR_read()[SEL]) > GetNumEventCounters() - 1 then {
                    R_set(t) = temp;
                    throw(Error_Undefined())
                } else if ELUsingAArch32(EL2) then {
                    R_set(t) = temp;
                    AArch32_TakeHypTrapException(UInt(0x03))
                } else {
                    R_set(t) = temp;
                    AArch64_AArch32SystemAccessTrap(EL2, UInt(0x03))
                }
            } else {
                let 'pmselr = UInt(PMSELR_read()[SEL]);
                assert(pmselr < 31);
                R_set(t) = PMEVCNTR_read(pmselr)[31 .. 0]
            }
        };
        ()
    };
    if (((cp_num == 15 & opc1 == 0b000) & opc2 == 0b000) & CRn == 0b1001) & CRm == 0b1100 then {
        R_set(t) = [R_read(t) with 15 .. 11 = AArch32_GetNumEventCountersAccessible()[4 .. 0]]
    };
    if ((cp_num == 15 & opc1 == 0b000) & CRn == 0b1110) & (CRm[3 .. 2] == 0b10 | CRm[3 .. 2] == 0b11 & (CRm[1 .. 0] @ opc2[2 .. 0]) != 0b11111) then {
        if UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > GetNumEventCounters() - 1 | (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > AArch32_GetNumEventCountersAccessible() - 1 then {
            if UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > GetNumEventCounters() - 1 then {
                R_set(t) = temp;
                throw(Error_Undefined())
            } else if ELUsingAArch32(EL2) then {
                R_set(t) = temp;
                AArch32_TakeHypTrapException(UInt(0x03))
            } else {
                R_set(t) = temp;
                AArch64_AArch32SystemAccessTrap(EL2, UInt(0x03))
            }
        };
        ()
    };
    if ((cp_num == 14 & opc1 == 0b000) & opc2 == 0b110) & CRn == 0b0111 then {
        if CRm == 0b1000 then {
            R_set(t) = [R_read(t) with 7 .. 0 = 0b11111111]
        };
        if CRm == 0b1001 then {
            R_set(t) = [R_read(t) with 7 .. 0 = DBGCLAIMCLR_read().bits[7 .. 0]]
        };
        return()
    };
    if (((cp_num == 14 & opc1 == 0b000) & opc2 == 0b010) & CRn == 0b0000) & CRm == 0b0010 then {
        R_set(t) = [R_read(t) with 18 .. 18 = if CurrentSecurityState() == SS_NonSecure then
          0b1
        else
          0b0];
        if HaveEL(EL3) then {
            if ELUsingAArch32(EL3) & SDCR[SPME] == 0b1 then {
                R_set(t) = [R_read(t) with 17 .. 17 = 0b0]
            } else if not_bool(ELUsingAArch32(EL3)) & MDCR_EL3[SPME] == 0b1 then {
                R_set(t) = [R_read(t) with 17 .. 17 = 0b0]
            } else {
                R_set(t) = [R_read(t) with 17 .. 17 = 0b1]
            }
        };
        return()
    };
    if (((cp_num == 15 & opc1 == 0b000) & opc2 == 0b000) & CRn == 0b1100) & CRm == 0b0001 then {
        R_set(t) = getISR();
        return()
    } else if (((cp_num == 15 & opc1 == 0b001) & (opc2 == 0b000 | opc2 == 0b010)) & CRn == 0b0000) & CRm == 0b0000 then {
        if opc2 == 0b000 then {
            R_set(t) = CacheConfigRead(CSSELR_read().bits[3 .. 0])[31 .. 0];
            return()
        } else {
            R_set(t) = CacheConfigRead(CSSELR_read().bits[3 .. 0])[63 .. 32];
            return()
        }
    } else ();
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b0101) & CRm == 0b0100) & (opc2 == 0b000 | opc2 == 0b100) then {
        if UInt(ERRIDR_read()[NUM]) == UInt(0x0) | UInt(ERRSELR_read()[SEL]) >= UInt(ERRIDR_read()[NUM]) then {
            R_set(t) = Zeros(32)
        } else {
            let 'index = UInt(ERRSELR_read()[SEL]);
            if opc2 == 0b000 then {
                assert(constraint((0 <= 'index & 'index < 4)));
                R_set(t) = ERRnFR[index].bits[31 .. 0]
            } else {
                assert(constraint((0 <= 'index & 'index < 4)));
                R_set(t) = ERRnFR[index].bits[63 .. 32]
            }
        }
    };
    if (((cp_num == 14 & opc1 == 0b000) & CRn == 0b0000) & CRm == 0b0101) & opc2 == 0b000 then {
        DBGDSCRint_write() = [DBGDSCRint_read() with RXfull = 0b0];
        MDCCSR_EL0[RXfull] = 0b0;
        DBGDSCRext_write() = [DBGDSCRext_read() with RXfull = 0b0];
        EDSCR_write() = [EDSCR_read() with RXfull = 0b0]
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b0001) & CRm == 0b0000) & opc2 == 0b010 then {
        if ((CurrentSecurityState() == SS_NonSecure & HaveEL(EL3)) & ELUsingAArch32(EL3)) & NSACR[cp10] == 0b0 then {
            R_set(t) = [R_read(t) with 23 .. 20 = 0b0000]
        };
        ()
    };
    return()
}

function AArch32_SysRegWriteM (cp_num, instr, address) = {
    let CRd : bits(4) = instr[15 .. 12];
    if CRd == 0b0101 & cp_num == UInt(0xE) then {
        AArch32_LDC(cp_num[3 .. 0], CRd, address)
    };
    ()
}

function AArch32_SysRegRead64 (cp_num, instr, t, t2) = {
    el : bits(2) = undefined;
    n : int = undefined;
    let (_, __tup_1 : bits(2)) = ELFromM32(PSTATE.M) in
      {
          el = __tup_1
      };
    let opc1 : bits(4) = Slice(instr, 4, 4);
    let CRm : bits(4) = Slice(instr, 0, 4);
    if (cp_num == 15 & (match CRm[3 .. 1] {
      [bitzero, _, bitzero] => true,
      _ => false
    }) : bool) & [opc1[3]] == 0b0 then {
        let 'n = UInt([CRm[0]] @ opc1[2 .. 0]);
        if CRm[3 .. 1] == 0b000 then {
            if n >= UInt(AMCGCR_read()[CG0NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else if CRm[3 .. 1] == 0b010 then {
            if n >= UInt(AMCGCR_read()[CG1NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else ()
    };
    AArch32_AutoGen_SysRegRead64(el, cp_num[3 .. 0], opc1, CRm, t, t2)
}

function AArch32_SysRegWrite (cp_num, instr, t) = {
    el : bits(2) = undefined;
    temprt : bits(32) = R_read(t);
    let (_, __tup_1 : bits(2)) = ELFromM32(PSTATE.M) in
      {
          el = __tup_1
      };
    let opc1 : bits(3) = Slice(instr, 21, 3);
    let CRn : bits(4) = Slice(instr, 16, 4);
    let CRm : bits(4) = Slice(instr, 0, 4);
    let opc2 : bits(3) = Slice(instr, 5, 3);
    if ((cp_num == 14 & opc1 == 0b000) & CRn == 0b0000) & opc2 == 0b101 then {
        temprt[8] = Bit([temprt[7]]);
        temprt[6] = Bit([temprt[5]])
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b0001) & CRm == 0b0000) & opc2 == 0b010 then {
        if ((CurrentSecurityState() == SS_NonSecure & HaveEL(EL3)) & ELUsingAArch32(EL3)) & NSACR[cp10] == 0b0 then {
            temprt[23 .. 22] = CPACR_read__1()[cp11];
            temprt[21 .. 20] = CPACR_read__1()[cp10]
        };
        ()
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b1001) & (CRm == 0b1100 | CRm == 0b1110)) & (opc2 == 0b001 | opc2 == 0b010 | opc2 == 0b011) then {
        let mask : bits(32) = PMUCounterMask()[31 .. 0];
        if opc2 == 0b011 & CRm == 0b1100 then {
            temprt = PMOVSSET_read().bits & not_vec(temprt & mask)
        };
        if opc2 == 0b011 & CRm == 0b1110 then {
            temprt = PMOVSSET_read().bits | temprt & mask
        };
        if opc2 == 0b010 & CRm == 0b1100 then {
            temprt = PMCNTENSET_read().bits & not_vec(temprt & mask)
        };
        if opc2 == 0b001 & CRm == 0b1100 then {
            temprt = PMCNTENSET_read().bits | temprt & mask
        };
        if opc2 == 0b010 & CRm == 0b1110 then {
            temprt = PMINTENSET_read().bits & not_vec(temprt & mask)
        };
        if opc2 == 0b001 & CRm == 0b1110 then {
            temprt = PMINTENSET_read().bits | temprt & mask
        };
        ()
    };
    if (((cp_num == 15 & opc1 == 0b000) & opc2 == 0b000) & CRn == 0b1001) & CRm == 0b1100 then {
        if [temprt[3]] == 0b1 & PMCR_read()[D] == 0b0 then {
            __clock_divider = 63
        };
        ()
    };
    if ((cp_num == 15 & opc1 == 0b000) & CRn == 0b1110) & (CRm[3 .. 2] == 0b10 | CRm[3 .. 2] == 0b11 & (CRm[1 .. 0] @ opc2[2 .. 0]) != 0b11111) then {
        if UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > GetNumEventCounters() - 1 & (CRm[1 .. 0] @ opc2[2 .. 0]) != 0b11111 | ((EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & PMUSERENR_EL0[EN] == 0b1) & UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > AArch32_GetNumEventCountersAccessible() - 1 then {
            if UInt(CRm[1 .. 0] @ opc2[2 .. 0]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else if ELUsingAArch32(EL2) then {
                AArch32_TakeHypTrapException(UInt(0x03))
            } else {
                AArch64_AArch32SystemAccessTrap(EL2, UInt(0x03))
            }
        };
        ()
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b1001) & CRm == 0b1101) & (opc2 == 0b001 & PMSELR_read()[SEL] != 0b11111 | opc2 == 0b010) then {
        if UInt(PMSELR_read()[SEL]) > GetNumEventCounters() - 1 & PMSELR_read()[SEL] != 0b11111 | ((EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & PMUSERENR_EL0[EN] == 0b1) & UInt(PMSELR_read()[SEL]) > AArch32_GetNumEventCountersAccessible() - 1 then {
            if UInt(PMSELR_read()[SEL]) > GetNumEventCounters() - 1 then {
                throw(Error_Undefined())
            } else if ELUsingAArch32(EL2) then {
                AArch32_TakeHypTrapException(UInt(0x03))
            } else {
                AArch64_AArch32SystemAccessTrap(EL2, UInt(0x03))
            }
        };
        ()
    };
    if ((cp_num == 14 & opc1 == 0b000) & opc2 == 0b110) & CRn == 0b0111 then {
        if CRm == 0b1000 then {
            temprt[7 .. 0] = DBGCLAIMCLR_read().bits[7 .. 0] | temprt[7 .. 0]
        };
        if CRm == 0b1001 then {
            temprt[7 .. 0] = DBGCLAIMCLR_read().bits[7 .. 0] & not_vec(temprt[7 .. 0])
        };
        ()
    };
    let temprt2 : bits(32) = R_read(t);
    R_set(t) = temprt;
    AArch32_AutoGen_SysRegWrite32(el, cp_num[3 .. 0], opc1, CRn, opc2, CRm, t);
    R_set(t) = temprt2;
    if (((cp_num == 14 & opc1 == 0b000) & opc2 == 0b110) & CRn == 0b0111) & CRm == 0b1000 then {
        DBGCLAIMCLR_write() = Mk_DBGCLAIMCLR_Type([DBGCLAIMCLR_read().bits with 7 .. 0 = temprt[7 .. 0]])
    };
    if (((cp_num == 14 & opc1 == 0b000) & opc2 == 0b100) & CRn == 0b0001) & CRm == 0b0000 then {
        if UInt(temprt) == UInt(0xC5ACCE55) then {
            DBGOSLSR_write() = [DBGOSLSR_read() with OSLK = 0b1];
            EDPRSR[OSLK] = 0b1;
            OSLSR_EL1[OSLK] = 0b1
        } else {
            if DBGOSLSR_read()[OSLK] == 0b1 then {
                DBGOSLSR_write() = [DBGOSLSR_read() with OSLK = 0b0];
                EDPRSR[OSLK] = 0b0;
                OSLSR_EL1[OSLK] = 0b0;
                CheckOSUnlockCatch()
            };
            ()
        }
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b1001) & (CRm == 0b1100 | CRm == 0b1110)) & (opc2 == 0b001 | opc2 == 0b010 | opc2 == 0b011) then {
        if opc2 == 0b011 & CRm == 0b1100 then {
            PMOVSSET_write() = Mk_PMOVSSET_Type(temprt)
        };
        if opc2 == 0b011 & CRm == 0b1110 then {
            PMOVSR_write() = Mk_PMOVSR_Type(temprt)
        };
        if opc2 == 0b010 & CRm == 0b1100 then {
            PMCNTENSET_write() = Mk_PMCNTENSET_Type(temprt)
        };
        if opc2 == 0b001 & CRm == 0b1100 then {
            PMCNTENCLR_write() = Mk_PMCNTENCLR_Type(temprt)
        };
        if opc2 == 0b010 & CRm == 0b1110 then {
            PMINTENSET_write() = Mk_PMINTENSET_Type(temprt)
        };
        if opc2 == 0b001 & CRm == 0b1110 then {
            PMINTENCLR_write() = Mk_PMINTENCLR_Type(temprt)
        };
        ()
    };
    if (((cp_num == 15 & opc1 == 0b000) & opc2 == 0b000) & CRn == 0b1001) & CRm == 0b1100 then {
        if [temprt[2]] == 0b1 then {
            PMCCNTR_write() = Mk_PMCCNTR_Type(Zeros(64))
        };
        if [temprt[1]] == 0b1 then {
            AArch32_ClearEventCounters()
        };
        ()
    };
    if (((cp_num == 15 & opc1 == 0b000) & CRn == 0b1001) & CRm == 0b1101) & (opc2 == 0b001 | opc2 == 0b010) then {
        let 'pmselr = UInt(PMSELR_read()[SEL]);
        if opc2 == 0b001 then {
            if pmselr == 31 then {
                PMCCFILTR_write() = __get_PMCCFILTR(Mk_PMCCFILTR_Type(temprt))
            } else {
                PMEVTYPER_set(pmselr) = __get_PMEVTYPER(Mk_PMEVTYPER_Type(temprt))
            }
        };
        if opc2 == 0b010 then {
            assert(pmselr < 31);
            PMEVCNTR_set(pmselr) = temprt
        };
        ()
    };
    if ((cp_num == 15 & opc1 == 0b000) & CRn == 0b1110) & CRm[3 .. 2] == 0b11 then {
        let 'index = UInt(CRm[1 .. 0] @ opc2[2 .. 0]);
        if index == 31 then {
            PMCCFILTR_write() = __get_PMCCFILTR(Mk_PMCCFILTR_Type(temprt))
        } else {
            PMEVTYPER_set(index) = __get_PMEVTYPER(Mk_PMEVTYPER_Type(temprt))
        }
    };
    if (((cp_num == 15 & opc1 == 0b000) & opc2 == 0b100) & CRn == 0b1001) & CRm == 0b1100 then {
        AArch32_PMUSwIncrement(temprt)
    };
    if ((((cp_num == 15 & (opc1 == 0b000 | opc1 == 0b100)) & CRn == 0b1100) & opc2 == 0b010) & CRm == 0b0000) & [temprt[1]] == 0b1 then {
        TakeReset(false)
    } else if (((cp_num == 15 & opc1 == 0b000) & (opc2 == 0b100 | opc2 == 0b111)) & CRn == 0b0000) & CRm == 0b0000 then {
        MIDR_write() = Mk_MIDR_Type(temprt)
    } else ();
    if (((cp_num == 14 & opc1 == 0b000) & CRn == 0b0000) & opc2 == 0b000) & CRm == 0b0101 then {
        DBGDSCRint_write() = [DBGDSCRint_read() with TXfull = 0b1];
        MDCCSR_EL0[TXfull] = 0b1;
        DBGDSCRext_write() = [DBGDSCRext_read() with TXfull = 0b1];
        EDSCR_write() = [EDSCR_read() with TXfull = 0b1]
    };
    return()
}

function AArch32_SysRegWrite64 (cp_num, instr, t, t2) = {
    el : bits(2) = undefined;
    n : int = undefined;
    let (_, __tup_1 : bits(2)) = ELFromM32(PSTATE.M) in
      {
          el = __tup_1
      };
    let opc1 : bits(4) = Slice(instr, 4, 4);
    let CRm : bits(4) = Slice(instr, 0, 4);
    if (cp_num == 15 & (match CRm[3 .. 1] {
      [bitzero, _, bitzero] => true,
      _ => false
    }) : bool) & [opc1[3]] == 0b0 then {
        let 'n = UInt([CRm[0]] @ opc1[2 .. 0]);
        if CRm[3 .. 1] == 0b000 then {
            if n >= UInt(AMCGCR_read()[CG0NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else if CRm[3 .. 1] == 0b010 then {
            if n >= UInt(AMCGCR_read()[CG1NC]) then {
                throw(Error_Undefined())
            };
            ()
        } else ()
    };
    AArch32_AutoGen_SysRegWrite64(el, cp_num[3 .. 0], opc1, CRm, t, t2);
    return()
}

function GetNreg () = {
    nreg : int = undefined;
    let instr : bits(32) = ThisInstr();
    if (instr[31 .. 28] != 0b1111 & instr[27 .. 24] == 0b1110) & [instr[4]] == 0b1 then {
        nreg = 1
    } else if instr[31 .. 28] != 0b1111 & instr[27 .. 21] == 0b1100010 then {
        nreg = 2
    } else if (instr[31 .. 28] != 0b1111 & instr[27 .. 25] == 0b110) & [instr[22]] == 0b0 then {
        nreg = 0
    } else {
        assert(false)
    };
    let 'nreg = nreg;
    return(nreg)
}

function AArch32_UnallocatedSysRegAccess (coproc, opc1, CRn, opc2, CRm, read, t) = {
    tid3_trap : bool = false;
    if ((PLOfEL(PSTATE.EL) == PL1 & read) & EL2Enabled()) & HCR_EL2[TID3] == 0b1 then {
        tid3_trap = if HaveFGTExt() then true else
          __IMPDEF_boolean("Unallocated encodings trapped by HCR_EL2.TID3")
    };
    if (((tid3_trap & UInt(coproc) == 15) & UInt(opc1) == 0) & UInt(CRn) == 0) & (UInt(CRm) == 2 | UInt(CRm) == 3 | UInt(CRm) == 4 | UInt(CRm) == 5 | UInt(CRm) == 6 | UInt(CRm) == 7) then {
        if ELUsingAArch32(EL2) then {
            AArch32_SystemAccessTrap(M32_Hyp, UInt(0x3))
        } else {
            AArch64_AArch32SystemAccessTrap(EL2, UInt(0x3))
        }
    };
    AArch32_CheckCP15InstrCoarseTraps(UInt(CRn), GetNreg(), UInt(CRm));
    if (((UInt(coproc) == 15 & opc1 == 0b000) & CRn == 0b0000) & CRm == 0b0010) & opc2 == 0b111 then {
        if PSTATE.EL != EL0 & read then {
            R_set(t) = __UNKNOWN_bits(32);
            return()
        } else {
            throw(Error_Undefined())
        }
    };
    if ((UInt(coproc) == 15 & opc1 == 0b000) & CRn == 0b0000) & UInt(CRm) >= 3 then {
        if PSTATE.EL != EL0 & read then {
            R_set(t) = __UNKNOWN_bits(32);
            return()
        } else {
            throw(Error_Undefined())
        }
    };
    if not_bool(read) then {
        throw(Error_Undefined())
    };
    if UInt(coproc) == 15 & CRn == 0b0000 then {
        if UInt(opc1) > 0 then {
            throw(Error_Undefined())
        } else {
            if CRm == 0b0011 & (opc2 == 0b000 | opc2 == 0b001 | opc2 == 0b010) then {
                R_set(t) = __UNKNOWN_bits(32);
                return()
            };
            if (CRm == 0b0100 | CRm == 0b0110 | CRm == 0b0111) & (opc2 == 0b000 | opc2 == 0b001 | opc2 == 0b111) then {
                R_set(t) = __UNKNOWN_bits(32);
                return()
            };
            if CRm == 0b0101 & (opc2 == 0b000 | opc2 == 0b001 | opc2 == 0b100 | opc2 == 0b101) then {
                R_set(t) = __UNKNOWN_bits(32);
                return()
            } else {
                R_set(t) = Zeros(32);
                return()
            }
        }
    };
    throw(Error_Undefined())
}

function AArch64_ImpDefSysRegRead (op0, op1, CRn, CRm, op2, t) = {
    throw(Error_Undefined())
}

function AArch64_ImpDefSysRegWrite (op0, op1, CRn, CRm, op2, t) = {
    throw(Error_Undefined())
}

function AArch64_ImpDefSysRegRead128 (op0, op1, CRn, CRm, op2, t, t2) = {
    throw(Error_Undefined())
}

function AArch64_ImpDefSysRegWrite128 (op0, op1, CRn, CRm, op2, t, t2) = {
    throw(Error_Undefined())
}

function AArch64_ImpDefSysInstr128 (el, op1, CRn, CRm, op2, t, t2) = {
    throw(Error_Undefined())
}
