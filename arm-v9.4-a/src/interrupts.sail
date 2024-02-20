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

function AArch64_PendingUnmaskedPhysicalInterrupts mask_in = {
    fiq : bool = undefined;
    fiq_nmi : bool = undefined;
    irq : bool = undefined;
    irq_nmi : bool = undefined;
    mask : bits(3) = mask_in;
    let se_pending : bits(1) = if IsPhysicalSErrorPending() then 0b1 else 0b0;
    (irq, irq_nmi) = IRQPending();
    (fiq, fiq_nmi) = FIQPending();
    let irq_pending : bits(1) = if irq then 0b1 else 0b0;
    let fiq_pending : bits(1) = if fiq then 0b1 else 0b0;
    allintmask : bits(1) = undefined;
    if HaveFeatNMI() & SCTLR_read__1()[NMI] == 0b1 then {
        allintmask = PSTATE.ALLINT | PSTATE.SP & SCTLR_read__1()[SPINTMASK];
        if PSTATE.EL == EL0 | allintmask == 0b0 then {
            if irq_nmi then {
                mask[1] = Bit(0b0)
            };
            if fiq_nmi then {
                mask[0] = Bit(0b0)
            };
            ()
        };
        ()
    } else {
        allintmask = 0b0
    };
    let pending : bits(3) = (se_pending @ irq_pending) @ fiq_pending;
    if EL2Enabled() then {
        mask_override : bits(3) = undefined;
        if (HaveVirtHostExt() & HCR_EL2[E2H] == 0b1) & HCR_EL2[TGE] == 0b1 then {
            mask_override = 0b000
        } else if HCR_EL2[TGE] == 0b1 then {
            mask_override = 0b111
        } else {
            mask_override = HCR_EL2[AMO] @ (HCR_EL2[IMO] @ HCR_EL2[FMO])
        };
        if PSTATE.EL == EL0 | PSTATE.EL == EL1 then {
            mask = mask & not_vec(mask_override)
        } else if PSTATE.EL == EL2 then {
            if not_bool(ELUsingAArch32(EL2)) & HCR_EL2[TGE] == 0b0 then {
                mask = mask | not_vec(mask_override)
            };
            ()
        } else ()
    };
    if HaveEL(EL3) then {
        if PSTATE.EL != EL3 then {
            mask = mask & not_vec(SCR_EL3[EA] @ (SCR_EL3[IRQ] @ SCR_EL3[FIQ]))
        } else {
            mask = mask | not_vec(SCR_EL3[EA] @ (SCR_EL3[IRQ] @ SCR_EL3[FIQ]))
        }
    };
    if PSTATE.EL != EL0 & allintmask == 0b1 then {
        if PSTATE.EL == EL1 then {
            if HCR_EL2[FMO] == 0b0 & SCR_EL3[FIQ] == 0b0 then {
                mask[0] = Bit(0b1)
            };
            if HCR_EL2[IMO] == 0b0 & SCR_EL3[IRQ] == 0b0 then {
                mask[1] = Bit(0b1)
            };
            ()
        } else if PSTATE.EL == EL2 then {
            if HCR_EL2[FMO] == 0b1 then {
                mask[0] = Bit(0b1)
            };
            if HCR_EL2[IMO] == 0b1 then {
                mask[1] = Bit(0b1)
            };
            ()
        } else {
            if SCR_EL3[FIQ] == 0b1 then {
                mask[0] = Bit(0b1)
            };
            if SCR_EL3[IRQ] == 0b1 then {
                mask[1] = Bit(0b1)
            };
            ()
        }
    };
    let unmasked_pending : bits(3) = pending & not_vec(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

function AArch64_PendingUnmaskedVirtualInterrupts mask_in = {
    allintmask : bits(1) = undefined;
    mask : bits(3) = mask_in;
    pending : bits(3) = undefined;
    if ((PSTATE.EL == EL0 | PSTATE.EL == EL1) & EL2Enabled()) & HCR_EL2[TGE] == 0b0 then {
        pending = (HCR_EL2[VSE] @ (HCR_EL2[VI] @ HCR_EL2[VF])) & (HCR_EL2[AMO] @ (HCR_EL2[IMO] @ HCR_EL2[FMO]));
        if HaveFeatNMI() & SCTLR_read__1()[NMI] == 0b1 then {
            let allintmask : bits(1) = PSTATE.ALLINT | PSTATE.SP & SCTLR_read__1()[SPINTMASK];
            if IsHCRXEL2Enabled() & (PSTATE.EL == EL0 | allintmask == 0b0) then {
                if HCRX_EL2[VFNMI] == 0b1 then {
                    mask[0] = Bit(0b0)
                };
                if HCRX_EL2[VINMI] == 0b1 then {
                    mask[1] = Bit(0b0)
                };
                ()
            };
            if PSTATE.EL == EL1 & allintmask == 0b1 then {
                if HCR_EL2[FMO] == 0b1 then {
                    mask[0] = Bit(0b1)
                };
                if HCR_EL2[IMO] == 0b1 then {
                    mask[1] = Bit(0b1)
                };
                ()
            };
            ()
        };
        ()
    } else {
        pending = 0b000
    };
    let unmasked_pending : bits(3) = pending & not_vec(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

function AArch32_PendingUnmaskedPhysicalInterrupts () = {
    fiq : bool = undefined;
    irq : bool = undefined;
    mask_override : bits(3) = undefined;
    if HaveEL(EL3) & not_bool(ELUsingAArch32(EL3)) then {
        return(AArch64_PendingUnmaskedPhysicalInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F)))
    };
    let se_pending : bits(1) = if IsPhysicalSErrorPending() then 0b1 else 0b0;
    let (__tup_0 : bool, _) = IRQPending() in
      {
          irq = __tup_0
      };
    let (__tup_0 : bool, _) = FIQPending() in
      {
          fiq = __tup_0
      };
    let irq_pending : bits(1) = if irq then 0b1 else 0b0;
    let fiq_pending : bits(1) = if fiq then 0b1 else 0b0;
    let pending : bits(3) = (se_pending @ irq_pending) @ fiq_pending;
    mask : bits(3) = PSTATE.A @ (PSTATE.I @ PSTATE.F);
    if (PSTATE.EL == EL0 | PSTATE.EL == EL1) & EL2Enabled() then {
        let mask_override : bits(3) = if HCR_read()[TGE] == 0b1 then 0b111 else
          HCR_read()[AMO] @ (HCR_read()[IMO] @ HCR_read()[FMO]);
        mask = mask & not_vec(mask_override)
    };
    if HaveEL(EL3) & CurrentSecurityState() != SS_Secure then {
        if PSTATE.EL != EL3 then {
            if SCR[FIQ] == 0b1 & (SCR[FW] == 0b0 | HCR_read()[FMO] == 0b1) then {
                mask[0] = Bit(0b0)
            };
            if SCR[IRQ] == 0b1 & HCR_read()[IMO] == 0b1 then {
                mask[1] = Bit(0b0)
            };
            if EffectiveEA() == 0b1 & (SCR[AW] == 0b0 | HCR_read()[AMO] == 0b1) then {
                mask[2] = Bit(0b0)
            };
            ()
        };
        ()
    };
    let unmasked_pending : bits(3) = pending & not_vec(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

function AArch32_PendingUnmaskedVirtualInterrupts () = {
    if HaveEL(EL2) & not_bool(ELUsingAArch32(EL2)) | HaveEL(EL3) & not_bool(ELUsingAArch32(EL3)) then {
        return(AArch64_PendingUnmaskedVirtualInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F)))
    };
    let mask : bits(3) = PSTATE.A @ (PSTATE.I @ PSTATE.F);
    pending : bits(3) = undefined;
    if ((PSTATE.EL == EL0 | PSTATE.EL == EL1) & EL2Enabled()) & HCR_read()[TGE] == 0b0 then {
        pending = (HCR_read()[VA] @ (HCR_read()[VI] @ HCR_read()[VF])) & (HCR_read()[AMO] @ (HCR_read()[IMO] @ HCR_read()[FMO]))
    } else {
        pending = 0b000
    };
    let unmasked_pending : bits(3) = pending & not_vec(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

function TakePendingInterrupts interrupt_req = {
    interrupt_pend : bool = undefined;
    interrupt_taken : bool = undefined;
    vAA : bool = undefined;
    vIRQ : bool = undefined;
    vSE : bool = undefined;
    vFIQ : bool = undefined;
    AA : bool = undefined;
    IRQ : bool = undefined;
    FIQ : bool = undefined;
    SE : bool = undefined;
    if UsingAArch32() then {
        (vAA, vIRQ, vFIQ) = AArch32_PendingUnmaskedVirtualInterrupts();
        (AA, IRQ, FIQ) = AArch32_PendingUnmaskedPhysicalInterrupts();
        if not_bool(interrupt_req.take_SE) then {
            AA = false
        };
        if not_bool(interrupt_req.take_vSE) then {
            vAA = false
        };
        if not_bool(interrupt_req.take_IRQ) then {
            IRQ = false
        };
        if not_bool(interrupt_req.take_vIRQ) then {
            vIRQ = false
        };
        if not_bool(interrupt_req.take_FIQ) then {
            FIQ = false
        };
        if not_bool(interrupt_req.take_vFIQ) then {
            vFIQ = false
        };
        if ((((AA | FIQ) | IRQ) | vAA) | vFIQ) | vIRQ then {
            interrupt_taken = true
        } else {
            interrupt_taken = false
        };
        if vFIQ then {
            AArch32_TakeVirtualFIQException()
        } else if vIRQ then {
            AArch32_TakeVirtualIRQException()
        } else if vAA then {
            AArch32_TakeVirtualSErrorException()
        } else if FIQ then {
            AArch32_TakePhysicalFIQException()
        } else if IRQ then {
            AArch32_TakePhysicalIRQException()
        } else if AA then {
            AArch32_TakePhysicalSErrorException(interrupt_req.iesb_req)
        } else ()
    } else {
        (vSE, vIRQ, vFIQ) = AArch64_PendingUnmaskedVirtualInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F));
        (SE, IRQ, FIQ) = AArch64_PendingUnmaskedPhysicalInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F));
        if not_bool(interrupt_req.take_SE) then {
            SE = false
        };
        if not_bool(interrupt_req.take_vSE) then {
            vSE = false
        };
        if not_bool(interrupt_req.take_IRQ) then {
            IRQ = false
        };
        if not_bool(interrupt_req.take_vIRQ) then {
            vIRQ = false
        };
        if not_bool(interrupt_req.take_FIQ) then {
            FIQ = false
        };
        if not_bool(interrupt_req.take_vFIQ) then {
            vFIQ = false
        };
        if ((((SE | FIQ) | IRQ) | vSE) | vFIQ) | vIRQ then {
            if HaveTME() & TSTATE.depth > 0 then {
                (vSE, vIRQ, vFIQ) = AArch64_PendingUnmaskedVirtualInterrupts(TSTATE.A @ (TSTATE.I @ TSTATE.F));
                (SE, IRQ, FIQ) = AArch64_PendingUnmaskedPhysicalInterrupts(TSTATE.A @ (TSTATE.I @ TSTATE.F));
                if not_bool(interrupt_req.take_SE) then {
                    SE = false
                };
                if not_bool(interrupt_req.take_vSE) then {
                    vSE = false
                };
                if not_bool(interrupt_req.take_IRQ) then {
                    IRQ = false
                };
                if not_bool(interrupt_req.take_vIRQ) then {
                    vIRQ = false
                };
                if not_bool(interrupt_req.take_FIQ) then {
                    FIQ = false
                };
                if not_bool(interrupt_req.take_vFIQ) then {
                    vFIQ = false
                };
                let interrupt_pend : bool = ((((SE | FIQ) | IRQ) | vSE) | vFIQ) | vIRQ;
                FailTransaction__1(TMFailure_IMP, interrupt_pend, not_bool(interrupt_pend), Zeros(15))
            };
            interrupt_taken = true
        } else {
            interrupt_taken = false
        };
        if vFIQ then {
            AArch64_TakeVirtualFIQException()
        } else if vIRQ then {
            AArch64_TakeVirtualIRQException()
        } else if vSE then {
            AArch64_TakeVirtualSErrorException()
        } else if FIQ then {
            AArch64_TakePhysicalFIQException()
        } else if IRQ then {
            AArch64_TakePhysicalIRQException()
        } else if SE then {
            AArch64_TakePhysicalSErrorException(interrupt_req.iesb_req)
        } else ()
    };
    return(interrupt_taken)
}

function TakeUnmaskedSErrorInterrupts () = {
    interrupt_req : InterruptReq = undefined;
    interrupt_req.take_SE = false;
    interrupt_req.take_vSE = false;
    interrupt_req.take_FIQ = false;
    interrupt_req.take_vFIQ = false;
    interrupt_req.take_IRQ = false;
    interrupt_req.take_vIRQ = false;
    interrupt_req.iesb_req = false;
    interrupt_req.take_SE = true;
    interrupt_req.take_vSE = true;
    let interrupt_taken : bool = TakePendingInterrupts(interrupt_req);
    return()
}

// HACK: The following function is called by AArch64_TakeException.  In order
// to avoid a mutual recursion in the call graph, we don't directly take the
// exception in here, but throw a special Sail exception, which the top-level
// function can catch and actually take the SError exception.
function TakeUnmaskedPhysicalSErrorInterrupts iesb_req = {
    if UsingAArch32() then {
        let (AA, IRQ, FIQ) = AArch32_PendingUnmaskedPhysicalInterrupts();
        if AA then {
            ThrowSError(iesb_req)
        } else ()
    } else {
        let (SE, IRQ, FIQ) = AArch64_PendingUnmaskedPhysicalInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F));
        if SE then {
            ThrowSError(iesb_req)
        } else ()
    }
}
