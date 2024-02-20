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

function AArch32_CurrentCond () = {
    return(__currentCond)
}

function UnallocatedA32_Instruction instr = {
    nop : bool = undefined;
    match instr {
      [_, _, _, _, bitzero, bitzero, bitone, bitone, bitzero, bitzero, bitone, bitzero, bitzero, bitzero, bitzero, bitzero, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => {
          let cond : bits(4) = instr[31 .. 28];
          nop = cond != 0b1111
      },
      [bitone, bitone, bitone, bitone, bitzero, bitone, bitzero, bitzero, _, bitzero, bitzero, bitone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => {
          nop = true
      },
      [bitone, bitone, bitone, bitone, bitzero, bitone, bitone, bitzero, _, bitzero, bitzero, bitone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bitzero, _, _, _, _] => {
          nop = true
      },
      _ => {
          nop = false
      }
    };
    if not_bool(nop) & ConditionHolds(AArch32_CurrentCond()) then {
        AArch32_UndefinedFault()
    };
    ()
}

function UnallocatedT32_32_Instruction instr = {
    nop : bool = undefined;
    match instr {
      [bitone, bitone, bitone, bitone, bitzero, bitzero, bitone, bitone, bitone, bitzero, bitone, bitzero, _, _, _, _, bitone, bitzero, _, bitzero, _, bitzero, bitzero, bitzero, _, _, _, _, _, _, _, _] => {
          nop = true
      },
      [bitone, bitone, bitone, bitone, bitone, bitzero, bitzero, bitone, bitzero, bitzero, bitone, bitone, _, _, _, _, bitone, bitone, bitone, bitone, bitzero, bitzero, bitzero, bitzero, bitzero, bitzero, _, _, _, _, _, _] => {
          nop = true
      },
      [bitone, bitone, bitone, bitone, bitone, bitzero, bitzero, bitone, bitzero, bitzero, bitone, bitone, _, _, _, _, bitone, bitone, bitone, bitone, bitone, bitone, bitzero, bitzero, _, _, _, _, _, _, _, _] => {
          nop = true
      },
      [bitone, bitone, bitone, bitone, bitone, bitzero, bitzero, bitone, bitone, bitzero, bitone, bitone, _, _, _, _, bitone, bitone, bitone, bitone, _, _, _, _, _, _, _, _, _, _, _, _] => {
          nop = true
      },
      [bitone, bitone, bitone, bitone, bitone, bitzero, bitzero, bitone, _, bitzero, bitone, bitone, bitone, bitone, bitone, bitone, bitone, bitone, bitone, bitone, _, _, _, _, _, _, _, _, _, _, _, _] => {
          nop = true
      },
      _ => {
          nop = false
      }
    };
    let nop = nop;
    if not_bool(nop) & ConditionHolds(AArch32_CurrentCond()) then {
        AArch32_UndefinedFault()
    };
    ()
}

function UnallocatedT32_16_Instruction instr = {
    nop : bool = undefined;
    match instr {
      [bitone, bitzero, bitone, bitone, bitone, bitone, bitone, bitone, _, _, _, _, bitzero, bitzero, bitzero, bitzero] => {
          let hint : bits(4) = instr[7 .. 4];
          match hint {
            [bitzero, bitone, bitone, _] => {
                nop = true
            },
            [bitone, _, _, _] => {
                nop = true
            },
            _ => {
                nop = false
            }
          }
      },
      _ => {
          nop = false
      }
    };
    if not_bool(nop) & ConditionHolds(AArch32_CurrentCond()) then {
        AArch32_UndefinedFault()
    };
    ()
}

function __DefaultCond enc = {
    cond : bits(4) = undefined;
    if (enc == __A64 | enc == __A32) | PSTATE.IT[3 .. 0] == Zeros(4) then {
        cond = 0xE
    } else {
        cond = PSTATE.IT[7 .. 4]
    };
    return(cond)
}

function __SetThisInstrDetails (enc, opcode, cond) = {
    __ThisInstrEnc = enc;
    __ThisInstr = opcode;
    __currentCond = cond;
    return()
}

function ExecuteA64 instr = {
    if Halted() then {
        try {
            __SetThisInstrDetails(__A64, instr, __DefaultCond(__A64));
            __DecodeA64(UInt(_PC), instr)
        } catch {
          exn if IsExceptionTaken(exn) => (),
          exn if (IsSEE(exn) | IsUNDEFINED(exn)) | IsUNPREDICTABLE(exn) => {
              AArch64_UndefinedFault()
          }
        }
    } else {
        __DecodeA64(UInt(_PC), instr)
    }
}

function ExecuteA32 instr = {
    __DecodeA32(UInt(_PC), instr)
}

function ExecuteT32__1 instr = {
    if Halted() then {
        try {
            __SetThisInstrDetails(__T32, instr, __DefaultCond(__T32));
            __DecodeT32(UInt(_PC), instr)
        } catch {
          exn if IsExceptionTaken(exn) => (),
          exn if (IsSEE(exn) | IsUNDEFINED(exn)) | IsUNPREDICTABLE(exn) => {
              UnallocatedT32_32_Instruction(instr)
          }
        }
    } else {
        __DecodeT32(UInt(_PC), instr)
    }
}

function ExecuteT16 instr = {
    __DecodeT16(UInt(_PC), instr)
}

function ThisInstr () = {
    return(__ThisInstr)
}

function ThisInstrLength () = {
    return(if __ThisInstrEnc == __T16 then 16 else 32)
}

function NextInstrAddr N = {
    assert(constraint((0 <= 'N - 1 & 'N - 1 < 64)));
    return((_PC + DIV(ThisInstrLength(), 8))[N - 1 .. 0])
}

function __FetchInstr pc = {
    hw1 : bits(16) = undefined;
    hw2 : bits(16) = undefined;
    isT16 : bool = undefined;
    enc : __InstrEnc = undefined;
    instr : bits(32) = undefined;
    let accdesc : AccessDescriptor = CreateAccDescIFetch();
    SetBTypeCompatible(false);
    CheckSoftwareStep();
    if PSTATE.nRW == 0b0 then {
        AArch64_CheckPCAlignment();
        enc = __A64;
        instr = AArch64_MemSingle_read(PC_read(), 4, accdesc, true);
        AArch64_CheckIllegalState()
    } else {
        AArch32_CheckPCAlignment();
        if PSTATE.T == 0b1 then {
            let hw1 : bits(16) = AArch32_MemSingle_read(pc[31 .. 0], 2, accdesc, true);
            let isT16 : bool = UInt(hw1[15 .. 11]) < UInt(0b11101);
            if isT16 then {
                enc = __T16;
                instr = Zeros(16) @ hw1
            } else {
                let hw2 : bits(16) = AArch32_MemSingle_read(pc[31 .. 0] + 2, 2, accdesc, true);
                enc = __T32;
                instr = hw1 @ hw2
            }
        } else {
            enc = __A32;
            instr = AArch32_MemSingle_read(pc[31 .. 0], 4, accdesc, true)
        };
        AArch32_CheckIllegalState()
    };
    return((enc, instr))
}

val __TryDecodeExecute : (__InstrEnc, bits(32)) -> unit

function __TryDecodeExecute (enc, instr) = {
    match enc {
      __A64 => {
          ExecuteA64(instr)
      },
      __A32 => {
          ExecuteA32(instr)
      },
      __T16 => {
          ExecuteT16(instr[15 .. 0])
      },
      __T32 => {
          ExecuteT32__1(instr)
      }
    };
    return()
}

function __DecodeExecute (enc, instr) = {
    // SEE is handled in the Sail model by throwing a specific Sail exception
    // after recording the instruction we just tried in a global variable, so
    // that we can then retry decodings that we haven't tried yet.
    try {
        __TryDecodeExecute(enc, instr)
    } catch {
        exn if IsSEE(exn) => {
            // Retry decode in case of SEE;  retrying once seems enough in practice
            __TryDecodeExecute(enc, instr)
        },
        exn => throw(exn) // Pass through other kinds of exceptions
    }
}

register __emulator_termination_opcode : option(bits(32)) = None()

val __CheckForEmulatorTermination : (__InstrEnc, bits(32)) -> unit

function __CheckForEmulatorTermination(enc, instr) = {
    // Check for magic opcode to terminate the emulator
    match __emulator_termination_opcode {
        Some(magic) =>
            if instr == magic then {
                print("[Sail] Terminating emulation at opcode " ++ bits_str(magic) ++ "\n");
                exit()
            },
        None() => ()
    }
}

function __InstructionExecute () = {
    enc : __InstrEnc = undefined;
    instr : bits(32) = undefined;
    EDSCR_write() = [EDSCR_read() with PipeAdv = 0b1];
    if not_bool(IsZero(EDESR.bits)) then {
        CheckPendingOSUnlockCatch();
        CheckPendingResetCatch();
        CheckPendingExceptionCatch(true)
    };
    try {
        ShouldAdvanceIT = PSTATE.nRW == 0b1 & PSTATE.T == 0b1;
        ShouldAdvanceSS = true;
        let pc : bits(64) = ThisInstrAddr(64);
        (enc, instr) = __FetchInstr(pc);
        __CheckForEmulatorTermination(enc, instr);
        PMUEvent(PMU_EVENT_INST_SPEC);
        __BranchTaken = false;
        __ExclusiveMonitorSet = false;
        __SetThisInstrDetails(enc, instr, __DefaultCond(enc));
        SPEPreExecution();
        __DecodeExecute(enc, instr);
        PMUEvent(PMU_EVENT_INST_RETIRED)
    } catch {
      exn if (IsSEE(exn) | IsUNDEFINED(exn)) | IsUNPREDICTABLE(exn) => {
          if UsingAArch32() then {
              match enc {
                __A32 => {
                    UnallocatedA32_Instruction(instr)
                },
                __T16 => {
                    UnallocatedT32_16_Instruction(instr[15 .. 0])
                },
                __T32 => {
                    UnallocatedT32_32_Instruction(instr)
                },
                _ => {
                    Unreachable()
                }
              }
          } else {
              AArch64_UndefinedFault()
          }
      },
      exn if IsExceptionTaken(exn) => ()
    };
    SPEPostExecution();
    InGuardedPage = false;
    if not_bool(AArch64_ExecutingERETInstr()) then {
        PSTATE.BTYPE = BTypeNext
    };
    if not_bool(__BranchTaken) then {
        _PC = (_PC + DIV(ThisInstrLength(), 8))[63 .. 0]
    };
    if ShouldAdvanceIT then {
        AArch32_ITAdvance()
    };
    if ShouldAdvanceSS then {
        SSAdvance()
    };
    return()
}

function __TopLevel () = {
    BranchTaken : BranchType = undefined;
    interrupt_taken : bool = undefined;
    if Halted() then {
        return()
    };
    interrupt_req : InterruptReq = undefined;
    interrupt_req.take_SE = true;
    interrupt_req.take_vSE = true;
    interrupt_req.take_IRQ = true;
    interrupt_req.take_vIRQ = true;
    interrupt_req.take_FIQ = true;
    interrupt_req.take_vFIQ = true;
    try {
        let interrupt_taken : bool = TakePendingInterrupts(interrupt_req);
        if not_bool(interrupt_taken) then {
            if Branchtypetaken == BranchType_RESET then {
                CheckResetCatch();
                BranchTaken = BranchType_UNKNOWN
            };
            __InstructionExecute()
        };
        ()
    } catch {
        Error_SError(iesb_req) => {
            // Take physical SError exception
            // (see TakeUnmaskedPhysicalSErrorInterrupts)
            if UsingAArch32() then {
                AArch32_TakePhysicalSErrorException(iesb_req)
            } else {
                AArch64_TakePhysicalSErrorException(iesb_req)
            }
        },
        Error_ExceptionTaken() => (), // Exception setup should have been done by AArch{32,64}_TakeException
        e => throw(e) // Pass through other exceptions
    }
}

function __CycleEnd () = {
    SPECycle();
    __UpdateSystemCounter();
    if UsingAArch32() then {
        AArch32_PMUCycle()
    } else {
        AArch64_PMUCycle()
    };
    __EndCycle()
}
