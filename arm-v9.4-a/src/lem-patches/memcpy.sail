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

// Case split in memory operation instructions.  Note that we assume here a set
// of supported copy sizes, which doesn't seem to be constrained by the prose
// specification (i.e., a core could copy larger chunks).

val Mem_set : forall 'size, 'size in {1, 2, 4, 8, 16, 32, 64}.
  (bits(64), int('size), AccessDescriptor, bits('size * 8)) -> unit

val Mem_set__1 : forall ('ispair : Bool) 'size, 'size in {1, 2, 4, 8, 16, 32, 64}.
  (bits(64), int('size), AccessDescriptor, bool('ispair), bits('size * 8)) -> unit

val Mem_set__2 : forall ('highestAddressfirst : Bool) ('ispair : Bool) 'size,
  'size in {1, 2, 4, 8, 16, 32, 64}.
  (bits(64), int('size), AccessDescriptor, bool('ispair), bool('highestAddressfirst), bits('size * 8)) -> unit

val execute_aarch64_instrs_memory_mcpymset_setg : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(2), int('s), MOPSStage) -> unit

function execute_aarch64_instrs_memory_mcpymset_setg (d, n, options_name, s, stage) = {
    toaddress : bits(64) = X_read(d, 64);
    setsize : bits(64) = X_read(n, 64);
    let data : bits(8) = X_read(s, 8);
    nzcv : bits(4) = PSTATE.N @ (PSTATE.Z @ (PSTATE.C @ PSTATE.V));
    stagesetsize : bits(64) = undefined;
    let is_setg : bool = true;
    B : int = undefined;
    let supports_option_a : bool = SETGOptionA();
    let privileged : bool = if [options_name[0]] == 0b1 then
      AArch64_IsUnprivAccessPriv()
    else
      PSTATE.EL != EL0;
    let nontemporal : bool = [options_name[1]] == 0b1;
    let accdesc : AccessDescriptor = CreateAccDescSTGMOPS(privileged, nontemporal);
    if stage == MOPSStage_Prologue then {
        if [setsize[63]] == 0b1 then {
            setsize = 0x7FFFFFFFFFFFFFF0
        };
        if setsize != Zeros(64) & not_bool(IsAligned__1(toaddress, TAG_GRANULE)) then {
            AArch64_Abort(toaddress, AlignmentFault(accdesc))
        };
        if not_bool(IsAligned__1(setsize, TAG_GRANULE)) then {
            AArch64_Abort(toaddress, AlignmentFault(accdesc))
        };
        if supports_option_a then {
            nzcv = 0b0000;
            toaddress = toaddress + setsize;
            setsize = Zeros(64) - setsize
        } else {
            nzcv = 0b0010
        };
        stagesetsize = SETPreSizeChoice(toaddress, setsize, is_setg);
        assert([stagesetsize[63]] == [setsize[63]] | stagesetsize == Zeros(64));
        assert(stagesetsize[3 .. 0] == 0b0000);
        if SInt(setsize) > 0 then {
            assert(SInt(stagesetsize) <= SInt(setsize))
        } else {
            assert(SInt(stagesetsize) >= SInt(setsize))
        }
    } else {
        let postsize : bits(64) = SETPostSizeChoice(toaddress, setsize, is_setg);
        assert([postsize[63]] == [setsize[63]] | postsize == Zeros(64));
        assert(postsize[3 .. 0] == 0b0000);
        let zero_size_exceptions : bool = MemSetZeroSizeCheck();
        if zero_size_exceptions | SInt(setsize) != 0 then {
            if supports_option_a then {
                if [nzcv[1]] == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                };
                ()
            } else {
                if [nzcv[1]] == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                };
                ()
            }
        };
        if stage == MOPSStage_Main then {
            stagesetsize = setsize - postsize;
            if MemSetParametersIllformedM(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            };
            ()
        } else {
            stagesetsize = postsize;
            if setsize != postsize | MemSetParametersIllformedE(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            };
            ()
        };
        if setsize != Zeros(64) & not_bool(IsAligned__1(toaddress, TAG_GRANULE)) then {
            AArch64_Abort(toaddress, AlignmentFault(accdesc))
        };
        if not_bool(IsAligned__1(setsize, TAG_GRANULE)) then {
            AArch64_Abort(toaddress, AlignmentFault(accdesc))
        };
        ()
    };
    tagstep : int = undefined;
    tag : bits(4) = undefined;
    tagaddr : bits(64) = undefined;
    if SPESampleInFlight then {
        SPESampleMemSet()
    };
    if supports_option_a then {
        while SInt(stagesetsize) < 0 do {
            B = SETSizeChoice(toaddress, setsize, 16);
            assert(B <= negate(1) * SInt(stagesetsize));
            assert(B[3 .. 0] == 0b0000);
            let 'B = B;
	    assert(constraint('B in {16, 32, 64}));
	    match B {
	      16 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
	      32 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
	      64 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B)
	    };
            tagstep = DIV(B, 16);
            tag = AArch64_AllocationTagFromAddress(toaddress + setsize);
            while tagstep > 0 do {
                tagaddr = toaddress + setsize + (tagstep - 1) * 16;
                AArch64_MemTag_set(tagaddr, accdesc) = tag;
                tagstep = tagstep - 1
            };
            setsize = setsize + B;
            stagesetsize = stagesetsize + B;
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = setsize
            };
            ()
        }
    } else {
        while UInt(stagesetsize) > 0 do {
            B = SETSizeChoice(toaddress, setsize, 16);
            assert(B <= UInt(stagesetsize));
            assert(B[3 .. 0] == 0b0000);
            let 'B = B;
	    assert(constraint('B in {16, 32, 64}));
	    match B {
	      16 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
	      32 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
	      64 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B)
	    };
            tagstep = DIV(B, 16);
            tag = AArch64_AllocationTagFromAddress(toaddress);
            while tagstep > 0 do {
                tagaddr = toaddress + (tagstep - 1) * 16;
                AArch64_MemTag_set(tagaddr, accdesc) = tag;
                tagstep = tagstep - 1
            };
            toaddress = toaddress + B;
            setsize = setsize - B;
            stagesetsize = stagesetsize - B;
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = setsize;
                X_set(d, 64) = toaddress
            };
            ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(n, 64) = setsize;
        X_set(d, 64) = toaddress;
        (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv
    };
    ()
}

val execute_aarch64_instrs_memory_mcpymset_cpy : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(4), int('s), MOPSStage) -> unit

function execute_aarch64_instrs_memory_mcpymset_cpy (d, n, options_name, s, stage) = {
    let 'N = MaxBlockSizeCopiedBytes();
    toaddress : bits(64) = X_read(d, 64);
    fromaddress : bits(64) = X_read(s, 64);
    cpysize : bits(64) = X_read(n, 64);
    nzcv : bits(4) = PSTATE.N @ (PSTATE.Z @ (PSTATE.C @ PSTATE.V));
    stagecpysize : bits(64) = undefined;
    // readdata : bits(8 * 'N) = undefined;
    B : int = undefined;
    let supports_option_a : bool = CPYOptionA();
    let rprivileged : bool = if [options_name[1]] == 0b1 then
      AArch64_IsUnprivAccessPriv()
    else
      PSTATE.EL != EL0;
    let wprivileged : bool = if [options_name[0]] == 0b1 then
      AArch64_IsUnprivAccessPriv()
    else
      PSTATE.EL != EL0;
    let rnontemporal : bool = [options_name[3]] == 0b1;
    let wnontemporal : bool = [options_name[2]] == 0b1;
    let raccdesc : AccessDescriptor = CreateAccDescMOPS(MemOp_LOAD, rprivileged, rnontemporal);
    let waccdesc : AccessDescriptor = CreateAccDescMOPS(MemOp_STORE, wprivileged, wnontemporal);
    if stage == MOPSStage_Prologue then {
        if cpysize[63 .. 55] != 0b000000000 then {
            cpysize = 0x007FFFFFFFFFFFFF
        };
        forward : bool = undefined;
        if UInt(fromaddress[55 .. 0]) > UInt(toaddress[55 .. 0]) & UInt(fromaddress[55 .. 0]) < UInt(toaddress[55 .. 0] + cpysize[55 .. 0]) then {
            forward = true
        } else if UInt(fromaddress[55 .. 0]) < UInt(toaddress[55 .. 0]) & UInt(fromaddress[55 .. 0] + cpysize[55 .. 0]) > UInt(toaddress[55 .. 0]) then {
            forward = false
        } else {
            forward = MemCpyDirectionChoice(fromaddress, toaddress, cpysize)
        };
        if supports_option_a then {
            nzcv = 0b0000;
            if forward then {
                toaddress = toaddress + cpysize;
                fromaddress = fromaddress + cpysize;
                cpysize = Zeros(64) - cpysize
            };
            ()
        } else {
            if not_bool(forward) then {
                toaddress = toaddress + cpysize;
                fromaddress = fromaddress + cpysize;
                nzcv = 0b1010
            } else {
                nzcv = 0b0010
            }
        };
        stagecpysize = CPYPreSizeChoice(toaddress, fromaddress, cpysize);
        assert([stagecpysize[63]] == [cpysize[63]] | stagecpysize == Zeros(64));
        if SInt(cpysize) > 0 then {
            assert(SInt(stagecpysize) <= SInt(cpysize))
        } else {
            assert(SInt(stagecpysize) >= SInt(cpysize))
        }
    } else {
        let zero_size_exceptions : bool = MemCpyZeroSizeCheck();
        if zero_size_exceptions | SInt(cpysize) != 0 then {
            if supports_option_a then {
                if [nzcv[1]] == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                };
                ()
            } else {
                if [nzcv[1]] == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                };
                ()
            }
        };
        let postsize : bits(64) = CPYPostSizeChoice(toaddress, fromaddress, cpysize);
        assert([postsize[63]] == [cpysize[63]] | SInt(postsize) == 0);
        if stage == MOPSStage_Main then {
            stagecpysize = cpysize - postsize;
            if MemCpyParametersIllformedM(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            };
            ()
        } else {
            stagecpysize = postsize;
            if cpysize != postsize | MemCpyParametersIllformedE(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            };
            ()
        }
    };
    if SPESampleInFlight then {
        SPESampleMemCopy()
    };
    if supports_option_a then {
        while SInt(stagecpysize) != 0 do {
            let 'B = CPYSizeChoice(toaddress, fromaddress, cpysize);
	    assert(constraint('B in {1, 2, 4, 8, 16, 32, 64}));
            if SInt(cpysize) < 0 then {
                assert(B <= negate(1) * SInt(stagecpysize));
		match B {
                    1 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    2 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    4 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    8 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    16 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    32 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    64 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    }
		};
                cpysize = cpysize + B;
                stagecpysize = stagecpysize + B
            } else {
                assert(B <= SInt(stagecpysize));
                cpysize = cpysize - B;
                stagecpysize = stagecpysize - B;
		match B {
                    1 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    2 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    4 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    8 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    16 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    32 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    },
                    64 => {
                      let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                      Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                    }
		}
            };
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = cpysize
            };
            ()
        }
    } else {
        while UInt(stagecpysize) > 0 do {
            let 'B = CPYSizeChoice(toaddress, fromaddress, cpysize);
            assert(B <= UInt(stagecpysize));
	    assert(constraint('B in {1, 2, 4, 8, 16, 32, 64}));
            if [nzcv[3]] == 0b0 then {
                match B {
                    1 => {
                        let readdata = Mem_read(fromaddress, B, raccdesc);
                        Mem_set(toaddress, B, waccdesc) = readdata
                    },
                    2 => {
                        let readdata = Mem_read(fromaddress, B, raccdesc);
                        Mem_set(toaddress, B, waccdesc) = readdata
                    },
                    4 => {
                        let readdata = Mem_read(fromaddress, B, raccdesc);
                        Mem_set(toaddress, B, waccdesc) = readdata
                    },
                    8 => {
                        let readdata = Mem_read(fromaddress, B, raccdesc);
                        Mem_set(toaddress, B, waccdesc) = readdata
                    },
                    16 => {
                        let readdata = Mem_read(fromaddress, B, raccdesc);
                        Mem_set(toaddress, B, waccdesc) = readdata
                    },
                    32 => {
                        let readdata = Mem_read(fromaddress, B, raccdesc);
                        Mem_set(toaddress, B, waccdesc) = readdata
                    },
                    64 => {
                        let readdata = Mem_read(fromaddress, B, raccdesc);
                        Mem_set(toaddress, B, waccdesc) = readdata
                    }
                };
                fromaddress = fromaddress + B;
                toaddress = toaddress + B
            } else {
                match B {
                    1 => {
                        let readdata = Mem_read(fromaddress - B, B, raccdesc);
                        Mem_set(toaddress - B, B, waccdesc) = readdata
                    },
                    2 => {
                        let readdata = Mem_read(fromaddress - B, B, raccdesc);
                        Mem_set(toaddress - B, B, waccdesc) = readdata
                    },
                    4 => {
                        let readdata = Mem_read(fromaddress - B, B, raccdesc);
                        Mem_set(toaddress - B, B, waccdesc) = readdata
                    },
                    8 => {
                        let readdata = Mem_read(fromaddress - B, B, raccdesc);
                        Mem_set(toaddress - B, B, waccdesc) = readdata
                    },
                    16 => {
                        let readdata = Mem_read(fromaddress - B, B, raccdesc);
                        Mem_set(toaddress - B, B, waccdesc) = readdata
                    },
                    32 => {
                        let readdata = Mem_read(fromaddress - B, B, raccdesc);
                        Mem_set(toaddress - B, B, waccdesc) = readdata
                    },
                    64 => {
                        let readdata = Mem_read(fromaddress - B, B, raccdesc);
                        Mem_set(toaddress - B, B, waccdesc) = readdata
                    }
                };
                fromaddress = fromaddress - B;
                toaddress = toaddress - B
            };
            cpysize = cpysize - B;
            stagecpysize = stagecpysize - B;
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = cpysize;
                X_set(d, 64) = toaddress;
                X_set(s, 64) = fromaddress
            };
            ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(n, 64) = cpysize;
        X_set(d, 64) = toaddress;
        X_set(s, 64) = fromaddress;
        (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv
    };
    ()
}

val execute_aarch64_instrs_memory_mcpymset_cpyf : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(4), int('s), MOPSStage) -> unit

function execute_aarch64_instrs_memory_mcpymset_cpyf (d, n, options_name, s, stage) = {
    let 'N = MaxBlockSizeCopiedBytes();
    toaddress : bits(64) = X_read(d, 64);
    fromaddress : bits(64) = X_read(s, 64);
    cpysize : bits(64) = X_read(n, 64);
    nzcv : bits(4) = PSTATE.N @ (PSTATE.Z @ (PSTATE.C @ PSTATE.V));
    stagecpysize : bits(64) = undefined;
    // readdata : bits(8 * 'N) = undefined;
    B : int = undefined;
    let supports_option_a : bool = CPYFOptionA();
    let rprivileged : bool = if [options_name[1]] == 0b1 then
      AArch64_IsUnprivAccessPriv()
    else
      PSTATE.EL != EL0;
    let wprivileged : bool = if [options_name[0]] == 0b1 then
      AArch64_IsUnprivAccessPriv()
    else
      PSTATE.EL != EL0;
    let rnontemporal : bool = [options_name[3]] == 0b1;
    let wnontemporal : bool = [options_name[2]] == 0b1;
    let raccdesc : AccessDescriptor = CreateAccDescMOPS(MemOp_LOAD, rprivileged, rnontemporal);
    let waccdesc : AccessDescriptor = CreateAccDescMOPS(MemOp_STORE, wprivileged, wnontemporal);
    if stage == MOPSStage_Prologue then {
        if [cpysize[63]] == 0b1 then {
            cpysize = 0x7FFFFFFFFFFFFFFF
        };
        if supports_option_a then {
            nzcv = 0b0000;
            toaddress = toaddress + cpysize;
            fromaddress = fromaddress + cpysize;
            cpysize = Zeros(64) - cpysize
        } else {
            nzcv = 0b0010
        };
        stagecpysize = CPYPreSizeChoice(toaddress, fromaddress, cpysize);
        assert([stagecpysize[63]] == [cpysize[63]] | stagecpysize == Zeros(64));
        if SInt(cpysize) > 0 then {
            assert(SInt(stagecpysize) <= SInt(cpysize))
        } else {
            assert(SInt(stagecpysize) >= SInt(cpysize))
        }
    } else {
        let zero_size_exceptions : bool = MemCpyZeroSizeCheck();
        if zero_size_exceptions | SInt(cpysize) != 0 then {
            if supports_option_a then {
                if [nzcv[1]] == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                };
                ()
            } else {
                if [nzcv[1]] == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                };
                ()
            }
        };
        let postsize : bits(64) = CPYPostSizeChoice(toaddress, fromaddress, cpysize);
        assert([postsize[63]] == [cpysize[63]] | SInt(postsize) == 0);
        if stage == MOPSStage_Main then {
            stagecpysize = cpysize - postsize;
            if MemCpyParametersIllformedM(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            };
            ()
        } else {
            stagecpysize = postsize;
            if cpysize != postsize | MemCpyParametersIllformedE(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            };
            ()
        }
    };
    if SPESampleInFlight then {
        SPESampleMemCopy()
    };
    if supports_option_a then {
        while SInt(stagecpysize) != 0 do {
            let 'B = CPYSizeChoice(toaddress, fromaddress, cpysize);
            assert(B <= negate(1) * SInt(stagecpysize));
            assert(constraint('B in {1, 2, 4, 8, 16, 32, 64}));
            match B {
                1 => {
                    let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                    Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                },
                2 => {
                    let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                    Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                },
                4 => {
                    let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                    Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                },
                8 => {
                    let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                    Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                },
                16 => {
                    let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                    Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                },
                32 => {
                    let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                    Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                },
                64 => {
                    let readdata = Mem_read(fromaddress + cpysize, B, raccdesc);
                    Mem_set(toaddress + cpysize, B, waccdesc) = readdata
                }
            };
            cpysize = cpysize + B;
            stagecpysize = stagecpysize + B;
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = cpysize
            };
            ()
        }
    } else {
        while UInt(stagecpysize) > 0 do {
            let 'B = CPYSizeChoice(toaddress, fromaddress, cpysize);
            assert(B <= UInt(stagecpysize));
            assert(constraint('B in {1, 2, 4, 8, 16, 32, 64}));
            match B {
                1 => {
                    let readdata = Mem_read(fromaddress, B, raccdesc);
                    Mem_set(toaddress, B, waccdesc) = readdata
                },
                2 => {
                    let readdata = Mem_read(fromaddress, B, raccdesc);
                    Mem_set(toaddress, B, waccdesc) = readdata
                },
                4 => {
                    let readdata = Mem_read(fromaddress, B, raccdesc);
                    Mem_set(toaddress, B, waccdesc) = readdata
                },
                8 => {
                    let readdata = Mem_read(fromaddress, B, raccdesc);
                    Mem_set(toaddress, B, waccdesc) = readdata
                },
                16 => {
                    let readdata = Mem_read(fromaddress, B, raccdesc);
                    Mem_set(toaddress, B, waccdesc) = readdata
                },
                32 => {
                    let readdata = Mem_read(fromaddress, B, raccdesc);
                    Mem_set(toaddress, B, waccdesc) = readdata
                },
                64 => {
                    let readdata = Mem_read(fromaddress, B, raccdesc);
                    Mem_set(toaddress, B, waccdesc) = readdata
                }
            };
            fromaddress = fromaddress + B;
            toaddress = toaddress + B;
            cpysize = cpysize - B;
            stagecpysize = stagecpysize - B;
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = cpysize;
                X_set(d, 64) = toaddress;
                X_set(s, 64) = fromaddress
            };
            ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(n, 64) = cpysize;
        X_set(d, 64) = toaddress;
        X_set(s, 64) = fromaddress;
        (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv
    };
    ()
}

val execute_aarch64_instrs_memory_mcpymset_set : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(2), int('s), MOPSStage) -> unit

function execute_aarch64_instrs_memory_mcpymset_set (d, n, options_name, s, stage) = {
    toaddress : bits(64) = X_read(d, 64);
    setsize : bits(64) = X_read(n, 64);
    let data : bits(8) = X_read(s, 8);
    nzcv : bits(4) = PSTATE.N @ (PSTATE.Z @ (PSTATE.C @ PSTATE.V));
    stagesetsize : bits(64) = undefined;
    let is_setg : bool = false;
    B : int = undefined;
    let supports_option_a : bool = SETOptionA();
    let privileged : bool = if [options_name[0]] == 0b1 then
      AArch64_IsUnprivAccessPriv()
    else
      PSTATE.EL != EL0;
    let nontemporal : bool = [options_name[1]] == 0b1;
    let accdesc : AccessDescriptor = CreateAccDescMOPS(MemOp_STORE, privileged, nontemporal);
    if stage == MOPSStage_Prologue then {
        if [setsize[63]] == 0b1 then {
            setsize = 0x7FFFFFFFFFFFFFFF
        };
        if supports_option_a then {
            nzcv = 0b0000;
            toaddress = toaddress + setsize;
            setsize = Zeros(64) - setsize
        } else {
            nzcv = 0b0010
        };
        stagesetsize = SETPreSizeChoice(toaddress, setsize, is_setg);
        assert([stagesetsize[63]] == [setsize[63]] | stagesetsize == Zeros(64));
        if SInt(setsize) > 0 then {
            assert(SInt(stagesetsize) <= SInt(setsize))
        } else {
            assert(SInt(stagesetsize) >= SInt(setsize))
        }
    } else {
        let postsize : bits(64) = SETPostSizeChoice(toaddress, setsize, is_setg);
        assert([postsize[63]] == [setsize[63]] | postsize == Zeros(64));
        let zero_size_exceptions : bool = MemSetZeroSizeCheck();
        if zero_size_exceptions | SInt(setsize) != 0 then {
            if supports_option_a then {
                if [nzcv[1]] == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                };
                ()
            } else {
                if [nzcv[1]] == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                };
                ()
            }
        };
        if stage == MOPSStage_Main then {
            stagesetsize = setsize - postsize;
            if MemSetParametersIllformedM(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            };
            ()
        } else {
            stagesetsize = postsize;
            if setsize != postsize | MemSetParametersIllformedE(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            };
            ()
        }
    };
    if SPESampleInFlight then {
        SPESampleMemSet()
    };
    if supports_option_a then {
        while SInt(stagesetsize) < 0 do {
            let 'B = SETSizeChoice(toaddress, setsize, 1);
            assert(B <= negate(1) * SInt(stagesetsize));
            assert(constraint('B in {1, 2, 4, 8, 16, 32, 64}));
            match B {
                1 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
                2 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
                4 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
                8 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
                16 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
                32 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B),
                64 => Mem_set(toaddress + setsize, B, accdesc) = Replicate(data, B)
            };
            setsize = setsize + B;
            stagesetsize = stagesetsize + B;
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = setsize
            };
            ()
        }
    } else {
        while UInt(stagesetsize) > 0 do {
            let 'B = SETSizeChoice(toaddress, setsize, 1);
            assert(B <= UInt(stagesetsize));
            assert(constraint('B in {1, 2, 4, 8, 16, 32, 64}));
            match B {
                1 => Mem_set(toaddress, B, accdesc) = Replicate(data, B),
                2 => Mem_set(toaddress, B, accdesc) = Replicate(data, B),
                4 => Mem_set(toaddress, B, accdesc) = Replicate(data, B),
                8 => Mem_set(toaddress, B, accdesc) = Replicate(data, B),
                16 => Mem_set(toaddress, B, accdesc) = Replicate(data, B),
                32 => Mem_set(toaddress, B, accdesc) = Replicate(data, B),
                64 => Mem_set(toaddress, B, accdesc) = Replicate(data, B)
            };
            toaddress = toaddress + B;
            setsize = setsize - B;
            stagesetsize = stagesetsize - B;
            if stage != MOPSStage_Prologue then {
                X_set(n, 64) = setsize;
                X_set(d, 64) = toaddress
            };
            ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(n, 64) = setsize;
        X_set(d, 64) = toaddress;
        (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv
    };
    ()
}
