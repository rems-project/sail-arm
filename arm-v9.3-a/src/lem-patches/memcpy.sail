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

// Case split in memory operation instructions.  Note that the set of
// allowed sizes comes from the assert in the underlying memory
// operations - it isn't clear to me from the prose that this is actually
// intended (e.g., that the core won't do a larger copy).

val execute_aarch64_instrs_memory_mcpymset_setg : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(2), int('s), MOPSStage) -> unit effect {escape, rreg, undef, wmem, wreg}

function execute_aarch64_instrs_memory_mcpymset_setg (d, n, options_name, s, stage) = {
    CheckMOPSEnabled();
    toaddress : bits(64) = X_read(64, d);
    setsize : bits(64) = X_read(64, n);
    let data : bits(8) = X_read(8, s);
    stagesetsize : bits(64) = undefined;
    let is_setg : bool = true;
    B : int = undefined;
    if HaveMTE2Ext() then {
        SetTagCheckedInstruction(false)
    } else ();
    let supports_option_a : bool = MemCpyOptionA();
    let acctype : AccType = MemSetAccessType(options_name);
    if stage == MOPSStage_Prologue then {
        if [setsize[63]] == 0b1 then {
            setsize = 0x7FFFFFFFFFFFFFF0
        } else ();
        if setsize != Zeros(64) & toaddress != Align(toaddress, TAG_GRANULE) then {
            let iswrite : bool = true;
            let secondstage : bool = false;
            AArch64_Abort(toaddress, AlignmentFault(acctype, iswrite, secondstage))
        } else ();
        if setsize != Align(setsize, TAG_GRANULE) then {
            let iswrite : bool = true;
            let secondstage : bool = false;
            AArch64_Abort(toaddress, AlignmentFault(acctype, iswrite, secondstage))
        } else ();
        if supports_option_a then {
            PSTATE.C = 0b0;
            toaddress = toaddress + setsize;
            setsize = Zeros(64) - setsize
        } else {
            PSTATE.C = 0b1
        };
        PSTATE.N = 0b0;
        PSTATE.V = 0b0;
        PSTATE.Z = 0b0;
        stagesetsize = SETPreSizeChoice(toaddress, setsize, is_setg);
        assert([stagesetsize[63]] == [setsize[63]] | stagesetsize == Zeros());
        assert(stagesetsize[3 .. 0] == 0b0000);
        if SInt(setsize) > 0 then {
            assert(SInt(stagesetsize) <= SInt(setsize))
        } else {
            assert(SInt(stagesetsize) >= SInt(setsize))
        }
    } else {
        let postsize : bits(64) = SETPostSizeChoice(toaddress, setsize, is_setg);
        assert([postsize[63]] == [setsize[63]] | postsize == Zeros());
        assert(postsize[3 .. 0] == 0b0000);
        let zero_size_exceptions : bool = MemSetZeroSizeCheck();
        if zero_size_exceptions | SInt(setsize) != 0 then {
            if supports_option_a then {
                if PSTATE.C == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                } else ()
            } else {
                if PSTATE.C == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                } else ()
            }
        } else ();
        if stage == MOPSStage_Main then {
            stagesetsize = setsize - postsize;
            if MemSetParametersIllformedM(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            } else ()
        } else {
            stagesetsize = postsize;
            if setsize != postsize | MemSetParametersIllformedE(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            } else ()
        };
        if setsize != Zeros(64) & toaddress != Align(toaddress, TAG_GRANULE) then {
            let iswrite : bool = true;
            let secondstage : bool = false;
            AArch64_Abort(toaddress, AlignmentFault(acctype, iswrite, secondstage))
        } else ();
        if setsize != Align(setsize, TAG_GRANULE) then {
            let iswrite : bool = true;
            let secondstage : bool = false;
            AArch64_Abort(toaddress, AlignmentFault(acctype, iswrite, secondstage))
        } else ()
    };
    tagstep : int = undefined;
    tag : bits(4) = undefined;
    tagaddr : bits(64) = undefined;
    if supports_option_a then {
        while SInt(stagesetsize) < 0 do {
            B = SETSizeChoice(toaddress, setsize, 16);
            assert(B <= negate(1) * SInt(stagesetsize));
            assert(B[3 .. 0] == 0b0000);
            let 'B = B in
              {
                  assert(constraint(('B * 8 == 8 | 'B * 8 == 16 | 'B * 8 == 32 | 'B * 8 == 64 | 'B * 8 == 128)));
                  match B {
                  1 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  2 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  4 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  8 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  16 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  }
              };
            tagstep = DIV(B, 16);
            tag = AArch64_AllocationTagFromAddress(toaddress + setsize);
            while tagstep > 0 do {
                tagaddr = toaddress + setsize + (tagstep - 1) * 16;
                AArch64_MemTag_set(tagaddr, acctype) = tag;
                tagstep = tagstep - 1
            };
            setsize = setsize + B;
            stagesetsize = stagesetsize + B;
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = setsize
            } else ()
        }
    } else {
        while UInt(stagesetsize) > 0 do {
            B = SETSizeChoice(toaddress, setsize, 16);
            assert(B <= UInt(stagesetsize));
            assert(B[3 .. 0] == 0b0000);
            let 'B = B in
              {
                  assert(constraint(('B * 8 == 8 | 'B * 8 == 16 | 'B * 8 == 32 | 'B * 8 == 64 | 'B * 8 == 128)));
                  match B {
                  1 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  2 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  4 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  8 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  16 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  }
              };
            tagstep = DIV(B, 16);
            tag = AArch64_AllocationTagFromAddress(toaddress);
            while tagstep > 0 do {
                tagaddr = toaddress + (tagstep - 1) * 16;
                AArch64_MemTag_set(tagaddr, acctype) = tag;
                tagstep = tagstep - 1
            };
            toaddress = toaddress + B;
            setsize = setsize - B;
            stagesetsize = stagesetsize - B;
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = setsize;
                X_set(64, d) = toaddress
            } else ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(64, n) = setsize;
        X_set(64, d) = toaddress
    } else ()
}

val execute_aarch64_instrs_memory_mcpymset_cpy : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(4), int('s), MOPSStage) -> unit effect {escape, rreg, undef, wmem, wreg}

function execute_aarch64_instrs_memory_mcpymset_cpy (d, n, options_name, s, stage) = {
    racctype : AccType = undefined;
    wacctype : AccType = undefined;
    CheckMOPSEnabled();
    let 'N = MaxBlockSizeCopiedBytes();
    toaddress : bits(64) = X_read(64, d);
    fromaddress : bits(64) = X_read(64, s);
    cpysize : bits(64) = X_read(64, n);
    stagecpysize : bits(64) = undefined;
    //readdata : bits(8 * 'N) = undefined;
    B : int = undefined;
    if HaveMTE2Ext() then {
        SetTagCheckedInstruction(true)
    } else ();
    let supports_option_a : bool = MemCpyOptionA();
    (racctype, wacctype) = MemCpyAccessTypes(options_name);
    if stage == MOPSStage_Prologue then {
        if cpysize[63 .. 55] != 0b000000000 then {
            cpysize = 0x007FFFFFFFFFFFFF
        } else ();
        forward : bool = undefined;
        if UInt(fromaddress[55 .. 0]) > UInt(toaddress[55 .. 0]) & UInt(fromaddress[55 .. 0]) < UInt(toaddress[55 .. 0] + cpysize[55 .. 0]) then {
            forward = true
        } else if UInt(fromaddress[55 .. 0]) < UInt(toaddress[55 .. 0]) & UInt(fromaddress[55 .. 0] + cpysize[55 .. 0]) > UInt(toaddress[55 .. 0]) then {
            forward = false
        } else {
            forward = MemCpyDirectionChoice(fromaddress, toaddress, cpysize)
        };
        if supports_option_a then {
            PSTATE.C = 0b0;
            PSTATE.N = 0b0;
            if forward then {
                toaddress = toaddress + cpysize;
                fromaddress = fromaddress + cpysize;
                cpysize = Zeros(64) - cpysize
            } else ()
        } else {
            PSTATE.C = 0b1;
            if not_bool(forward) then {
                toaddress = toaddress + cpysize;
                fromaddress = fromaddress + cpysize;
                PSTATE.N = 0b1
            } else {
                PSTATE.N = 0b0
            }
        };
        PSTATE.V = 0b0;
        PSTATE.Z = 0b0;
        stagecpysize = CPYPreSizeChoice(toaddress, fromaddress, cpysize);
        assert([stagecpysize[63]] == [cpysize[63]] | stagecpysize == Zeros());
        if SInt(cpysize) > 0 then {
            assert(SInt(stagecpysize) <= SInt(cpysize))
        } else {
            assert(SInt(stagecpysize) >= SInt(cpysize))
        }
    } else {
        let zero_size_exceptions : bool = MemCpyZeroSizeCheck();
        if zero_size_exceptions | SInt(cpysize) != 0 then {
            if supports_option_a then {
                if PSTATE.C == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                } else ()
            } else {
                if PSTATE.C == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                } else ()
            }
        } else ();
        let postsize : bits(64) = CPYPostSizeChoice(toaddress, fromaddress, cpysize);
        assert([postsize[63]] == [cpysize[63]] | SInt(postsize) == 0);
        if stage == MOPSStage_Main then {
            stagecpysize = cpysize - postsize;
            if MemCpyParametersIllformedM(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            } else ()
        } else {
            stagecpysize = postsize;
            if cpysize != postsize | MemCpyParametersIllformedE(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            } else ()
        }
    };
    if supports_option_a then {
        while SInt(stagecpysize) != 0 do {
            B = CPYSizeChoice(toaddress, fromaddress, cpysize);
            let 'B = B in
              {
                  if SInt(cpysize) < 0 then {
                      assert(B <= negate(1) * SInt(stagecpysize));
                      assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                      assert(constraint('B in {1, 2, 4, 8, 16}));
                      //readdata[B * 8 - 1 .. 0] = Mem_read(fromaddress + cpysize, B, racctype);
                      //Mem_set(toaddress + cpysize, B, wacctype) = readdata[B * 8 - 1 .. 0];
                      match B {
                      1 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      2 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      4 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      8 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      16 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      }
                      };
                      cpysize = cpysize + B;
                      stagecpysize = stagecpysize + B
                  } else {
                      assert(B <= SInt(stagecpysize));
                      cpysize = cpysize - B;
                      stagecpysize = stagecpysize - B;
                      assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                      assert(constraint('B in {1, 2, 4, 8, 16}));
                      //readdata[B * 8 - 1 .. 0] = Mem_read(fromaddress + cpysize, B, racctype);
                      //Mem_set(toaddress + cpysize, B, wacctype) = readdata[B * 8 - 1 .. 0]
                      match B {
                      1 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      2 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      4 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      8 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      },
                      16 => {
                          let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                          Mem_set(toaddress + cpysize, B, wacctype) = readdata;
                      }
                      };
                  }
              };
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = cpysize
            } else ()
        }
    } else {
        while UInt(stagecpysize) > 0 do {
            B = CPYSizeChoice(toaddress, fromaddress, cpysize);
            assert(B <= UInt(stagecpysize));
            let 'B = B in
              {
                  if PSTATE.N == 0b0 then {
                      assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                      assert(constraint('B in {1, 2, 4, 8, 16}));
                      //readdata[B * 8 - 1 .. 0] = Mem_read(fromaddress, B, racctype);
                      //Mem_set(toaddress, B, wacctype) = readdata[B * 8 - 1 .. 0];
                      match B {
                      1 => {
                          let readdata = Mem_read(fromaddress, B, racctype);
                          Mem_set(toaddress, B, wacctype) = readdata;
                      },
                      2 => {
                          let readdata = Mem_read(fromaddress, B, racctype);
                          Mem_set(toaddress, B, wacctype) = readdata;
                      },
                      4 => {
                          let readdata = Mem_read(fromaddress, B, racctype);
                          Mem_set(toaddress, B, wacctype) = readdata;
                      },
                      8 => {
                          let readdata = Mem_read(fromaddress, B, racctype);
                          Mem_set(toaddress, B, wacctype) = readdata;
                      },
                      16 => {
                          let readdata = Mem_read(fromaddress, B, racctype);
                          Mem_set(toaddress, B, wacctype) = readdata;
                      },
                      };
                      fromaddress = fromaddress + B;
                      toaddress = toaddress + B
                  } else {
                      assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                      assert(constraint('B in {1, 2, 4, 8, 16}));
                      //readdata[B * 8 - 1 .. 0] = Mem_read(fromaddress - B, B, racctype);
                      //Mem_set(toaddress - B, B, wacctype) = readdata[B * 8 - 1 .. 0];
                      match B {
                      1 => {
                          let readdata = Mem_read(fromaddress - B, B, racctype);
                          Mem_set(toaddress - B, B, wacctype) = readdata;
                      },
                      2 => {
                          let readdata = Mem_read(fromaddress - B, B, racctype);
                          Mem_set(toaddress - B, B, wacctype) = readdata;
                      },
                      4 => {
                          let readdata = Mem_read(fromaddress - B, B, racctype);
                          Mem_set(toaddress - B, B, wacctype) = readdata;
                      },
                      8 => {
                          let readdata = Mem_read(fromaddress - B, B, racctype);
                          Mem_set(toaddress - B, B, wacctype) = readdata;
                      },
                      16 => {
                          let readdata = Mem_read(fromaddress - B, B, racctype);
                          Mem_set(toaddress - B, B, wacctype) = readdata;
                      },
                      };
                      fromaddress = fromaddress - B;
                      toaddress = toaddress - B
                  }
              };
            cpysize = cpysize - B;
            stagecpysize = stagecpysize - B;
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = cpysize;
                X_set(64, d) = toaddress;
                X_set(64, s) = fromaddress
            } else ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(64, n) = cpysize;
        X_set(64, d) = toaddress;
        X_set(64, s) = fromaddress
    } else ()
}

val execute_aarch64_instrs_memory_mcpymset_cpyf : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(4), int('s), MOPSStage) -> unit effect {escape, rreg, undef, wmem, wreg}

function execute_aarch64_instrs_memory_mcpymset_cpyf (d, n, options_name, s, stage) = {
    racctype : AccType = undefined;
    wacctype : AccType = undefined;
    CheckMOPSEnabled();
    let 'N = MaxBlockSizeCopiedBytes();
    toaddress : bits(64) = X_read(64, d);
    fromaddress : bits(64) = X_read(64, s);
    cpysize : bits(64) = X_read(64, n);
    stagecpysize : bits(64) = undefined;
    //readdata : bits(8 * 'N) = undefined;
    B : int = undefined;
    if HaveMTE2Ext() then {
        SetTagCheckedInstruction(true)
    } else ();
    let supports_option_a : bool = MemCpyOptionA();
    (racctype, wacctype) = MemCpyAccessTypes(options_name);
    if stage == MOPSStage_Prologue then {
        if [cpysize[63]] == 0b1 then {
            cpysize = 0x7FFFFFFFFFFFFFFF
        } else ();
        if supports_option_a then {
            PSTATE.C = 0b0;
            toaddress = toaddress + cpysize;
            fromaddress = fromaddress + cpysize;
            cpysize = Zeros(64) - cpysize
        } else {
            PSTATE.C = 0b1
        };
        PSTATE.N = 0b0;
        PSTATE.V = 0b0;
        PSTATE.Z = 0b0;
        stagecpysize = CPYPreSizeChoice(toaddress, fromaddress, cpysize);
        assert([stagecpysize[63]] == [cpysize[63]] | stagecpysize == Zeros());
        if SInt(cpysize) > 0 then {
            assert(SInt(stagecpysize) <= SInt(cpysize))
        } else {
            assert(SInt(stagecpysize) >= SInt(cpysize))
        }
    } else {
        let zero_size_exceptions : bool = MemCpyZeroSizeCheck();
        if zero_size_exceptions | SInt(cpysize) != 0 then {
            if supports_option_a then {
                if PSTATE.C == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                } else ()
            } else {
                if PSTATE.C == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
                } else ()
            }
        } else ();
        let postsize : bits(64) = CPYPostSizeChoice(toaddress, fromaddress, cpysize);
        assert([postsize[63]] == [cpysize[63]] | SInt(postsize) == 0);
        if stage == MOPSStage_Main then {
            stagecpysize = cpysize - postsize;
            if MemCpyParametersIllformedM(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            } else ()
        } else {
            stagecpysize = postsize;
            if cpysize != postsize | MemCpyParametersIllformedE(toaddress, fromaddress, cpysize) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemCpyException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name)
            } else ()
        }
    };
    if supports_option_a then {
        while SInt(stagecpysize) != 0 do {
            B = CPYSizeChoice(toaddress, fromaddress, cpysize);
            assert(B <= negate(1) * SInt(stagecpysize));
            let 'B = B;
            /*let 'B = B in
              {
                  assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                  assert(constraint('B in {1, 2, 4, 8, 16}));
                  readdata[B * 8 - 1 .. 0] = Mem_read(fromaddress + cpysize, B, racctype)
              };
            let 'B = B in
              {
                  assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                  assert(constraint(('B * 8 == 8 | 'B * 8 == 16 | 'B * 8 == 32 | 'B * 8 == 64 | 'B * 8 == 128)));
                  Mem_set(toaddress + cpysize, B, wacctype) = readdata[B * 8 - 1 .. 0]
              };*/
            assert(constraint('B in {1, 2, 4, 8, 16}));
            match B {
            1 => {
                let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                Mem_set(toaddress + cpysize, B, wacctype) = readdata;
            },
            2 => {
                let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                Mem_set(toaddress + cpysize, B, wacctype) = readdata;
            },
            4 => {
                let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                Mem_set(toaddress + cpysize, B, wacctype) = readdata;
            },
            8 => {
                let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                Mem_set(toaddress + cpysize, B, wacctype) = readdata;
            },
            16 => {
                let readdata = Mem_read(fromaddress + cpysize, B, racctype);
                Mem_set(toaddress + cpysize, B, wacctype) = readdata;
            },
            };
            cpysize = cpysize + B;
            stagecpysize = stagecpysize + B;
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = cpysize
            } else ()
        }
    } else {
        while UInt(stagecpysize) > 0 do {
            B = CPYSizeChoice(toaddress, fromaddress, cpysize);
            assert(B <= UInt(stagecpysize));
            let 'B = B;
            /*let 'B = B in
              {
                  assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                  assert(constraint('B in {1, 2, 4, 8, 16}));
                  readdata[B * 8 - 1 .. 0] = Mem_read(fromaddress, B, racctype)
              };
            let 'B = B in
              {
                  assert(constraint((0 <= 'B * 8 - 1 & 'B * 8 - 1 < 8 * 'N)));
                  assert(constraint(('B * 8 == 8 | 'B * 8 == 16 | 'B * 8 == 32 | 'B * 8 == 64 | 'B * 8 == 128)));
                  Mem_set(toaddress, B, wacctype) = readdata[B * 8 - 1 .. 0]
              };*/
            assert(constraint('B in {1, 2, 4, 8, 16}));
            match B {
            1 => {
                let readdata = Mem_read(fromaddress, B, racctype);
                Mem_set(toaddress, B, wacctype) = readdata;
            },
            2 => {
                let readdata = Mem_read(fromaddress, B, racctype);
                Mem_set(toaddress, B, wacctype) = readdata;
            },
            4 => {
                let readdata = Mem_read(fromaddress, B, racctype);
                Mem_set(toaddress, B, wacctype) = readdata;
            },
            8 => {
                let readdata = Mem_read(fromaddress, B, racctype);
                Mem_set(toaddress, B, wacctype) = readdata;
            },
            16 => {
                let readdata = Mem_read(fromaddress, B, racctype);
                Mem_set(toaddress, B, wacctype) = readdata;
            },
            };
            fromaddress = fromaddress + B;
            toaddress = toaddress + B;
            cpysize = cpysize - B;
            stagecpysize = stagecpysize - B;
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = cpysize;
                X_set(64, d) = toaddress;
                X_set(64, s) = fromaddress
            } else ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(64, n) = cpysize;
        X_set(64, d) = toaddress;
        X_set(64, s) = fromaddress
    } else ()
}

val execute_aarch64_instrs_memory_mcpymset_set : forall 'd 'n 's,
  (0 <= 's & 's <= 31 & 0 <= 'n & 'n <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('n), bits(2), int('s), MOPSStage) -> unit effect {escape, rreg, undef, wmem, wreg}

function execute_aarch64_instrs_memory_mcpymset_set (d, n, options_name, s, stage) = {
    CheckMOPSEnabled();
    toaddress : bits(64) = X_read(64, d);
    setsize : bits(64) = X_read(64, n);
    let data : bits(8) = X_read(8, s);
    stagesetsize : bits(64) = undefined;
    let is_setg : bool = false;
    B : int = undefined;
    if HaveMTE2Ext() then {
        SetTagCheckedInstruction(true)
    } else ();
    let supports_option_a : bool = MemCpyOptionA();
    let acctype : AccType = MemSetAccessType(options_name);
    if stage == MOPSStage_Prologue then {
        if [setsize[63]] == 0b1 then {
            setsize = 0x007FFFFFFFFFFFF0
        } else ();
        if supports_option_a then {
            PSTATE.C = 0b0;
            toaddress = toaddress + setsize;
            setsize = Zeros(64) - setsize
        } else {
            PSTATE.C = 0b1
        };
        PSTATE.N = 0b0;
        PSTATE.V = 0b0;
        PSTATE.Z = 0b0;
        stagesetsize = SETPreSizeChoice(toaddress, setsize, is_setg);
        assert([stagesetsize[63]] == [setsize[63]] | stagesetsize == Zeros());
        if SInt(setsize) > 0 then {
            assert(SInt(stagesetsize) <= SInt(setsize))
        } else {
            assert(SInt(stagesetsize) >= SInt(setsize))
        }
    } else {
        let postsize : bits(64) = SETPostSizeChoice(toaddress, setsize, is_setg);
        assert([postsize[63]] == [setsize[63]] | postsize == Zeros());
        let zero_size_exceptions : bool = MemSetZeroSizeCheck();
        if zero_size_exceptions | SInt(setsize) != 0 then {
            if supports_option_a then {
                if PSTATE.C == 0b1 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                } else ()
            } else {
                if PSTATE.C == 0b0 then {
                    let wrong_option : bool = true;
                    let from_epilogue : bool = stage == MOPSStage_Epilogue;
                    MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
                } else ()
            }
        } else ();
        if stage == MOPSStage_Main then {
            stagesetsize = setsize - postsize;
            if MemSetParametersIllformedM(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = false;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            } else ()
        } else {
            stagesetsize = postsize;
            if setsize != postsize | MemSetParametersIllformedE(toaddress, setsize, is_setg) then {
                let wrong_option : bool = false;
                let from_epilogue : bool = true;
                MismatchedMemSetException(supports_option_a, d, s, n, wrong_option, from_epilogue, options_name, is_setg)
            } else ()
        }
    };
    if supports_option_a then {
        while SInt(stagesetsize) < 0 do {
            B = SETSizeChoice(toaddress, setsize, 1);
            assert(B <= negate(1) * SInt(stagesetsize));
            let 'B = B in
              {
                  assert(constraint(('B * 8 == 8 | 'B * 8 == 16 | 'B * 8 == 32 | 'B * 8 == 64 | 'B * 8 == 128)));
                  match B {
                  1 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  2 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  4 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  8 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  16 => Mem_set(toaddress + setsize, B, acctype) = Replicate(data, B),
                  }
              };
            setsize = setsize + B;
            stagesetsize = stagesetsize + B;
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = setsize
            } else ()
        }
    } else {
        while UInt(stagesetsize) > 0 do {
            B = SETSizeChoice(toaddress, setsize, 1);
            assert(B <= UInt(stagesetsize));
            let 'B = B in
              {
                  assert(constraint(('B * 8 == 8 | 'B * 8 == 16 | 'B * 8 == 32 | 'B * 8 == 64 | 'B * 8 == 128)));
                  match B {
                  1 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  2 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  4 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  8 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  16 => Mem_set(toaddress, B, acctype) = Replicate(data, B),
                  }
              };
            toaddress = toaddress + B;
            setsize = setsize - B;
            stagesetsize = stagesetsize - B;
            if stage != MOPSStage_Prologue then {
                X_set(64, n) = setsize;
                X_set(64, d) = toaddress
            } else ()
        }
    };
    if stage == MOPSStage_Prologue then {
        X_set(64, n) = setsize;
        X_set(64, d) = toaddress
    } else ()
}
