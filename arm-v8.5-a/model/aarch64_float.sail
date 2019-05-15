/**************************************************************************/
/* BSD 3-clause Clear License                                             */
/*                                                                        */
/* Copyright (c) 2019                                                     */
/*   Arm Limited (or its affiliates),                                     */
/*   Alasdair Armstrong,                                                  */
/*   Alastair Reid,                                                       */
/*   Thomas Bauereiss,                                                    */
/*   Peter Sewell,                                                        */
/*   Kathryn Gray,                                                        */
/*   Anthony Fox                                                          */
/*                                                                        */
/* All rights reserved.                                                   */
/*                                                                        */
/* Redistribution and use in source and binary forms, with or without     */
/* modification, are permitted (subject to the limitations in the         */
/* disclaimer below) provided that the following conditions are met:      */
/*                                                                        */
/* 	* Redistributions of source code must retain the above            */
/*        copyright notice, this list of conditions and the following     */
/* 	  disclaimer.                                                     */
/*      * Redistributions in binary form must reproduce the above         */
/*        copyright notice, this list of conditions and the following     */
/*        disclaimer in the documentation and/or other materials          */
/* 	  provided with the distribution.                                 */
/* 	* Neither the name of ARM Limited nor the names of its            */
/*        contributors may be used to endorse or promote products         */
/*        derived from this software without specific prior written       */
/*        permission.                                                     */
/*                                                                        */
/* NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE        */
/* GRANTED BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT    */
/* HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED            */
/* WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF   */
/* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE               */
/* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE  */
/* LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR    */
/* CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF   */
/* SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        */
/* BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,  */
/* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE   */
/* OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN */
/* IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                          */
/**************************************************************************/

val __UNKNOWN_real : unit -> real

function __UNKNOWN_real () = {
    0.0
}

val HaveFP16Ext : unit -> bool

function HaveFP16Ext () = {
    true
}

val __UNKNOWN_FPUnaryOp : unit -> FPUnaryOp

function __UNKNOWN_FPUnaryOp () = {
    FPUnaryOp_ABS
}

val __UNKNOWN_FPType : unit -> FPType

function __UNKNOWN_FPType () = {
    FPType_Nonzero
}

val __UNKNOWN_FPRounding : unit -> FPRounding

function __UNKNOWN_FPRounding () = {
    FPRounding_TIEEVEN
}

val __UNKNOWN_FPMaxMinOp : unit -> FPMaxMinOp

function __UNKNOWN_FPMaxMinOp () = {
    FPMaxMinOp_MAX
}

val FPDecodeRounding : bits(2) -> FPRounding

function FPDecodeRounding rmode = {
    match rmode {
      0b00 => {
          return(FPRounding_TIEEVEN)
      },
      0b01 => {
          return(FPRounding_POSINF)
      },
      0b10 => {
          return(FPRounding_NEGINF)
      },
      0b11 => {
          return(FPRounding_ZERO)
      }
    }
}

val FPRoundingMode : bits(32) -> FPRounding

function FPRoundingMode fpcr = {
    FPDecodeRounding(slice(fpcr, 22, 2))
}

val __UNKNOWN_FPConvOp : unit -> FPConvOp

function __UNKNOWN_FPConvOp () = {
    FPConvOp_CVT_FtoI
}

val HaveFrintExt : unit -> bool

function HaveFrintExt () = {
    HasArchVersion(ARMv8p5)
}

val HaveFJCVTZSExt : unit -> bool

function HaveFJCVTZSExt () = {
    HasArchVersion(ARMv8p3)
}

val aget_Vpart : forall 'width 'n 'part,
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}).
  (implicit('width), int('n), int('part)) -> bits('width) effect {escape, rreg}

function aget_Vpart (width, n, part) = {
    assert(n >= 0 & n <= 31);
    assert(part == 0 | part == 1);
    if part == 0 then {
        assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64);
        return(slice(_V[n], 0, 'width))
    } else {
        assert('width == 32 | 'width == 64);
        return(slice(_V[n], 'width, 'width))
    }
}

overload Vpart = {aget_Vpart}

val FPNeg : forall ('N : Int), 'N >= 0. bits('N) -> bits('N) effect {escape}

function FPNeg op = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    ~([op['N - 1]]) @ slice(op, 0, 'N - 1)
}

val FPAbs : forall ('N : Int), 'N >= 0. bits('N) -> bits('N) effect {escape}

function FPAbs op = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    0b0 @ slice(op, 0, 'N - 1)
}

val UnsignedSatQ : forall ('N : Int) ('i : Int), 'N >= 0.
  (int('i), int('N)) -> (bits('N), bool) effect {undef}

function UnsignedSatQ (i, N) = {
    result : int = undefined : int;
    saturated : bool = undefined : bool;
    if i > 2 ^ N - 1 then {
        result = 2 ^ N - 1;
        saturated = true
    } else {
        if i < 0 then {
            result = 0;
            saturated = true
        } else {
            result = i;
            saturated = false
        }
    };
    return((__GetSlice_int(N, result, 0), saturated))
}

val SignedSatQ : forall ('N : Int) ('i : Int), 'N >= 0.
  (int('i), int('N)) -> (bits('N), bool) effect {undef}

function SignedSatQ (i, N) = {
    result : int = undefined : int;
    saturated : bool = undefined : bool;
    if i > 2 ^ (N - 1) - 1 then {
        result = 2 ^ (N - 1) - 1;
        saturated = true
    } else {
        if i < negate(2 ^ (N - 1)) then {
            result = negate(2 ^ (N - 1));
            saturated = true
        } else {
            result = i;
            saturated = false
        }
    };
    return((__GetSlice_int(N, result, 0), saturated))
}

val SatQ : forall ('N : Int) ('i : Int) ('unsigned : Bool), 'N >= 0.
  (int('i), int('N), bool('unsigned)) -> (bits('N), bool) effect {undef}

function SatQ (i, N, unsigned) = {
    result : bits('N) = undefined : bits('N);
    sat : bool = undefined : bool;
    (result, sat) = if unsigned then UnsignedSatQ(i, N) else SignedSatQ(i, N);
    return((result, sat))
}

val aset_Vpart : forall 'width 'n 'part,
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}).
  (int('n), int('part), bits('width)) -> unit effect {escape, rreg, wreg}

function aset_Vpart (n, part, value_name) = {
    assert(n >= 0 & n <= 31);
    assert(part == 0 | part == 1);
    if part == 0 then {
        assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64);
        _V[n] = ZeroExtend(value_name, 128)
    } else {
        assert('width == 64);
        __tc1 : bits(128) = _V[n];
        __tc1 = __SetSlice_bits(128, 'width, __tc1, 'width, slice(value_name, 0, 'width));
        _V[n] = __tc1
    }
}

overload Vpart = {aset_Vpart}

val FPZero : forall ('N : Int).
  (implicit('N), bits(1)) -> bits('N) effect {escape}

function FPZero (N, sign) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    let exp : bits('E) = Zeros(E);
    let frac : bits('N - 1 - 'E) = Zeros(F);
    (sign @ exp) @ frac
}

val FPTwo : forall ('N : Int).
  (implicit('N), bits(1)) -> bits('N) effect {escape}

function FPTwo (N, sign) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    let exp : bits('E) = 0b1 @ Zeros(E - 1);
    let frac : bits('N - 1 - 'E) = Zeros(F);
    (sign @ exp) @ frac
}

val FPThree : forall ('N : Int).
  (implicit('N), bits(1)) -> bits('N) effect {escape}

function FPThree (N, sign) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    let exp : bits('E) = 0b1 @ Zeros(E - 1);
    let frac : bits('N - 1 - 'E) = 0b1 @ Zeros(F - 1);
    (sign @ exp) @ frac
}

val VFPExpandImm : forall ('N : Int).
  (implicit('N), bits(8)) -> bits('N) effect {escape}

function VFPExpandImm (N, imm8) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - 'E - 1. int('n)} = 'N - E - 1;
    let sign = [imm8[7]];
    let exp : bits('E) = (~([imm8[6]]) @ replicate_bits([imm8[6]], E - 3)) @ slice(imm8, 4, 2);
    let frac : bits('N - 1 - 'E) = slice(imm8, 0, 4) @ Zeros(F - 4);
    (sign @ exp) @ frac
}

val FPMaxNormal : forall ('N : Int).
  (implicit('N), bits(1)) -> bits('N) effect {escape}

function FPMaxNormal (N, sign) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    let exp : bits('E) = Ones(E - 1) @ 0b0;
    let frac : bits('N - 1 - 'E) = Ones(F);
    (sign @ exp) @ frac
}

val FPInfinity : forall ('N : Int).
  (implicit('N), bits(1)) -> bits('N) effect {escape}

function FPInfinity (N, sign) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    let exp : bits('E) = Ones(E);
    let frac : bits('N - 1 - 'E) = Zeros(F);
    (sign @ exp) @ frac
}

val FPDefaultNaN : forall ('N : Int). implicit('N) -> bits('N) effect {escape}

function FPDefaultNaN N = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    let sign = 0b0;
    let exp : bits('E) = Ones(E);
    let frac : bits('N - 1 - 'E) = 0b1 @ Zeros(F - 1);
    (sign @ exp) @ frac
}

val FPConvertNaN : forall ('N : Int) ('M : Int), 'N >= 0.
  (implicit('M), bits('N)) -> bits('M) effect {escape, undef}

function FPConvertNaN (M, op) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    assert('M == 16 | 'M == 32 | 'M == 64);
    result : bits('M) = undefined : bits('M);
    frac : bits(51) = undefined : bits(51);
    let sign = [op['N - 1]];
    match 'N {
      64 => {
          frac = slice(op, 0, 51)
      },
      32 => {
          frac = slice(op, 0, 22) @ Zeros(29)
      },
      16 => {
          frac = slice(op, 0, 9) @ Zeros(42)
      }
    };
    let frac = frac;
    match 'M {
      64 => {
          result = (sign @ Ones('M - 52)) @ frac
      },
      32 => {
          result = (sign @ Ones('M - 23)) @ slice(frac, 29, 22)
      },
      16 => {
          result = (sign @ Ones('M - 10)) @ slice(frac, 42, 9)
      }
    };
    let result = result;
    result
}

val FPProcessException : (FPExc, bits(32)) -> unit effect {escape, rreg, undef, wreg}

function FPProcessException (exception, fpcr) = {
    cumul : int = undefined : int;
    match exception {
      FPExc_InvalidOp => {
          cumul = 0
      },
      FPExc_DivideByZero => {
          cumul = 1
      },
      FPExc_Overflow => {
          cumul = 2
      },
      FPExc_Underflow => {
          cumul = 3
      },
      FPExc_Inexact => {
          cumul = 4
      },
      FPExc_InputDenorm => {
          cumul = 7
      }
    };
    let cumul = cumul;
    let enable : int = cumul + 8;
    if [fpcr[enable]] == 0b1 then {
        throw(Error_Implementation_Defined("floating-point trap handling"))
    } else {
        if UsingAArch32() then {
            FPSCR = __SetSlice_bits(32, 1, FPSCR, cumul, 0b1)
        } else {
            FPSR = __SetSlice_bits(32, 1, FPSR, cumul, 0b1)
        }
    };
    return()
}

val FPRoundBase : forall ('N : Int), 'N >= 0.
  (implicit('N), real, bits(32), FPRounding) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRoundBase (N, op, fpcr, rounding) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    assert(op != 0.0);
    assert(rounding != FPRounding_TIEAWAY);
    result : bits('N) = undefined : bits('N);
    E : int = undefined : int;
    F : int = undefined : int;
    minimum_exp : int = undefined : int;
    if 'N == 16 then {
        minimum_exp = negate(14);
        E = 5;
        F = 10
    } else {
        if 'N == 32 then {
            minimum_exp = negate(126);
            E = 8;
            F = 23
        } else {
            minimum_exp = negate(1022);
            E = 11;
            F = 52
        }
    };
    let 'F = F;
    let 'E = E;
    assert('F < 'N);
    assert(constraint(('F in {10, 23, 52} & 'E in {5, 8, 11})));
    mantissa : real = undefined : real;
    sign : bits(1) = undefined : bits(1);
    if op < 0.0 then {
        sign = 0b1;
        mantissa = negate(op)
    } else {
        sign = 0b0;
        mantissa = op
    };
    exponent : int = undefined : int;
    exponent = 0;
    while mantissa < 1.0 do {
        mantissa = mantissa * 2.0;
        exponent = exponent - 1
    };
    while mantissa >= 2.0 do {
        mantissa = mantissa / 2.0;
        exponent = exponent + 1
    };
    if ([fpcr[24]] == 0b1 & 'N != 16 | [fpcr[19]] == 0b1 & 'N == 16) & exponent < minimum_exp then {
        if UsingAArch32() then {
            FPSCR = __SetSlice_bits(32, 1, FPSCR, 3, 0b1)
        } else {
            FPSR = __SetSlice_bits(32, 1, FPSR, 3, 0b1)
        };
        return(FPZero(sign))
    };
    biased_exp : int = undefined : int;
    biased_exp = max(exponent - minimum_exp + 1, 0);
    if biased_exp == 0 then {
        mantissa = mantissa / 2.0 ^ (minimum_exp - exponent)
    };
    int_mant : int = undefined : int;
    int_mant = RoundDown(mantissa * 2.0 ^ F);
    error : real = undefined : real;
    error = mantissa * 2.0 ^ F - Real(int_mant);
    if biased_exp == 0 & (error != 0.0 | [fpcr[11]] == 0b1) then {
        FPProcessException(FPExc_Underflow, fpcr)
    };
    overflow_to_inf : bool = undefined : bool;
    round_up : bool = undefined : bool;
    match rounding {
      FPRounding_TIEEVEN => {
          round_up = error > 0.5 | error == 0.5 & __GetSlice_int(1, int_mant, 0) == 0b1;
          overflow_to_inf = true
      },
      FPRounding_POSINF => {
          round_up = error != 0.0 & sign == 0b0;
          overflow_to_inf = sign == 0b0
      },
      FPRounding_NEGINF => {
          round_up = error != 0.0 & sign == 0b1;
          overflow_to_inf = sign == 0b1
      },
      FPRounding_ZERO => {
          round_up = false;
          overflow_to_inf = false
      },
      FPRounding_ODD => {
          round_up = false;
          overflow_to_inf = false
      }
    };
    if round_up then {
        int_mant = int_mant + 1;
        if int_mant == pow2(F) then {
            biased_exp = 1
        };
        if int_mant == pow2(F + 1) then {
            biased_exp = biased_exp + 1;
            int_mant = int_mant / 2
        }
    };
    if error != 0.0 & rounding == FPRounding_ODD then {
        int_mant = __SetSlice_int(1, int_mant, 0, 0b1)
    };
    if 'N != 16 | [fpcr[26]] == 0b0 then {
        if biased_exp >= pow2(E) - 1 then {
            result = if overflow_to_inf then FPInfinity(sign) else FPMaxNormal(sign);
            FPProcessException(FPExc_Overflow, fpcr);
            error = 1.0
        } else {
            result = (sign @ __GetSlice_int('N - F - 1, biased_exp, 0)) @ __GetSlice_int(F, int_mant, 0)
        }
    } else {
        if biased_exp >= pow2(E) then {
            result = sign @ Ones('N - 1);
            FPProcessException(FPExc_InvalidOp, fpcr);
            error = 0.0
        } else {
            result = (sign @ __GetSlice_int('N - F - 1, biased_exp, 0)) @ __GetSlice_int(F, int_mant, 0)
        }
    };
    if error != 0.0 then {
        FPProcessException(FPExc_Inexact, fpcr)
    };
    result
}

val FPRoundCV : forall ('N : Int), 'N >= 0.
  (implicit('N), real, bits(32), FPRounding) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRoundCV (N, op, fpcr, rounding) = {
    let fpcr = __SetSlice_bits(32, 1, fpcr, 19, 0b0);
    FPRoundBase(op, fpcr, rounding)
}

val FPRound__0 : forall ('N : Int), 'N >= 0.
  (implicit('N), real, bits(32), FPRounding) -> bits('N) effect {escape, rreg, undef, wreg}

val FPRound__1 : forall ('N : Int), 'N >= 0.
  (implicit('N), real, bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

overload FPRound = {FPRound__0, FPRound__1}

function FPRound__0 (N, op, fpcr, rounding) = {
    let fpcr = __SetSlice_bits(32, 1, fpcr, 26, 0b0);
    FPRoundBase(op, fpcr, rounding)
}

function FPRound__1 (N, op, fpcr) = {
    FPRound(op, fpcr, FPRoundingMode(fpcr))
}

val FixedToFP : forall ('M : Int) ('N : Int) ('fbits : Int), 'M >= 0 & 'N >= 0.
  (implicit('N), bits('M), int('fbits), bool, bits(32), FPRounding) -> bits('N) effect {escape, undef, wreg, rreg}

function FixedToFP (N, op, fbits, unsigned, fpcr, rounding) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    assert('M == 16 | 'M == 32 | 'M == 64);
    result : bits('N) = undefined : bits('N);
    assert(fbits >= 0);
    assert(rounding != FPRounding_ODD);
    let int_operand : int = asl_Int(op, unsigned);
    let real_operand : real = Real(int_operand) / 2.0 ^ fbits;
    if real_operand == 0.0 then {
        result = FPZero(0b0)
    } else {
        result = FPRound(real_operand, fpcr, rounding)
    };
    result
}

val FPProcessNaN : forall ('N : Int), 'N >= 0.
  (FPType, bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPProcessNaN (typ, op, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    assert(typ == FPType_QNaN | typ == FPType_SNaN);
    topfrac : int = undefined : int;
    match 'N {
      16 => {
          topfrac = 9
      },
      32 => {
          topfrac = 22
      },
      64 => {
          topfrac = 51
      }
    };
    let topfrac = topfrac;
    result : bits('N) = undefined : bits('N);
    result = op;
    if typ == FPType_SNaN then {
        result = __SetSlice_bits('N, 1, result, topfrac, 0b1);
        FPProcessException(FPExc_InvalidOp, fpcr)
    };
    if [fpcr[25]] == 0b1 then {
        result = FPDefaultNaN()
    };
    result
}

val FPProcessNaNs3 : forall ('N : Int), ('N >= 0 & 'N >= 0 & 'N >= 0).
  (FPType, FPType, FPType, bits('N), bits('N), bits('N), bits(32)) -> (bool, bits('N)) effect {escape, rreg, undef, wreg}

function FPProcessNaNs3 (type1, type2, type3, op1, op2, op3, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    if type1 == FPType_SNaN then {
        done = true;
        result = FPProcessNaN(type1, op1, fpcr)
    } else {
        if type2 == FPType_SNaN then {
            done = true;
            result = FPProcessNaN(type2, op2, fpcr)
        } else {
            if type3 == FPType_SNaN then {
                done = true;
                result = FPProcessNaN(type3, op3, fpcr)
            } else {
                if type1 == FPType_QNaN then {
                    done = true;
                    result = FPProcessNaN(type1, op1, fpcr)
                } else {
                    if type2 == FPType_QNaN then {
                        done = true;
                        result = FPProcessNaN(type2, op2, fpcr)
                    } else {
                        if type3 == FPType_QNaN then {
                            done = true;
                            result = FPProcessNaN(type3, op3, fpcr)
                        } else {
                            done = false;
                            result = Zeros()
                        }
                    }
                }
            }
        }
    };
    return((done, result))
}

val FPProcessNaNs : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (FPType, FPType, bits('N), bits('N), bits(32)) -> (bool, bits('N)) effect {escape, rreg, undef, wreg}

function FPProcessNaNs (type1, type2, op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    if type1 == FPType_SNaN then {
        done = true;
        result = FPProcessNaN(type1, op1, fpcr)
    } else {
        if type2 == FPType_SNaN then {
            done = true;
            result = FPProcessNaN(type2, op2, fpcr)
        } else {
            if type1 == FPType_QNaN then {
                done = true;
                result = FPProcessNaN(type1, op1, fpcr)
            } else {
                if type2 == FPType_QNaN then {
                    done = true;
                    result = FPProcessNaN(type2, op2, fpcr)
                } else {
                    done = false;
                    result = Zeros()
                }
            }
        }
    };
    return((done, result))
}

val FPUnpackBase : forall ('N : Int), 'N >= 0.
  (bits('N), bits(32)) -> (FPType, bits(1), real) effect {escape, rreg, undef, wreg}

function FPUnpackBase (fpval, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    exp16 : bits(5) = undefined : bits(5);
    exp32 : bits(8) = undefined : bits(8);
    exp64 : bits(11) = undefined : bits(11);
    frac16 : bits(10) = undefined : bits(10);
    frac32 : bits(23) = undefined : bits(23);
    frac64 : bits(52) = undefined : bits(52);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    if 'N == 16 then {
        sign = [fpval[15]];
        exp16 = slice(fpval, 10, 5);
        frac16 = slice(fpval, 0, 10);
        if IsZero(exp16) then {
            if IsZero(frac16) | [fpcr[19]] == 0b1 then {
                typ = FPType_Zero;
                value_name = 0.0
            } else {
                typ = FPType_Nonzero;
                value_name = 2.0 ^ negate(14) * (Real(UInt(frac16)) * 2.0 ^ negate(10))
            }
        } else {
            if IsOnes(exp16) & [fpcr[26]] == 0b0 then {
                if IsZero(frac16) then {
                    typ = FPType_Infinity;
                    value_name = 2.0 ^ 1000000
                } else {
                    typ = if [frac16[9]] == 0b1 then FPType_QNaN else FPType_SNaN;
                    value_name = 0.0
                }
            } else {
                typ = FPType_Nonzero;
                value_name = 2.0 ^ (UInt(exp16) - 15) * (1.0 + Real(UInt(frac16)) * 2.0 ^ negate(10))
            }
        }
    } else {
        if 'N == 32 then {
            sign = [fpval[31]];
            exp32 = slice(fpval, 23, 8);
            frac32 = slice(fpval, 0, 23);
            if IsZero(exp32) then {
                if IsZero(frac32) | [fpcr[24]] == 0b1 then {
                    typ = FPType_Zero;
                    value_name = 0.0;
                    if ~(IsZero(frac32)) then {
                        FPProcessException(FPExc_InputDenorm, fpcr)
                    }
                } else {
                    typ = FPType_Nonzero;
                    value_name = 2.0 ^ negate(126) * (Real(UInt(frac32)) * 2.0 ^ negate(23))
                }
            } else {
                if IsOnes(exp32) then {
                    if IsZero(frac32) then {
                        typ = FPType_Infinity;
                        value_name = 2.0 ^ 1000000
                    } else {
                        typ = if [frac32[22]] == 0b1 then FPType_QNaN else FPType_SNaN;
                        value_name = 0.0
                    }
                } else {
                    typ = FPType_Nonzero;
                    value_name = 2.0 ^ (UInt(exp32) - 127) * (1.0 + Real(UInt(frac32)) * 2.0 ^ negate(23))
                }
            }
        } else {
            sign = [fpval[63]];
            exp64 = slice(fpval, 52, 11);
            frac64 = slice(fpval, 0, 52);
            if IsZero(exp64) then {
                if IsZero(frac64) | [fpcr[24]] == 0b1 then {
                    typ = FPType_Zero;
                    value_name = 0.0;
                    if ~(IsZero(frac64)) then {
                        FPProcessException(FPExc_InputDenorm, fpcr)
                    }
                } else {
                    typ = FPType_Nonzero;
                    value_name = 2.0 ^ negate(1022) * (Real(UInt(frac64)) * 2.0 ^ negate(52))
                }
            } else {
                if IsOnes(exp64) then {
                    if IsZero(frac64) then {
                        typ = FPType_Infinity;
                        value_name = 2.0 ^ 1000000
                    } else {
                        typ = if [frac64[51]] == 0b1 then FPType_QNaN else FPType_SNaN;
                        value_name = 0.0
                    }
                } else {
                    typ = FPType_Nonzero;
                    value_name = 2.0 ^ (UInt(exp64) - 1023) * (1.0 + Real(UInt(frac64)) * 2.0 ^ negate(52))
                }
            }
        }
    };
    if sign == 0b1 then {
        value_name = negate(value_name)
    };
    return((typ, sign, value_name))
}

val FPUnpackCV : forall ('N : Int), 'N >= 0.
  (bits('N), bits(32)) -> (FPType, bits(1), real) effect {escape, rreg, undef, wreg}

function FPUnpackCV (fpval, fpcr) = {
    let fpcr = __SetSlice_bits(32, 1, fpcr, 19, 0b0);
    fp_type : FPType = undefined : FPType;
    sign : bits(1) = undefined : bits(1);
    value_name : real = undefined : real;
    (fp_type, sign, value_name) = FPUnpackBase(fpval, fpcr);
    return((fp_type, sign, value_name))
}

val FPConvert__0 : forall ('N : Int) ('M : Int), 'N >= 0.
  (implicit('M), bits('N), bits(32), FPRounding) -> bits('M) effect {escape, rreg, undef, wreg}

val FPConvert__1 : forall ('N : Int) ('M : Int), 'N >= 0.
  (implicit('M), bits('N), bits(32)) -> bits('M) effect {escape, rreg, undef, wreg}

overload FPConvert = {FPConvert__0, FPConvert__1}

function FPConvert__0 (M, op, fpcr, rounding) = {
    assert('M == 16 | 'M == 32 | 'M == 64);
    assert('N == 16 | 'N == 32 | 'N == 64);
    result : bits('M) = undefined : bits('M);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpackCV(op, fpcr);
    let alt_hp : bool = 'M == 16 & [fpcr[26]] == 0b1;
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        if alt_hp then {
            result = FPZero(sign)
        } else {
            if [fpcr[25]] == 0b1 then {
                result = FPDefaultNaN()
            } else {
                result = FPConvertNaN(op)
            }
        };
        if typ == FPType_SNaN | alt_hp then {
            FPProcessException(FPExc_InvalidOp, fpcr)
        }
    } else {
        if typ == FPType_Infinity then {
            if alt_hp then {
                result = sign @ Ones('M - 1);
                FPProcessException(FPExc_InvalidOp, fpcr)
            } else {
                result = FPInfinity(sign)
            }
        } else {
            if typ == FPType_Zero then {
                result = FPZero(sign)
            } else {
                result = FPRoundCV(value_name, fpcr, rounding)
            }
        }
    };
    result
}

function FPConvert__1 (M, op, fpcr) = {
    FPConvert(op, fpcr, FPRoundingMode(fpcr))
}

val FPUnpack : forall ('N : Int), 'N >= 0.
  (bits('N), bits(32)) -> (FPType, bits(1), real) effect {escape, rreg, undef, wreg}

function FPUnpack (fpval, fpcr) = {
    let fpcr = __SetSlice_bits(32, 1, fpcr, 26, 0b0);
    fp_type : FPType = undefined : FPType;
    sign : bits(1) = undefined : bits(1);
    value_name : real = undefined : real;
    (fp_type, sign, value_name) = FPUnpackBase(fpval, fpcr);
    return((fp_type, sign, value_name))
}

val FPToFixedJS : forall ('M : Int) ('N : Int) ('Is64 : Bool), 'M >= 0.
  (implicit('N), bits('M), bits(32), bool('Is64)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPToFixedJS (N, op, fpcr, Is64) = {
    assert('M == 64 & 'N == 32);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(op, fpcr);
    Z : bits(1) = undefined : bits(1);
    Z = 0b1;
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        FPProcessException(FPExc_InvalidOp, fpcr);
        Z = 0b0
    };
    int_result : int = undefined : int;
    int_result = RoundDown(value_name);
    let error : real = value_name - Real(int_result);
    let round_it_up : bool = error != 0.0 & int_result < 0;
    if round_it_up then {
        int_result = int_result + 1
    };
    result : int = undefined : int;
    if int_result < 0 then {
        result = int_result - 2 ^ 32 * RoundUp(Real(int_result) / Real(2 ^ 32))
    } else {
        result = int_result - 2 ^ 32 * RoundDown(Real(int_result) / Real(2 ^ 32))
    };
    if int_result < negate(2 ^ 31) | int_result > 2 ^ 31 - 1 then {
        FPProcessException(FPExc_InvalidOp, fpcr);
        Z = 0b0
    } else {
        if error != 0.0 then {
            FPProcessException(FPExc_Inexact, fpcr);
            Z = 0b0
        }
    };
    if sign == 0b1 & value_name == 0.0 then {
        Z = 0b0
    };
    if typ == FPType_Infinity then {
        result = 0
    };
    if Is64 then {
        (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = (0b0 @ Z) @ 0b00
    } else {
        FPSCR = __SetSlice_bits(32, 4, FPSCR, 28, (0b0 @ Z) @ 0b00)
    };
    __GetSlice_int('N, result, 0)
}

val FPToFixed : forall 'N 'M 'fbits ('unsigned : Bool),
  ('N >= 0 & 'fbits >= 0).
  (implicit('M), bits('N), int('fbits), bool('unsigned), bits(32), FPRounding) -> bits('M) effect {escape, rreg, undef, wreg}

function FPToFixed (M, op, fbits, unsigned, fpcr, rounding) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    assert('M == 16 | 'M == 32 | 'M == 64);
    assert(fbits >= 0);
    assert(rounding != FPRounding_ODD);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(op, fpcr);
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        FPProcessException(FPExc_InvalidOp, fpcr)
    };
    let value_name = value_name * 2.0 ^ fbits;
    int_result : int = undefined : int;
    int_result = RoundDown(value_name);
    let error : real = value_name - Real(int_result);
    round_up : bool = undefined : bool;
    match rounding {
      FPRounding_TIEEVEN => {
          round_up = error > 0.5 | error == 0.5 & __GetSlice_int(1, int_result, 0) == 0b1
      },
      FPRounding_POSINF => {
          round_up = error != 0.0
      },
      FPRounding_NEGINF => {
          round_up = false
      },
      FPRounding_ZERO => {
          round_up = error != 0.0 & int_result < 0
      },
      FPRounding_TIEAWAY => {
          round_up = error > 0.5 | error == 0.5 & int_result >= 0
      }
    };
    let round_up = round_up;
    if round_up then {
        int_result = int_result + 1
    };
    overflow : bool = undefined : bool;
    result : bits('M) = undefined : bits('M);
    (result, overflow) = SatQ(int_result, 'M, unsigned);
    if overflow then {
        FPProcessException(FPExc_InvalidOp, fpcr)
    } else {
        if error != 0.0 then {
            FPProcessException(FPExc_Inexact, fpcr)
        }
    };
    result
}

val FPSqrt : forall ('N : Int), 'N >= 0.
  (bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPSqrt (op, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(op, fpcr);
    result : bits('N) = undefined : bits('N);
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        result = FPProcessNaN(typ, op, fpcr)
    } else {
        if typ == FPType_Zero then {
            result = FPZero(sign)
        } else {
            if typ == FPType_Infinity & sign == 0b0 then {
                result = FPInfinity(sign)
            } else {
                if sign == 0b1 then {
                    result = FPDefaultNaN();
                    FPProcessException(FPExc_InvalidOp, fpcr)
                } else {
                    result = FPRound(Sqrt(value_name), fpcr)
                }
            }
        }
    };
    result
}

val FPRoundIntN : forall 'N 'intsize,
  ('N >= 0 & 'intsize in {32, 64}).
  (bits('N), bits(32), FPRounding, int('intsize)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRoundIntN (op, fpcr, rounding, intsize) = {
    assert(rounding != FPRounding_ODD);
    assert('N == 32 | 'N == 64);
    assert(intsize == 32 | intsize == 64);
    exp : int = undefined : int;
    let 'E : {'n, 'n in {8, 11}. int('n)} = if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(op, fpcr);
    error : real = undefined : real;
    int_result : int = undefined : int;
    real_result : real = undefined : real;
    result : bits('N) = undefined : bits('N);
    round_up : bool = undefined : bool;
    if typ == FPType_SNaN | typ == FPType_QNaN | typ == FPType_Infinity then {
        if 'N == 32 then {
            exp = 126 + intsize;
            result = (0b1 @ __GetSlice_int(E, exp, 0)) @ Zeros(F)
        } else {
            exp = 1022 + intsize;
            result = (0b1 @ __GetSlice_int(E, exp, 0)) @ Zeros(F)
        };
        FPProcessException(FPExc_InvalidOp, fpcr)
    } else {
        if typ == FPType_Zero then {
            result = FPZero(sign)
        } else {
            int_result = RoundDown(value_name);
            error = value_name - Real(int_result);
            match rounding {
              FPRounding_TIEEVEN => {
                  round_up = error > 0.5 | error == 0.5 & __GetSlice_int(1, int_result, 0) == 0b1
              },
              FPRounding_POSINF => {
                  round_up = error != 0.0
              },
              FPRounding_NEGINF => {
                  round_up = false
              },
              FPRounding_ZERO => {
                  round_up = error != 0.0 & int_result < 0
              },
              FPRounding_TIEAWAY => {
                  round_up = error > 0.5 | error == 0.5 & int_result >= 0
              }
            };
            if round_up then {
                int_result = int_result + 1
            };
            if int_result > 2 ^ (intsize - 1) - 1 | int_result < negate(1) * 2 ^ (intsize - 1) then {
                if 'N == 32 then {
                    exp = 126 + intsize;
                    result = (0b1 @ __GetSlice_int(E, exp, 0)) @ Zeros(F)
                } else {
                    exp = 1022 + intsize;
                    result = (0b1 @ __GetSlice_int(E, exp, 0)) @ Zeros(F)
                };
                FPProcessException(FPExc_InvalidOp, fpcr);
                error = 0.0
            } else {
                real_result = Real(int_result);
                if real_result == 0.0 then {
                    result = FPZero(sign)
                } else {
                    result = FPRound(real_result, fpcr, FPRounding_ZERO)
                }
            };
            if error != 0.0 then {
                FPProcessException(FPExc_Inexact, fpcr)
            }
        }
    };
    result
}

val FPRoundInt : forall ('N : Int) ('exact : Bool), 'N >= 0.
  (bits('N), bits(32), FPRounding, bool('exact)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRoundInt (op, fpcr, rounding, exact) = {
    assert(rounding != FPRounding_ODD);
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(op, fpcr);
    error : real = undefined : real;
    int_result : int = undefined : int;
    real_result : real = undefined : real;
    result : bits('N) = undefined : bits('N);
    round_up : bool = undefined : bool;
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        result = FPProcessNaN(typ, op, fpcr)
    } else {
        if typ == FPType_Infinity then {
            result = FPInfinity(sign)
        } else {
            if typ == FPType_Zero then {
                result = FPZero(sign)
            } else {
                int_result = RoundDown(value_name);
                error = value_name - Real(int_result);
                match rounding {
                  FPRounding_TIEEVEN => {
                      round_up = error > 0.5 | error == 0.5 & __GetSlice_int(1, int_result, 0) == 0b1
                  },
                  FPRounding_POSINF => {
                      round_up = error != 0.0
                  },
                  FPRounding_NEGINF => {
                      round_up = false
                  },
                  FPRounding_ZERO => {
                      round_up = error != 0.0 & int_result < 0
                  },
                  FPRounding_TIEAWAY => {
                      round_up = error > 0.5 | error == 0.5 & int_result >= 0
                  }
                };
                if round_up then {
                    int_result = int_result + 1
                };
                real_result = Real(int_result);
                if real_result == 0.0 then {
                    result = FPZero(sign)
                } else {
                    result = FPRound(real_result, fpcr, FPRounding_ZERO)
                };
                if error != 0.0 & exact then {
                    FPProcessException(FPExc_Inexact, fpcr)
                }
            }
        }
    };
    result
}

val FPCompare : forall 'N ('signal_nans : Bool),
  ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bool('signal_nans), bits(32)) -> bits(4) effect {escape, rreg, undef, wreg}

function FPCompare (op1, op2, signal_nans, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    result : bits(4) = undefined : bits(4);
    if ((type1 == FPType_SNaN | type1 == FPType_QNaN) | type2 == FPType_SNaN) | type2 == FPType_QNaN then {
        result = 0x3;
        if (type1 == FPType_SNaN | type2 == FPType_SNaN) | signal_nans then {
            FPProcessException(FPExc_InvalidOp, fpcr)
        }
    } else {
        if value1_name == value2_name then {
            result = 0x6
        } else {
            if value1_name < value2_name then {
                result = 0x8
            } else {
                result = 0x2
            }
        }
    };
    result
}

val FPSub : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPSub (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let rounding = FPRoundingMode(fpcr);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
    inf1 : bool = undefined : bool;
    inf2 : bool = undefined : bool;
    result_sign : bits(1) = undefined : bits(1);
    result_value : real = undefined : real;
    zero1 : bool = undefined : bool;
    zero2 : bool = undefined : bool;
    if ~(done) then {
        inf1 = type1 == FPType_Infinity;
        inf2 = type2 == FPType_Infinity;
        zero1 = type1 == FPType_Zero;
        zero2 = type2 == FPType_Zero;
        if (inf1 & inf2) & sign1 == sign2 then {
            result = FPDefaultNaN();
            FPProcessException(FPExc_InvalidOp, fpcr)
        } else {
            if inf1 & sign1 == 0b0 | inf2 & sign2 == 0b1 then {
                result = FPInfinity(0b0)
            } else {
                if inf1 & sign1 == 0b1 | inf2 & sign2 == 0b0 then {
                    result = FPInfinity(0b1)
                } else {
                    if (zero1 & zero2) & sign1 == ~(sign2) then {
                        result = FPZero(sign1)
                    } else {
                        result_value = value1_name - value2_name;
                        if result_value == 0.0 then {
                            result_sign = if rounding == FPRounding_NEGINF then 0b1 else 0b0;
                            result = FPZero(result_sign)
                        } else {
                            result = FPRound(result_value, fpcr, rounding)
                        }
                    }
                }
            }
        }
    };
    result
}

val FPMulAdd : forall ('N : Int), ('N >= 0 & 'N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMulAdd (addend, op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let rounding = FPRoundingMode(fpcr);
    signA : bits(1) = undefined : bits(1);
    typeA : FPType = undefined : FPType;
    valueA_name : real = undefined : real;
    (typeA, signA, valueA_name) = FPUnpack(addend, fpcr);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    let inf1 : bool = type1 == FPType_Infinity;
    let zero1 : bool = type1 == FPType_Zero;
    let inf2 : bool = type2 == FPType_Infinity;
    let zero2 : bool = type2 == FPType_Zero;
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    (done, result) = FPProcessNaNs3(typeA, type1, type2, addend, op1, op2, fpcr);
    if typeA == FPType_QNaN & (inf1 & zero2 | zero1 & inf2) then {
        result = FPDefaultNaN();
        FPProcessException(FPExc_InvalidOp, fpcr)
    };
    infA : bool = undefined : bool;
    infP : bool = undefined : bool;
    result_sign : bits(1) = undefined : bits(1);
    result_value : real = undefined : real;
    signP : bits(1) = undefined : bits(1);
    zeroA : bool = undefined : bool;
    zeroP : bool = undefined : bool;
    if ~(done) then {
        infA = typeA == FPType_Infinity;
        zeroA = typeA == FPType_Zero;
        signP = sign1 ^ sign2;
        infP = inf1 | inf2;
        zeroP = zero1 | zero2;
        if (inf1 & zero2 | zero1 & inf2) | (infA & infP) & signA != signP then {
            result = FPDefaultNaN();
            FPProcessException(FPExc_InvalidOp, fpcr)
        } else {
            if infA & signA == 0b0 | infP & signP == 0b0 then {
                result = FPInfinity(0b0)
            } else {
                if infA & signA == 0b1 | infP & signP == 0b1 then {
                    result = FPInfinity(0b1)
                } else {
                    if (zeroA & zeroP) & signA == signP then {
                        result = FPZero(signA)
                    } else {
                        result_value = valueA_name + value1_name * value2_name;
                        if result_value == 0.0 then {
                            result_sign = if rounding == FPRounding_NEGINF then 0b1 else 0b0;
                            result = FPZero(result_sign)
                        } else {
                            result = FPRound(result_value, fpcr)
                        }
                    }
                }
            }
        }
    };
    result
}

val FPMul : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMul (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
    inf1 : bool = undefined : bool;
    inf2 : bool = undefined : bool;
    zero1 : bool = undefined : bool;
    zero2 : bool = undefined : bool;
    if ~(done) then {
        inf1 = type1 == FPType_Infinity;
        inf2 = type2 == FPType_Infinity;
        zero1 = type1 == FPType_Zero;
        zero2 = type2 == FPType_Zero;
        if inf1 & zero2 | zero1 & inf2 then {
            result = FPDefaultNaN();
            FPProcessException(FPExc_InvalidOp, fpcr)
        } else {
            if inf1 | inf2 then {
                result = FPInfinity(sign1 ^ sign2)
            } else {
                if zero1 | zero2 then {
                    result = FPZero(sign1 ^ sign2)
                } else {
                    result = FPRound(value1_name * value2_name, fpcr)
                }
            }
        }
    };
    result
}

val FPMin : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMin (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    if ~(done) then {
        if value1_name < value2_name then {
            (typ, sign, value_name) = (type1, sign1, value1_name)
        } else {
            (typ, sign, value_name) = (type2, sign2, value2_name)
        };
        if typ == FPType_Infinity then {
            result = FPInfinity(sign)
        } else {
            if typ == FPType_Zero then {
                sign = sign1 | sign2;
                result = FPZero(sign)
            } else {
                result = FPRound(value_name, fpcr)
            }
        }
    };
    result
}

val FPMinNum : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMinNum (op1__arg, op2__arg, fpcr) = {
    op1 = op1__arg;
    op2 = op2__arg;
    assert('N == 16 | 'N == 32 | 'N == 64);
    __anon1 : bits(1) = undefined : bits(1);
    __anon2 : real = undefined : real;
    type1 : FPType = undefined : FPType;
    (type1, __anon1, __anon2) = FPUnpack(op1, fpcr);
    __anon3 : bits(1) = undefined : bits(1);
    __anon4 : real = undefined : real;
    type2 : FPType = undefined : FPType;
    (type2, __anon3, __anon4) = FPUnpack(op2, fpcr);
    if type1 == FPType_QNaN & type2 != FPType_QNaN then {
        op1 = FPInfinity(0b0)
    } else {
        if type1 != FPType_QNaN & type2 == FPType_QNaN then {
            op2 = FPInfinity(0b0)
        }
    };
    FPMin(op1, op2, fpcr)
}

val FPMax : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMax (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    if ~(done) then {
        if value1_name > value2_name then {
            (typ, sign, value_name) = (type1, sign1, value1_name)
        } else {
            (typ, sign, value_name) = (type2, sign2, value2_name)
        };
        if typ == FPType_Infinity then {
            result = FPInfinity(sign)
        } else {
            if typ == FPType_Zero then {
                sign = sign1 & sign2;
                result = FPZero(sign)
            } else {
                result = FPRound(value_name, fpcr)
            }
        }
    };
    result
}

val FPMaxNum : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMaxNum (op1__arg, op2__arg, fpcr) = {
    op1 = op1__arg;
    op2 = op2__arg;
    assert('N == 16 | 'N == 32 | 'N == 64);
    __anon1 : bits(1) = undefined : bits(1);
    __anon2 : real = undefined : real;
    type1 : FPType = undefined : FPType;
    (type1, __anon1, __anon2) = FPUnpack(op1, fpcr);
    __anon3 : bits(1) = undefined : bits(1);
    __anon4 : real = undefined : real;
    type2 : FPType = undefined : FPType;
    (type2, __anon3, __anon4) = FPUnpack(op2, fpcr);
    if type1 == FPType_QNaN & type2 != FPType_QNaN then {
        op1 = FPInfinity(0b1)
    } else {
        if type1 != FPType_QNaN & type2 == FPType_QNaN then {
            op2 = FPInfinity(0b1)
        }
    };
    FPMax(op1, op2, fpcr)
}

val FPDiv : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPDiv (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
    inf1 : bool = undefined : bool;
    inf2 : bool = undefined : bool;
    zero1 : bool = undefined : bool;
    zero2 : bool = undefined : bool;
    if ~(done) then {
        inf1 = type1 == FPType_Infinity;
        inf2 = type2 == FPType_Infinity;
        zero1 = type1 == FPType_Zero;
        zero2 = type2 == FPType_Zero;
        if inf1 & inf2 | zero1 & zero2 then {
            result = FPDefaultNaN();
            FPProcessException(FPExc_InvalidOp, fpcr)
        } else {
            if inf1 | zero2 then {
                result = FPInfinity(sign1 ^ sign2);
                if ~(inf1) then {
                    FPProcessException(FPExc_DivideByZero, fpcr)
                }
            } else {
                if zero1 | inf2 then {
                    result = FPZero(sign1 ^ sign2)
                } else {
                    result = FPRound(value1_name / value2_name, fpcr)
                }
            }
        }
    };
    result
}

val FPAdd : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPAdd (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let rounding = FPRoundingMode(fpcr);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    done : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
    inf1 : bool = undefined : bool;
    inf2 : bool = undefined : bool;
    result_sign : bits(1) = undefined : bits(1);
    result_value : real = undefined : real;
    zero1 : bool = undefined : bool;
    zero2 : bool = undefined : bool;
    if ~(done) then {
        inf1 = type1 == FPType_Infinity;
        inf2 = type2 == FPType_Infinity;
        zero1 = type1 == FPType_Zero;
        zero2 = type2 == FPType_Zero;
        if (inf1 & inf2) & sign1 == ~(sign2) then {
            result = FPDefaultNaN();
            FPProcessException(FPExc_InvalidOp, fpcr)
        } else {
            if inf1 & sign1 == 0b0 | inf2 & sign2 == 0b0 then {
                result = FPInfinity(0b0)
            } else {
                if inf1 & sign1 == 0b1 | inf2 & sign2 == 0b1 then {
                    result = FPInfinity(0b1)
                } else {
                    if (zero1 & zero2) & sign1 == sign2 then {
                        result = FPZero(sign1)
                    } else {
                        result_value = value1_name + value2_name;
                        if result_value == 0.0 then {
                            result_sign = if rounding == FPRounding_NEGINF then 0b1 else 0b0;
                            result = FPZero(result_sign)
                        } else {
                            result = FPRound(result_value, fpcr, rounding)
                        }
                    }
                }
            }
        }
    };
    result
}

val float_move_fp_select : forall 'd 'datasize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31).
  (bits(4), int('d), int('datasize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function float_move_fp_select (condition, d, datasize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let result : bits('datasize) = if ConditionHolds(condition) then V(n) else V(m);
    V(d) = result
}

val float_move_fp_select_decode : (bits(5), bits(5), bits(4), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_move_fp_select_decode (Rd, Rn, cond, Rm, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    let condition = cond;
    __PostDecode();
    float_move_fp_select(condition, d, datasize, m, n)
}

val float_move_fp_imm : forall 'd 'datasize,
  'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), bits('datasize)) -> unit effect {escape, rreg, undef, wreg}

function float_move_fp_imm (d, datasize, imm) = {
    CheckFPAdvSIMDEnabled64();
    V(d) = imm
}

val float_move_fp_imm_decode : (bits(5), bits(5), bits(8), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_move_fp_imm_decode (Rd, imm5, imm8, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    let imm : bits('datasize) = VFPExpandImm(imm8);
    __PostDecode();
    float_move_fp_imm(d, datasize, imm)
}

val float_convert_int : forall 'd 'fltsize 'intsize 'n 'part ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & 'fltsize >= 0 & ('d >= 0 & 'd <= 31) & 'intsize in {8, 16, 32, 64} & 'part in {0, 1}.
  (int('d), int('fltsize), int('intsize), int('n), FPConvOp, int('part), FPRounding, bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function float_convert_int (d, fltsize, intsize, n, op, part, rounding, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    fltval : bits('fltsize) = undefined : bits('fltsize);
    intval : bits('intsize) = undefined : bits('intsize);
    match op {
      FPConvOp_CVT_FtoI => {
          fltval = V(n);
          intval = FPToFixed(fltval, 0, unsigned, FPCR, rounding);
          X(d) = intval
      },
      FPConvOp_CVT_ItoF => {
          intval = X(n);
          fltval = FixedToFP(intval, 0, unsigned, FPCR, rounding);
          V(d) = fltval
      },
      FPConvOp_MOV_FtoI => {
          fltval = Vpart(n, part);
          intval = ZeroExtend(fltval, intsize);
          X(d) = intval
      },
      FPConvOp_MOV_ItoF => {
          intval = X(n);
          fltval = slice(intval, 0, fltsize);
          Vpart(d, part) = fltval
      },
      FPConvOp_CVT_FtoI_JS => {
          fltval = V(n);
          intval = FPToFixedJS(fltval, FPCR, true);
          X(d) = ZeroExtend(slice(intval, 0, 32), 64)
      }
    };
    let intval = intval;
    let fltval = fltval;
    ()
}

val float_convert_int_decode : (bits(5), bits(5), bits(3), bits(2), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_convert_int_decode (Rd, Rn, opcode, rmode, typ, S, sf) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'intsize : {|64, 32|} = if sf == 0b1 then 64 else 32;
    fltsize : int = undefined : int;
    op : FPConvOp = undefined : FPConvOp;
    rounding : FPRounding = undefined : FPRounding;
    unsigned : bool = undefined : bool;
    part : int = undefined : int;
    match typ {
      0b00 => {
          fltsize = 32
      },
      0b01 => {
          fltsize = 64
      },
      0b10 => {
          if (slice(opcode, 1, 2) @ rmode) != 0xD then {
              throw(Error_Undefined())
          };
          fltsize = 128
      },
      0b11 => {
          if HaveFP16Ext() then {
              fltsize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    match slice(opcode, 1, 2) @ rmode {
      [bitzero] @ [bitzero] @ _ : bits(1) @ _ : bits(1) => {
          rounding = FPDecodeRounding(rmode);
          unsigned = [opcode[0]] == 0b1;
          op = FPConvOp_CVT_FtoI
      },
      0x4 => {
          rounding = FPRoundingMode(FPCR);
          unsigned = [opcode[0]] == 0b1;
          op = FPConvOp_CVT_ItoF
      },
      0x8 => {
          rounding = FPRounding_TIEAWAY;
          unsigned = [opcode[0]] == 0b1;
          op = FPConvOp_CVT_FtoI
      },
      0xC => {
          if fltsize != 16 & fltsize != intsize then {
              throw(Error_Undefined())
          };
          op = if [opcode[0]] == 0b1 then FPConvOp_MOV_ItoF else FPConvOp_MOV_FtoI;
          part = 0
      },
      0xD => {
          if intsize != 64 | fltsize != 128 then {
              throw(Error_Undefined())
          };
          op = if [opcode[0]] == 0b1 then FPConvOp_MOV_ItoF else FPConvOp_MOV_FtoI;
          part = 1;
          fltsize = 64
      },
      0xF => {
          if ~(HaveFJCVTZSExt()) then {
              throw(Error_Undefined())
          };
          rounding = FPRounding_ZERO;
          unsigned = [opcode[0]] == 0b1;
          op = FPConvOp_CVT_FtoI_JS
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    __PostDecode();
    let 'fltsize = fltsize;
    let 'part = part;
    assert(constraint(('part in {0, 1} & 'fltsize >= 0)));
    float_convert_int(d, fltsize, intsize, n, op, part, rounding, unsigned)
}

val float_convert_fp : forall 'd 'dstsize 'n 'srcsize,
  ('n >= 0 & 'n <= 31 & 'srcsize >= 0 & 'd >= 0 & 'd <= 31).
  (int('d), int('dstsize), int('n), int('srcsize)) -> unit effect {escape, rreg, undef, wreg}

function float_convert_fp (d, dstsize, n, srcsize) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('srcsize) = aget_V(n);
    let result : bits('dstsize) = FPConvert(operand, FPCR);
    aset_V(d, result)
}

val float_convert_fp_decode : (bits(5), bits(5), bits(2), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_convert_fp_decode (Rd, Rn, opc, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if typ == opc then {
        throw(Error_Undefined())
    };
    srcsize : int = undefined : int;
    match typ {
      0b00 => {
          srcsize = 32
      },
      0b01 => {
          srcsize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          srcsize = 16
      }
    };
    dstsize : int = undefined : int;
    match opc {
      0b00 => {
          dstsize = 32
      },
      0b01 => {
          dstsize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          dstsize = 16
      }
    };
    __PostDecode();
    let 'srcsize = srcsize;
    let 'dstsize = dstsize;
    assert(constraint(('srcsize in {16, 32, 64} & 'dstsize in {16, 32, 64})));
    float_convert_fp(d, dstsize, n, srcsize)
}

val float_convert_fix : forall 'd 'fltsize 'fracbits 'intsize 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('fltsize >= 0 & 'fracbits >= 0) & ('d >= 0 & 'd <= 31) & 'intsize in {8, 16, 32, 64}.
  (int('d), int('fltsize), int('fracbits), int('intsize), int('n), FPConvOp, FPRounding, bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function float_convert_fix (d, fltsize, fracbits, intsize, n, op, rounding, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    fltval : bits('fltsize) = undefined : bits('fltsize);
    intval : bits('intsize) = undefined : bits('intsize);
    match op {
      FPConvOp_CVT_FtoI => {
          fltval = V(n);
          intval = FPToFixed(fltval, fracbits, unsigned, FPCR, rounding);
          X(d) = intval
      },
      FPConvOp_CVT_ItoF => {
          intval = X(n);
          fltval = FixedToFP(intval, fracbits, unsigned, FPCR, rounding);
          V(d) = fltval
      }
    };
    let intval = intval;
    let fltval = fltval;
    ()
}

val float_convert_fix_decode : (bits(5), bits(5), bits(6), bits(3), bits(2), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_convert_fix_decode (Rd, Rn, scale, opcode, rmode, typ, S, sf) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'intsize : {|64, 32|} = if sf == 0b1 then 64 else 32;
    fltsize : int = undefined : int;
    op : FPConvOp = undefined : FPConvOp;
    rounding : FPRounding = undefined : FPRounding;
    unsigned : bool = undefined : bool;
    match typ {
      0b00 => {
          fltsize = 32
      },
      0b01 => {
          fltsize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              fltsize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    if sf == 0b0 & [scale[5]] == 0b0 then {
        throw(Error_Undefined())
    };
    let 'fracbits = 64 - UInt(scale);
    match slice(opcode, 1, 2) @ rmode {
      0x3 => {
          rounding = FPRounding_ZERO;
          unsigned = [opcode[0]] == 0b1;
          op = FPConvOp_CVT_FtoI
      },
      0x4 => {
          rounding = FPRoundingMode(FPCR);
          unsigned = [opcode[0]] == 0b1;
          op = FPConvOp_CVT_ItoF
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    __PostDecode();
    let 'fltsize = fltsize;
    assert(constraint('fltsize in {16, 32, 64}));
    float_convert_fix(d, fltsize, fracbits, intsize, n, op, rounding, unsigned)
}

val float_compare_uncond : forall ('cmp_with_zero : Bool) 'datasize 'm 'n ('signal_all_nans : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31 | not(not('cmp_with_zero))) & ('datasize >= 0 & 'datasize >= 0).
  (bool('cmp_with_zero), int('datasize), int('m), int('n), bool('signal_all_nans)) -> unit effect {escape, rreg, undef, wreg}

function float_compare_uncond (cmp_with_zero, datasize, m, n, signal_all_nans) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = if cmp_with_zero then FPZero(0b0) else V(m);
    (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = FPCompare(operand1, operand2, signal_all_nans, FPCR)
}

val float_compare_uncond_decode : (bits(2), bits(5), bits(2), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_compare_uncond_decode (opc, Rn, op, Rm, typ, S, M) = {
    __unconditional = true;
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    let signal_all_nans : bool = [opc[1]] == 0b1;
    let cmp_with_zero : bool = [opc[0]] == 0b1;
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_compare_uncond(cmp_with_zero, datasize, m, n, signal_all_nans)
}

val float_compare_cond : forall 'datasize 'm 'n ('signal_all_nans : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'datasize >= 0).
  (bits(4), int('datasize), bits(4), int('m), int('n), bool('signal_all_nans)) -> unit effect {escape, rreg, undef, wreg}

function float_compare_cond (condition, datasize, flags__arg, m, n, signal_all_nans) = {
    flags = flags__arg;
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    if ConditionHolds(condition) then {
        flags = FPCompare(operand1, operand2, signal_all_nans, FPCR)
    };
    (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = flags
}

val float_compare_cond_decode : (bits(4), bits(1), bits(5), bits(4), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_compare_cond_decode (nzcv, op, Rn, cond, Rm, typ, S, M) = {
    __unconditional = true;
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    let signal_all_nans : bool = op == 0b1;
    let condition : bits(4) = cond;
    let flags : bits(4) = nzcv;
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_compare_cond(condition, datasize, flags, m, n, signal_all_nans)
}

val float_arithmetic_unary : forall 'd 'datasize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), FPUnaryOp, int('n)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_unary (d, datasize, fpop, n) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    let operand : bits('datasize) = V(n);
    match fpop {
      FPUnaryOp_MOV => {
          result = operand
      },
      FPUnaryOp_ABS => {
          result = FPAbs(operand)
      },
      FPUnaryOp_NEG => {
          result = FPNeg(operand)
      },
      FPUnaryOp_SQRT => {
          result = FPSqrt(operand, FPCR)
      }
    };
    let result = result;
    V(d) = result
}

val float_arithmetic_unary_decode : (bits(5), bits(5), bits(2), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_unary_decode (Rd, Rn, opc, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    fpop : FPUnaryOp = undefined : FPUnaryOp;
    match opc {
      0b00 => {
          fpop = FPUnaryOp_MOV
      },
      0b01 => {
          fpop = FPUnaryOp_ABS
      },
      0b10 => {
          fpop = FPUnaryOp_NEG
      },
      0b11 => {
          fpop = FPUnaryOp_SQRT
      }
    };
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_unary(d, datasize, fpop, n)
}

val float_arithmetic_round_frint_32_64 : forall 'd 'datasize 'intsize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'intsize in {32, 64}) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('intsize), int('n), FPRounding) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_round_frint_32_64 (d, datasize, intsize, n, rounding) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    let operand : bits('datasize) = V(n);
    let result = FPRoundIntN(operand, FPCR, rounding, intsize);
    V(d) = result
}

val float_arithmetic_round_frint_32_64_decode : (bits(5), bits(5), bits(2), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_round_frint_32_64_decode (Rd, Rn, op, typ) = {
    __unconditional = true;
    if ~(HaveFrintExt()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      [bitone] @ _ : bits(1) => {
          throw(Error_Undefined())
      }
    };
    let 'intsize : {|32, 64|} = if [op[1]] == 0b0 then 32 else 64;
    let rounding : FPRounding = if [op[0]] == 0b0 then FPRounding_ZERO else FPRoundingMode(FPCR);
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_round_frint_32_64(d, datasize, intsize, n, rounding)
}

val float_arithmetic_round_frint : forall 'd 'datasize ('exact : Bool) 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), bool('exact), int('n), FPRounding) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_round_frint (d, datasize, exact, n, rounding) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    let operand : bits('datasize) = V(n);
    let result = FPRoundInt(operand, FPCR, rounding, exact);
    V(d) = result
}

val float_arithmetic_round_frint_decode : (bits(5), bits(5), bits(3), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_round_frint_decode (Rd, Rn, rmode, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    exact : bool = false;
    rounding : FPRounding = undefined : FPRounding;
    match rmode {
      [bitzero] @ _ : bits(1) @ _ : bits(1) => {
          rounding = FPDecodeRounding(slice(rmode, 0, 2))
      },
      0b100 => {
          rounding = FPRounding_TIEAWAY
      },
      0b101 => {
          throw(Error_Undefined())
      },
      0b110 => {
          rounding = FPRoundingMode(FPCR);
          exact = true
      },
      0b111 => {
          rounding = FPRoundingMode(FPCR)
      }
    };
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_round_frint(d, datasize, exact, n, rounding)
}

val float_arithmetic_mul_product : forall 'd 'datasize 'm 'n ('negated : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'datasize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('m), int('n), bool('negated)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_mul_product (d, datasize, m, n, negated) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result = FPMul(operand1, operand2, FPCR);
    if negated then {
        result = FPNeg(result)
    };
    V(d) = result
}

val float_arithmetic_mul_product_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_mul_product_decode (Rd, Rn, op, Rm, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    let negated : bool = op == 0b1;
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_mul_product(d, datasize, m, n, negated)
}

val float_arithmetic_mul_addsub : forall 'a 'd 'datasize 'm 'n ('op1_neg : Bool) ('opa_neg : Bool),
  ('a >= 0 & 'a <= 31) & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 | not('opa_neg)) & ('datasize >= 0 | not('op1_neg)) & ('datasize >= 0 & 'datasize >= 0 & 'datasize >= 0) & ('d >= 0 & 'd <= 31).
  (int('a), int('d), int('datasize), int('m), int('n), bool('op1_neg), bool('opa_neg)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_mul_addsub (a, d, datasize, m, n, op1_neg, opa_neg) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    operanda : bits('datasize) = V(a);
    operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    if opa_neg then {
        operanda = FPNeg(operanda)
    };
    if op1_neg then {
        operand1 = FPNeg(operand1)
    };
    let result = FPMulAdd(operanda, operand1, operand2, FPCR);
    V(d) = result
}

val float_arithmetic_mul_addsub_decode : (bits(5), bits(5), bits(5), bits(1), bits(5), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_mul_addsub_decode (Rd, Rn, Ra, o0, Rm, o1, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'a = UInt(Ra);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    let opa_neg : bool = o1 == 0b1;
    let op1_neg : bool = o0 != o1;
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_mul_addsub(a, d, datasize, m, n, op1_neg, opa_neg)
}

val float_arithmetic_maxmin : forall 'd 'datasize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'datasize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('m), int('n), FPMaxMinOp) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_maxmin (d, datasize, m, n, operation) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    match operation {
      FPMaxMinOp_MAX => {
          result = FPMax(operand1, operand2, FPCR)
      },
      FPMaxMinOp_MIN => {
          result = FPMin(operand1, operand2, FPCR)
      },
      FPMaxMinOp_MAXNUM => {
          result = FPMaxNum(operand1, operand2, FPCR)
      },
      FPMaxMinOp_MINNUM => {
          result = FPMinNum(operand1, operand2, FPCR)
      }
    };
    let result = result;
    V(d) = result
}

val float_arithmetic_maxmin_decode : (bits(5), bits(5), bits(2), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_maxmin_decode (Rd, Rn, op, Rm, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    operation : FPMaxMinOp = undefined : FPMaxMinOp;
    match op {
      0b00 => {
          operation = FPMaxMinOp_MAX
      },
      0b01 => {
          operation = FPMaxMinOp_MIN
      },
      0b10 => {
          operation = FPMaxMinOp_MAXNUM
      },
      0b11 => {
          operation = FPMaxMinOp_MINNUM
      }
    };
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_maxmin(d, datasize, m, n, operation)
}

val float_arithmetic_div : forall 'd 'datasize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'datasize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_div (d, datasize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    let result = FPDiv(operand1, operand2, FPCR);
    V(d) = result
}

val float_arithmetic_div_decode : (bits(5), bits(5), bits(4), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_div_decode (Rd, Rn, opcode, Rm, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_div(d, datasize, m, n)
}

val float_arithmetic_addsub : forall 'd 'datasize 'm 'n ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'datasize >= 0 | not('sub_op)) & ('datasize >= 0 & 'datasize >= 0 | not(not('sub_op))) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('m), int('n), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_addsub (d, datasize, m, n, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    result : bits('datasize) = undefined : bits('datasize);
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    if sub_op then {
        result = FPSub(operand1, operand2, FPCR)
    } else {
        result = FPAdd(operand1, operand2, FPCR)
    };
    V(d) = result
}

val float_arithmetic_addsub_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_addsub_decode (Rd, Rn, op, Rm, typ, S, M) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    datasize : int = undefined : int;
    match typ {
      0b00 => {
          datasize = 32
      },
      0b01 => {
          datasize = 64
      },
      0b10 => {
          throw(Error_Undefined())
      },
      0b11 => {
          if HaveFP16Ext() then {
              datasize = 16
          } else {
              throw(Error_Undefined())
          }
      }
    };
    let sub_op : bool = op == 0b1;
    __PostDecode();
    let 'datasize = datasize;
    assert(constraint('datasize in {16, 32, 64}));
    float_arithmetic_addsub(d, datasize, m, n, sub_op)
}
