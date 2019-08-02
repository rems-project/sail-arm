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

val __UNKNOWN_VBitOp : unit -> VBitOp

function __UNKNOWN_VBitOp () = {
    VBitOp_VBIF
}

val __UNKNOWN_ImmediateOp : unit -> ImmediateOp

function __UNKNOWN_ImmediateOp () = {
    ImmediateOp_MOVI
}

val SHAparity : (bits(32), bits(32), bits(32)) -> bits(32)

function SHAparity (x, y, z) = {
    (x ^ y) ^ z
}

val __UNKNOWN_CompareOp : unit -> CompareOp

function __UNKNOWN_CompareOp () = {
    CompareOp_GT
}

val SHAmajority : (bits(32), bits(32), bits(32)) -> bits(32)

function SHAmajority (x, y, z) = {
    x & y | (x | y) & z
}

val SHAchoose : (bits(32), bits(32), bits(32)) -> bits(32)

function SHAchoose (x, y, z) = {
    (y ^ z & x) ^ z
}

val AESSubBytes : bits(128) -> bits(128) effect {escape}

function AESSubBytes op = {
    throw(Error_Implementation_Defined("AESSubBytes unimplemented"))
}

val AESShiftRows : bits(128) -> bits(128) effect {escape}

function AESShiftRows op = {
    throw(Error_Implementation_Defined("AESShiftRows unimplemented"))
}

val AESMixColumns : bits(128) -> bits(128) effect {escape}

function AESMixColumns op = {
    throw(Error_Implementation_Defined("AESMixColumns unimplemented"))
}

val AESInvSubBytes : bits(128) -> bits(128) effect {escape}

function AESInvSubBytes op = {
    throw(Error_Implementation_Defined("AESInvSubBytes unimplemented"))
}

val AESInvShiftRows : bits(128) -> bits(128) effect {escape}

function AESInvShiftRows op = {
    throw(Error_Implementation_Defined("AESInvShiftRows unimplemented"))
}

val AESInvMixColumns : bits(128) -> bits(128) effect {escape}

function AESInvMixColumns op = {
    throw(Error_Implementation_Defined("AESInvMixColumns unimplemented"))
}

val HaveSHA256Ext : unit -> bool effect {escape}

function HaveSHA256Ext () = {
    __IMPDEF_boolean("Has SHA256 Crypto instructions")
}

val HaveSHA1Ext : unit -> bool effect {escape}

function HaveSHA1Ext () = {
    __IMPDEF_boolean("Has SHA1 Crypto instructions")
}

val HaveBit128PMULLExt : unit -> bool effect {escape}

function HaveBit128PMULLExt () = {
    __IMPDEF_boolean("Has 128-bit form of PMULL instructions")
}

val HaveAESExt : unit -> bool effect {escape}

function HaveAESExt () = {
    __IMPDEF_boolean("Has AES Crypto instructions")
}

val HaveQRDMLAHExt : unit -> bool

function HaveQRDMLAHExt () = {
    HasArchVersion(ARMv8p1)
}

val HaveFCADDExt : unit -> bool

function HaveFCADDExt () = {
    HasArchVersion(ARMv8p3)
}

val HaveDOTPExt : unit -> bool effect {escape}

function HaveDOTPExt () = {
    HasArchVersion(ARMv8p4) | HasArchVersion(ARMv8p2) & __IMPDEF_boolean("Has Dot Product extension")
}

val LowestSetBit : forall ('N : Int), 'N >= 0. bits('N) -> int

function LowestSetBit x = {
    foreach (i from 0 to ('N - 1) by 1 in inc) {
        if [x[i]] == 0b1 then {
            return(i)
        }
    };
    'N
}

val BitCount : forall ('N : Int), 'N >= 0. bits('N) -> int

function BitCount x = {
    result : int = 0;
    foreach (i from 0 to ('N - 1) by 1 in inc) {
        if [x[i]] == 0b1 then {
            result = result + 1
        }
    };
    result
}

val Sbox : bits(8) -> bits(8) effect {undef}

function Sbox sboxin = {
    sboxout : bits(8) = undefined : bits(8);
    let sboxstring : bits(2048) = __GetSlice_int(2048, 27086457041271130658097913556973622859223908082898777931279708123265802528354842616141526661043990239966061245146490489245523501543590288385437002023358814947081845591010354165772708439349485551596405955355395097736697731641465653447759785887130139642898454897614116485023073928669016836841447803958846420478804845848435434304342658474410584354851222871590567875520195692946750020179880039080961350182547539832666651577275749378753269779670476274426614755119909370245322827169127262049788036928038538634406508934382584917480550081919950181243327359810644173326097655591141455893541487338091667629050780151417584433480, 0);
    let sboxin = UInt(sboxin);
    let sboxout = slice(sboxstring, (255 - sboxin) * 8, 8 + 8 * sboxin - 8 * sboxin);
    sboxout
}

val PolynomialMult : forall ('M : Int) ('N : Int), ('M >= 0 & 'N >= 0).
  (bits('M), bits('N)) -> bits('N + 'M) effect {escape, undef}

function PolynomialMult (op1, op2) = {
    result : bits('N + 'M) = undefined : bits('N + 'M);
    result = Zeros('M + 'N);
    let extended_op2 = ZeroExtend(op2, 'M + 'N);
    foreach (i from 0 to ('M - 1) by 1 in inc) {
        if [op1[i]] == 0b1 then {
            result = result ^ LSL(extended_op2, i)
        }
    };
    result
}

val FPOnePointFive : forall ('N : Int).
  (implicit('N), bits(1)) -> bits('N) effect {escape}

function FPOnePointFive (N, sign) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'E : {'n, 'n in {5, 8, 11}. int('n)} = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
    let 'F : {'n, 'n == 'N - ('E + 1). int('n)} = 'N - (E + 1);
    let exp : bits('E) = 0b0 @ Ones(E - 1);
    let frac : bits('N - 1 - 'E) = 0b1 @ Zeros(F - 1);
    (sign @ exp) @ frac
}

val RecipSqrtEstimate : forall ('a : Int). int('a) -> int effect {escape}

function RecipSqrtEstimate a__arg = {
    a : int = a__arg;
    assert(128 <= a & a < 512);
    if a < 256 then {
        a = a * 2 + 1
    } else {
        a = shl_int(shr_int(a, 1), 1);
        a = (a + 1) * 2
    };
    b : int = 512;
    while a * (b + 1) * (b + 1) < 2 ^ 28 do {
        b = b + 1
    };
    let r : int = (b + 1) / 2;
    assert(256 <= r & r < 512);
    r
}

val UnsignedRSqrtEstimate : forall ('N : Int), 'N >= 0.
  bits('N) -> bits('N) effect {escape, undef}

function UnsignedRSqrtEstimate operand = {
    assert('N == 16 | 'N == 32);
    estimate : int = undefined : int;
    result : bits('N) = undefined : bits('N);
    if slice(operand, 'N - 2, 2) == 0b00 then {
        result = Ones('N)
    } else {
        match 'N {
          16 => {
              estimate = RecipSqrtEstimate(UInt(slice(operand, 7, 9)))
          },
          32 => {
              estimate = RecipSqrtEstimate(UInt(slice(operand, 23, 9)))
          }
        };
        result = __GetSlice_int(9, estimate, 0) @ Zeros('N - 9)
    };
    result
}

val RecipEstimate : forall ('a : Int). int('a) -> int effect {escape}

function RecipEstimate a = {
    assert(256 <= a & a < 512);
    let a = a * 2 + 1;
    let 'b = 2 ^ 19 / a;
    let r : int = (b + 1) / 2;
    assert(256 <= r & r < 512);
    r
}

val UnsignedRecipEstimate : forall ('N : Int), 'N >= 0.
  bits('N) -> bits('N) effect {escape, undef}

function UnsignedRecipEstimate operand = {
    assert('N == 16 | 'N == 32);
    estimate : int = undefined : int;
    result : bits('N) = undefined : bits('N);
    if [operand['N - 1]] == 0b0 then {
        result = Ones('N)
    } else {
        match 'N {
          16 => {
              estimate = RecipEstimate(UInt(slice(operand, 7, 9)))
          },
          32 => {
              estimate = RecipEstimate(UInt(slice(operand, 23, 9)))
          }
        };
        result = __GetSlice_int(9, estimate, 0) @ Zeros('N - 9)
    };
    result
}

val SHAhashSIGMA1 : bits(32) -> bits(32) effect {escape, undef}

function SHAhashSIGMA1 x = {
    (ROR(x, 6) ^ ROR(x, 11)) ^ ROR(x, 25)
}

val SHAhashSIGMA0 : bits(32) -> bits(32) effect {escape, undef}

function SHAhashSIGMA0 x = {
    (ROR(x, 2) ^ ROR(x, 13)) ^ ROR(x, 22)
}

val ROL : forall ('N : Int) ('shift : Int), 'N >= 0.
  (bits('N), int('shift)) -> bits('N) effect {escape, undef}

function ROL (x, shift) = {
    assert(shift >= 0 & shift <= 'N);
    if shift == 0 then {
        return(x)
    };
    ROR(x, 'N - shift)
}

val SHA256hash : forall ('part1 : Bool).
  (bits(128), bits(128), bits(128), bool('part1)) -> bits(128) effect {escape, undef}

function SHA256hash (X__arg, Y__arg, W, part1) = {
    X = X__arg;
    Y = Y__arg;
    chs : bits(32) = undefined : bits(32);
    maj : bits(32) = undefined : bits(32);
    t : bits(32) = undefined : bits(32);
    foreach (e from 0 to 3 by 1 in inc) {
        chs = SHAchoose(slice(Y, 0, 32), slice(Y, 32, 32), slice(Y, 64, 32));
        maj = SHAmajority(slice(X, 0, 32), slice(X, 32, 32), slice(X, 64, 32));
        t = slice(Y, 96, 32) + SHAhashSIGMA1(slice(Y, 0, 32)) + chs + aget_Elem(W, e, 32);
        X = __SetSlice_bits(128, 32, X, 96, t + slice(X, 96, 32));
        Y = __SetSlice_bits(128, 32, Y, 96, t + SHAhashSIGMA0(slice(X, 0, 32)) + maj);
        let __tc1 = ROL(Y @ X, 32);
        Y = slice(__tc1, 128, 128);
        X = slice(__tc1, 0, 128)
    };
    if part1 then X else Y
}

val FPProcessNaNs3H : forall ('N : Int), 'N >= 0.
  (FPType, FPType, FPType, bits('N), bits(div('N, 2)), bits(div('N, 2)), bits(32)) -> (bool, bits('N)) effect {escape, rreg, undef, wreg}

function FPProcessNaNs3H (type1, type2, type3, op1, op2, op3, fpcr) = {
    assert('N == 32 | 'N == 64);
    result : bits('N) = undefined : bits('N);
    done : bool = undefined : bool;
    if type1 == FPType_SNaN then {
        done = true;
        result = FPProcessNaN(type1, op1, fpcr)
    } else {
        if type2 == FPType_SNaN then {
            done = true;
            result = FPConvertNaN(FPProcessNaN(type2, op2, fpcr))
        } else {
            if type3 == FPType_SNaN then {
                done = true;
                result = FPConvertNaN(FPProcessNaN(type3, op3, fpcr))
            } else {
                if type1 == FPType_QNaN then {
                    done = true;
                    result = FPProcessNaN(type1, op1, fpcr)
                } else {
                    if type2 == FPType_QNaN then {
                        done = true;
                        result = FPConvertNaN(FPProcessNaN(type2, op2, fpcr))
                    } else {
                        if type3 == FPType_QNaN then {
                            done = true;
                            result = FPConvertNaN(FPProcessNaN(type3, op3, fpcr))
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

val AdvSIMDExpandImm : (bits(1), bits(4), bits(8)) -> bits(64) effect {escape, rreg, undef}

function AdvSIMDExpandImm (op, cmode, imm8) = {
    imm32 : bits(32) = undefined : bits(32);
    imm64 : bits(64) = undefined : bits(64);
    imm8a : bits(8) = undefined : bits(8);
    imm8b : bits(8) = undefined : bits(8);
    imm8c : bits(8) = undefined : bits(8);
    imm8d : bits(8) = undefined : bits(8);
    imm8e : bits(8) = undefined : bits(8);
    imm8f : bits(8) = undefined : bits(8);
    imm8g : bits(8) = undefined : bits(8);
    imm8h : bits(8) = undefined : bits(8);
    match slice(cmode, 1, 3) {
      0b000 => {
          imm64 = replicate_bits(Zeros(24) @ imm8, 2)
      },
      0b001 => {
          imm64 = replicate_bits((Zeros(16) @ imm8) @ Zeros(8), 2)
      },
      0b010 => {
          imm64 = replicate_bits((Zeros(8) @ imm8) @ Zeros(16), 2)
      },
      0b011 => {
          imm64 = replicate_bits(imm8 @ Zeros(24), 2)
      },
      0b100 => {
          imm64 = replicate_bits(Zeros(8) @ imm8, 4)
      },
      0b101 => {
          imm64 = replicate_bits(imm8 @ Zeros(8), 4)
      },
      0b110 => {
          if [cmode[0]] == 0b0 then {
              imm64 = replicate_bits((Zeros(16) @ imm8) @ Ones(8), 2)
          } else {
              imm64 = replicate_bits((Zeros(8) @ imm8) @ Ones(16), 2)
          }
      },
      0b111 => {
          if [cmode[0]] == 0b0 & op == 0b0 then {
              imm64 = replicate_bits(imm8, 8)
          };
          if [cmode[0]] == 0b0 & op == 0b1 then {
              imm8a = replicate_bits([imm8[7]], 8);
              imm8b = replicate_bits([imm8[6]], 8);
              imm8c = replicate_bits([imm8[5]], 8);
              imm8d = replicate_bits([imm8[4]], 8);
              imm8e = replicate_bits([imm8[3]], 8);
              imm8f = replicate_bits([imm8[2]], 8);
              imm8g = replicate_bits([imm8[1]], 8);
              imm8h = replicate_bits([imm8[0]], 8);
              imm64 = ((((((imm8a @ imm8b) @ imm8c) @ imm8d) @ imm8e) @ imm8f) @ imm8g) @ imm8h
          };
          if [cmode[0]] == 0b1 & op == 0b0 then {
              imm32 = ((([imm8[7]] @ ~([imm8[6]])) @ replicate_bits([imm8[6]], 5)) @ slice(imm8, 0, 6)) @ Zeros(19);
              imm64 = replicate_bits(imm32, 2)
          };
          if [cmode[0]] == 0b1 & op == 0b1 then {
              if UsingAArch32() then {
                  throw(Error_ReservedEncoding())
              };
              imm64 = ((([imm8[7]] @ ~([imm8[6]])) @ replicate_bits([imm8[6]], 8)) @ slice(imm8, 0, 6)) @ Zeros(48)
          }
      }
    };
    imm64
}

val HaveSM4Ext : unit -> bool effect {escape}

function HaveSM4Ext () = {
    if ~(HasArchVersion(ARMv8p2)) then {
        return(false)
    };
    __IMPDEF_boolean("Has SM4 Crypto instructions")
}

val HaveSM3Ext : unit -> bool effect {escape}

function HaveSM3Ext () = {
    if ~(HasArchVersion(ARMv8p2)) then {
        return(false)
    };
    __IMPDEF_boolean("Has SM3 Crypto instructions")
}

val HaveSHA512Ext : unit -> bool effect {escape}

function HaveSHA512Ext () = {
    if ~(HasArchVersion(ARMv8p2)) | ~(HaveSHA1Ext() & HaveSHA256Ext()) then {
        return(false)
    };
    __IMPDEF_boolean("Has SHA512 Crypto instructions")
}

val HaveSHA3Ext : unit -> bool effect {escape}

function HaveSHA3Ext () = {
    if ~(HasArchVersion(ARMv8p2)) | ~(HaveSHA1Ext() & HaveSHA256Ext()) then {
        return(false)
    };
    __IMPDEF_boolean("Has SHA3 Crypto instructions")
}

val HaveFP16MulNoRoundingToFP32Ext : unit -> bool effect {escape}

function HaveFP16MulNoRoundingToFP32Ext () = {
    if ~(HaveFP16Ext()) then {
        return(false)
    };
    if HasArchVersion(ARMv8p4) then {
        return(true)
    };
    HasArchVersion(ARMv8p2) & __IMPDEF_boolean("Has accumulate FP16 product into FP32 extension")
}

val FPRecpX : forall ('N : Int), 'N >= 0.
  (bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRecpX (op, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    let 'esize : {|5, 8, 11|} = match 'N {
      16 => 5,
      32 => 8,
      64 => 11
    };
    result : bits('N) = undefined : bits('N);
    exp : bits('esize) = undefined : bits('esize);
    max_exp : bits('esize) = undefined : bits('esize);
    let frac : bits('N - 'esize - 1) = Zeros();
    match 'N {
      16 => {
          exp = slice(op, 10, esize)
      },
      32 => {
          exp = slice(op, 23, esize)
      },
      64 => {
          exp = slice(op, 52, esize)
      }
    };
    let max_exp = Ones(esize) - 1;
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(op, fpcr);
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        result = FPProcessNaN(typ, op, fpcr)
    } else {
        if IsZero(exp) then {
            result = (sign @ max_exp) @ frac
        } else {
            result = (sign @ ~(exp)) @ frac
        }
    };
    result
}

val FPRecipEstimate : forall ('N : Int), 'N >= 0.
  (bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRecipEstimate (operand, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(operand, fpcr);
    estimate : int = undefined : int;
    exp : int = undefined : int;
    fraction : bits(52) = undefined : bits(52);
    overflow_to_inf : bool = undefined : bool;
    result : bits('N) = undefined : bits('N);
    result_exp : int = undefined : int;
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        result = FPProcessNaN(typ, operand, fpcr)
    } else {
        if typ == FPType_Infinity then {
            result = FPZero(sign)
        } else {
            if typ == FPType_Zero then {
                result = FPInfinity(sign);
                FPProcessException(FPExc_DivideByZero, fpcr)
            } else {
                if ('N == 16 & abs(value_name) < 2.0 ^ negate(16) | 'N == 32 & abs(value_name) < 2.0 ^ negate(128)) | 'N == 64 & abs(value_name) < 2.0 ^ negate(1024) then {
                    match FPRoundingMode(fpcr) {
                      FPRounding_TIEEVEN => {
                          overflow_to_inf = true
                      },
                      FPRounding_POSINF => {
                          overflow_to_inf = sign == 0b0
                      },
                      FPRounding_NEGINF => {
                          overflow_to_inf = sign == 0b1
                      },
                      FPRounding_ZERO => {
                          overflow_to_inf = false
                      }
                    };
                    result = if overflow_to_inf then FPInfinity(sign) else FPMaxNormal(sign);
                    FPProcessException(FPExc_Overflow, fpcr);
                    FPProcessException(FPExc_Inexact, fpcr)
                } else {
                    if ([fpcr[24]] == 0b1 & 'N != 16 | [fpcr[19]] == 0b1 & 'N == 16) & (('N == 16 & abs(value_name) >= 2.0 ^ 14 | 'N == 32 & abs(value_name) >= 2.0 ^ 126) | 'N == 64 & abs(value_name) >= 2.0 ^ 1022) then {
                        result = FPZero(sign);
                        if UsingAArch32() then {
                            FPSCR = __SetSlice_bits(32, 1, FPSCR, 3, 0b1)
                        } else {
                            FPSR = __SetSlice_bits(32, 1, FPSR, 3, 0b1)
                        }
                    } else {
                        match 'N {
                          16 => {
                              fraction = slice(operand, 0, 10) @ Zeros(42);
                              exp = UInt(slice(operand, 10, 5))
                          },
                          32 => {
                              fraction = slice(operand, 0, 23) @ Zeros(29);
                              exp = UInt(slice(operand, 23, 8))
                          },
                          64 => {
                              fraction = slice(operand, 0, 52);
                              exp = UInt(slice(operand, 52, 11))
                          }
                        };
                        if exp == 0 then {
                            if [fraction[51]] == 0 then {
                                exp = negate(1);
                                fraction = slice(fraction, 0, 50) @ 0b00
                            } else {
                                fraction = slice(fraction, 0, 51) @ 0b0
                            }
                        };
                        let 'scaled = UInt(0b1 @ slice(fraction, 44, 8));
                        match 'N {
                          16 => {
                              result_exp = 29 - exp
                          },
                          32 => {
                              result_exp = 253 - exp
                          },
                          64 => {
                              result_exp = 2045 - exp
                          }
                        };
                        estimate = RecipEstimate(scaled);
                        fraction = __GetSlice_int(8, estimate, 0) @ Zeros(44);
                        if result_exp == 0 then {
                            fraction = 0b1 @ slice(fraction, 1, 51)
                        } else {
                            if result_exp == negate(1) then {
                                fraction = 0b01 @ slice(fraction, 2, 50);
                                result_exp = 0
                            }
                        };
                        match 'N {
                          16 => {
                              result = (sign @ __GetSlice_int('N - 11, result_exp, 0)) @ slice(fraction, 42, 10)
                          },
                          32 => {
                              result = (sign @ __GetSlice_int('N - 24, result_exp, 0)) @ slice(fraction, 29, 23)
                          },
                          64 => {
                              result = (sign @ __GetSlice_int('N - 53, result_exp, 0)) @ slice(fraction, 0, 52)
                          }
                        }
                    }
                }
            }
        }
    };
    result
}

val FPRSqrtEstimate : forall ('N : Int), 'N >= 0.
  (bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRSqrtEstimate (operand, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign : bits(1) = undefined : bits(1);
    typ : FPType = undefined : FPType;
    value_name : real = undefined : real;
    (typ, sign, value_name) = FPUnpack(operand, fpcr);
    estimate : int = undefined : int;
    exp : int = undefined : int;
    fraction : bits(52) = undefined : bits(52);
    result : bits('N) = undefined : bits('N);
    result_exp : int = undefined : int;
    scaled : int = undefined : int;
    if typ == FPType_SNaN | typ == FPType_QNaN then {
        result = FPProcessNaN(typ, operand, fpcr)
    } else {
        if typ == FPType_Zero then {
            result = FPInfinity(sign);
            FPProcessException(FPExc_DivideByZero, fpcr)
        } else {
            if sign == 0b1 then {
                result = FPDefaultNaN();
                FPProcessException(FPExc_InvalidOp, fpcr)
            } else {
                if typ == FPType_Infinity then {
                    result = FPZero(0b0)
                } else {
                    match 'N {
                      16 => {
                          fraction = slice(operand, 0, 10) @ Zeros(42);
                          exp = UInt(slice(operand, 10, 5))
                      },
                      32 => {
                          fraction = slice(operand, 0, 23) @ Zeros(29);
                          exp = UInt(slice(operand, 23, 8))
                      },
                      64 => {
                          fraction = slice(operand, 0, 52);
                          exp = UInt(slice(operand, 52, 11))
                      }
                    };
                    if exp == 0 then {
                        while [fraction[51]] == 0 do {
                            fraction = slice(fraction, 0, 51) @ 0b0;
                            exp = exp - 1
                        };
                        fraction = slice(fraction, 0, 51) @ 0b0
                    };
                    if __GetSlice_int(1, exp, 0) == 0b0 then {
                        scaled = UInt(0b1 @ slice(fraction, 44, 8))
                    } else {
                        scaled = UInt(0b01 @ slice(fraction, 45, 7))
                    };
                    match 'N {
                      16 => {
                          result_exp = (44 - exp) / 2
                      },
                      32 => {
                          result_exp = (380 - exp) / 2
                      },
                      64 => {
                          result_exp = (3068 - exp) / 2
                      }
                    };
                    estimate = RecipSqrtEstimate(scaled);
                    match 'N {
                      16 => {
                          result = ((0b0 @ __GetSlice_int('N - 11, result_exp, 0)) @ __GetSlice_int(8, estimate, 0)) @ Zeros(2)
                      },
                      32 => {
                          result = ((0b0 @ __GetSlice_int('N - 24, result_exp, 0)) @ __GetSlice_int(8, estimate, 0)) @ Zeros(15)
                      },
                      64 => {
                          result = ((0b0 @ __GetSlice_int('N - 53, result_exp, 0)) @ __GetSlice_int(8, estimate, 0)) @ Zeros(44)
                      }
                    }
                }
            }
        }
    };
    result
}

val FPCompareGT : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bool effect {escape, rreg, undef, wreg}

function FPCompareGT (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    result : bool = undefined : bool;
    if ((type1 == FPType_SNaN | type1 == FPType_QNaN) | type2 == FPType_SNaN) | type2 == FPType_QNaN then {
        result = false;
        FPProcessException(FPExc_InvalidOp, fpcr)
    } else {
        result = value1_name > value2_name
    };
    result
}

val FPCompareGE : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bool effect {escape, rreg, undef, wreg}

function FPCompareGE (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    result : bool = undefined : bool;
    if ((type1 == FPType_SNaN | type1 == FPType_QNaN) | type2 == FPType_SNaN) | type2 == FPType_QNaN then {
        result = false;
        FPProcessException(FPExc_InvalidOp, fpcr)
    } else {
        result = value1_name >= value2_name
    };
    result
}

val FPCompareEQ : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bool effect {escape, rreg, undef, wreg}

function FPCompareEQ (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    result : bool = undefined : bool;
    if ((type1 == FPType_SNaN | type1 == FPType_QNaN) | type2 == FPType_SNaN) | type2 == FPType_QNaN then {
        result = false;
        if type1 == FPType_SNaN | type2 == FPType_SNaN then {
            FPProcessException(FPExc_InvalidOp, fpcr)
        }
    } else {
        result = value1_name == value2_name
    };
    result
}

val FPRecipStepFused : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRecipStepFused (op1, op2) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    result : bits('N) = undefined : bits('N);
    let op1 = FPNeg(op1);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, FPCR);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, FPCR);
    done : bool = undefined : bool;
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, FPCR);
    inf1 : bool = undefined : bool;
    inf2 : bool = undefined : bool;
    result_value : real = undefined : real;
    sign : bits(1) = undefined : bits(1);
    zero1 : bool = undefined : bool;
    zero2 : bool = undefined : bool;
    if ~(done) then {
        inf1 = type1 == FPType_Infinity;
        inf2 = type2 == FPType_Infinity;
        zero1 = type1 == FPType_Zero;
        zero2 = type2 == FPType_Zero;
        if inf1 & zero2 | zero1 & inf2 then {
            result = FPTwo(0b0)
        } else {
            if inf1 | inf2 then {
                result = FPInfinity(sign1 ^ sign2)
            } else {
                result_value = 2.0 + value1_name * value2_name;
                if result_value == 0.0 then {
                    sign = if FPRoundingMode(FPCR) == FPRounding_NEGINF then 0b1 else 0b0;
                    result = FPZero(sign)
                } else {
                    result = FPRound(result_value, FPCR)
                }
            }
        }
    };
    result
}

val FPRSqrtStepFused : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRSqrtStepFused (op1, op2) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    result : bits('N) = undefined : bits('N);
    let op1 = FPNeg(op1);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, FPCR);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, FPCR);
    done : bool = undefined : bool;
    (done, result) = FPProcessNaNs(type1, type2, op1, op2, FPCR);
    inf1 : bool = undefined : bool;
    inf2 : bool = undefined : bool;
    result_value : real = undefined : real;
    sign : bits(1) = undefined : bits(1);
    zero1 : bool = undefined : bool;
    zero2 : bool = undefined : bool;
    if ~(done) then {
        inf1 = type1 == FPType_Infinity;
        inf2 = type2 == FPType_Infinity;
        zero1 = type1 == FPType_Zero;
        zero2 = type2 == FPType_Zero;
        if inf1 & zero2 | zero1 & inf2 then {
            result = FPOnePointFive(0b0)
        } else {
            if inf1 | inf2 then {
                result = FPInfinity(sign1 ^ sign2)
            } else {
                result_value = (3.0 + value1_name * value2_name) / 2.0;
                if result_value == 0.0 then {
                    sign = if FPRoundingMode(FPCR) == FPRounding_NEGINF then 0b1 else 0b0;
                    result = FPZero(sign)
                } else {
                    result = FPRound(result_value, FPCR)
                }
            }
        }
    };
    result
}

val FPMulX : forall ('N : Int), ('N >= 0 & 'N >= 0).
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMulX (op1, op2, fpcr) = {
    assert('N == 16 | 'N == 32 | 'N == 64);
    result : bits('N) = undefined : bits('N);
    sign1 : bits(1) = undefined : bits(1);
    type1 : FPType = undefined : FPType;
    value1_name : real = undefined : real;
    (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
    sign2 : bits(1) = undefined : bits(1);
    type2 : FPType = undefined : FPType;
    value2_name : real = undefined : real;
    (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
    done : bool = undefined : bool;
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
            result = FPTwo(sign1 ^ sign2)
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

val FPMulAddH : forall ('N : Int), 'N >= 0.
  (bits('N), bits(div('N, 2)), bits(div('N, 2)), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMulAddH (addend, op1, op2, fpcr) = {
    assert('N == 32 | 'N == 64);
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
    (done, result) = FPProcessNaNs3H(typeA, type1, type2, addend, op1, op2, fpcr);
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

val Reduce : forall 'N 'esize,
  'N >= 0 & ('esize >= 0 & 'esize >= 0).
  (ReduceOp, bits('N), int('esize)) -> bits('esize) effect {escape, rreg, undef, wreg}

function Reduce (op, input, esize) = {
    half : int = undefined : int;
    hi : bits('esize) = undefined : bits('esize);
    lo : bits('esize) = undefined : bits('esize);
    result : bits('esize) = undefined : bits('esize);
    if 'N == esize then {
        return(slice(input, 0, esize))
    };
    let half = 'N / 2;
    let hi = Reduce(op, slice(input, half, negate(half) + 'N), esize);
    let lo = Reduce(op, slice(input, 0, half), esize);
    match op {
      ReduceOp_FMINNUM => {
          result = FPMinNum(lo, hi, FPCR)
      },
      ReduceOp_FMAXNUM => {
          result = FPMaxNum(lo, hi, FPCR)
      },
      ReduceOp_FMIN => {
          result = FPMin(lo, hi, FPCR)
      },
      ReduceOp_FMAX => {
          result = FPMax(lo, hi, FPCR)
      },
      ReduceOp_FADD => {
          result = FPAdd(lo, hi, FPCR)
      },
      ReduceOp_ADD => {
          result = lo + hi
      }
    };
    let result = result;
    result
}

val vector_crypto_sm4_sm4enckey : forall 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm4_sm4enckey (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    intval : bits(32) = undefined : bits(32);
    let sboxout = undefined : bits(8);
    let result = undefined : bits(128);
    const : bits(32) = undefined : bits(32);
    roundresult : bits(128) = undefined : bits(128);
    roundresult = V(n);
    foreach (index from 0 to 3 by 1 in inc) {
        const = aget_Elem(Vm, index, 32);
        intval = ((slice(roundresult, 96, 32) ^ slice(roundresult, 64, 32)) ^ slice(roundresult, 32, 32)) ^ const;
        foreach (i from 0 to 3 by 1 in inc) {
            intval = aset_Elem(intval, i, 8, Sbox(aget_Elem(intval, i, 8)))
        };
        intval = (intval ^ ROL(intval, 13)) ^ ROL(intval, 23);
        intval = intval ^ slice(roundresult, 0, 32);
        roundresult = __SetSlice_bits(128, 32, roundresult, 0, slice(roundresult, 32, 32));
        roundresult = __SetSlice_bits(128, 32, roundresult, 32, slice(roundresult, 64, 32));
        roundresult = __SetSlice_bits(128, 32, roundresult, 64, slice(roundresult, 96, 32));
        roundresult = __SetSlice_bits(128, 32, roundresult, 96, intval)
    };
    V(d) = roundresult
}

val vector_crypto_sm4_sm4enckey_decode__0 : (bits(5), bits(5), bits(2), bits(1), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm4_sm4enckey_decode__1 : (bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm4_sm4enckey_decode = {
  vector_crypto_sm4_sm4enckey_decode__0,
  vector_crypto_sm4_sm4enckey_decode__1
}

function vector_crypto_sm4_sm4enckey_decode__0 (Rd, Rn, opcode, O, Rm) = {
    __unconditional = true;
    if ~(HaveSM4Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sm4_sm4enckey(d, m, n)
}

function vector_crypto_sm4_sm4enckey_decode__1 (Rd, Rn, Rm) = {
    __unconditional = true;
    if ~(HaveSM4Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sm4_sm4enckey(d, m, n)
}

val vector_crypto_sm4_sm4enc : forall 'd 'n,
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm4_sm4enc (d, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vn : bits(128) = V(n);
    intval : bits(32) = undefined : bits(32);
    let sboxout = undefined : bits(8);
    roundresult : bits(128) = undefined : bits(128);
    roundkey : bits(32) = undefined : bits(32);
    roundresult = V(d);
    foreach (index from 0 to 3 by 1 in inc) {
        roundkey = aget_Elem(Vn, index, 32);
        intval = ((slice(roundresult, 96, 32) ^ slice(roundresult, 64, 32)) ^ slice(roundresult, 32, 32)) ^ roundkey;
        foreach (i from 0 to 3 by 1 in inc) {
            intval = aset_Elem(intval, i, 8, Sbox(aget_Elem(intval, i, 8)))
        };
        intval = (((intval ^ ROL(intval, 2)) ^ ROL(intval, 10)) ^ ROL(intval, 18)) ^ ROL(intval, 24);
        intval = intval ^ slice(roundresult, 0, 32);
        roundresult = __SetSlice_bits(128, 32, roundresult, 0, slice(roundresult, 32, 32));
        roundresult = __SetSlice_bits(128, 32, roundresult, 32, slice(roundresult, 64, 32));
        roundresult = __SetSlice_bits(128, 32, roundresult, 64, slice(roundresult, 96, 32));
        roundresult = __SetSlice_bits(128, 32, roundresult, 96, intval)
    };
    V(d) = roundresult
}

val vector_crypto_sm4_sm4enc_decode__0 : (bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm4_sm4enc_decode__1 : (bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm4_sm4enc_decode = {
  vector_crypto_sm4_sm4enc_decode__0,
  vector_crypto_sm4_sm4enc_decode__1
}

function vector_crypto_sm4_sm4enc_decode__0 (Rd, Rn) = {
    __unconditional = true;
    if ~(HaveSM4Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    __PostDecode();
    vector_crypto_sm4_sm4enc(d, n)
}

function vector_crypto_sm4_sm4enc_decode__1 (Rd, Rn, opcode) = {
    __unconditional = true;
    if ~(HaveSM4Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    __PostDecode();
    vector_crypto_sm4_sm4enc(d, n)
}

val vector_crypto_sm3_sm3tt2b : forall 'd 'i 'm 'n,
  ('m >= 0 & 'm <= 31 & 'n >= 0 & 'n <= 31 & 'd >= 0 & 'd <= 31 & 'i >= 0 & ('i + 1) * 32 <= 128).
  (int('d), int('i), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm3_sm3tt2b (d, i, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = aget_V(m);
    let Vn : bits(128) = aget_V(n);
    let Vd : bits(128) = aget_V(d);
    Wj : bits(32) = undefined : bits(32);
    result : bits(128) = undefined : bits(128);
    TT2 : bits(32) = undefined : bits(32);
    let Wj = aget_Elem(Vm, i, 32);
    TT2 = slice(Vd, 96, 32) & slice(Vd, 64, 32) | ~(slice(Vd, 96, 32)) & slice(Vd, 32, 32);
    let TT2 = slice(TT2 + slice(Vd, 0, 32) + slice(Vn, 96, 32) + Wj, 0, 32);
    result = __SetSlice_bits(128, 32, result, 0, slice(Vd, 32, 32));
    result = __SetSlice_bits(128, 32, result, 32, ROL(slice(Vd, 64, 32), 19));
    result = __SetSlice_bits(128, 32, result, 64, slice(Vd, 96, 32));
    let result = __SetSlice_bits(128, 32, result, 96, (TT2 ^ ROL(TT2, 9)) ^ ROL(TT2, 17));
    aset_V(d, result)
}

val vector_crypto_sm3_sm3tt2b_decode__0 : (bits(5), bits(5), bits(2), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm3_sm3tt2b_decode__1 : (bits(5), bits(5), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm3_sm3tt2b_decode = {
  vector_crypto_sm3_sm3tt2b_decode__0,
  vector_crypto_sm3_sm3tt2b_decode__1
}

function vector_crypto_sm3_sm3tt2b_decode__0 (Rd, Rn, opcode, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt2b(d, i, m, n)
}

function vector_crypto_sm3_sm3tt2b_decode__1 (Rd, Rn, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt2b(d, i, m, n)
}

val vector_crypto_sm3_sm3tt2a : forall 'd 'i 'm 'n,
  ('m >= 0 & 'm <= 31 & 'n >= 0 & 'n <= 31 & 'd >= 0 & 'd <= 31 & 'i >= 0 & ('i + 1) * 32 <= 128).
  (int('d), int('i), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm3_sm3tt2a (d, i, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = aget_V(m);
    let Vn : bits(128) = aget_V(n);
    let Vd : bits(128) = aget_V(d);
    Wj : bits(32) = undefined : bits(32);
    result : bits(128) = undefined : bits(128);
    let TT1 : bits(32) = undefined : bits(32);
    let Wj = aget_Elem(Vm, i, 32);
    TT2 : bits(32) = undefined : bits(32);
    TT2 = slice(Vd, 32, 32) ^ slice(Vd, 96, 32) ^ slice(Vd, 64, 32);
    let TT2 = slice(TT2 + slice(Vd, 0, 32) + slice(Vn, 96, 32) + Wj, 0, 32);
    result = __SetSlice_bits(128, 32, result, 0, slice(Vd, 32, 32));
    result = __SetSlice_bits(128, 32, result, 32, ROL(slice(Vd, 64, 32), 19));
    result = __SetSlice_bits(128, 32, result, 64, slice(Vd, 96, 32));
    let result = __SetSlice_bits(128, 32, result, 96, (TT2 ^ ROL(TT2, 9)) ^ ROL(TT2, 17));
    aset_V(d, result)
}

val vector_crypto_sm3_sm3tt2a_decode__0 : (bits(5), bits(5), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm3_sm3tt2a_decode__1 : (bits(5), bits(5), bits(2), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm3_sm3tt2a_decode = {
  vector_crypto_sm3_sm3tt2a_decode__0,
  vector_crypto_sm3_sm3tt2a_decode__1
}

function vector_crypto_sm3_sm3tt2a_decode__0 (Rd, Rn, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt2a(d, i, m, n)
}

function vector_crypto_sm3_sm3tt2a_decode__1 (Rd, Rn, opcode, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt2a(d, i, m, n)
}

val vector_crypto_sm3_sm3tt1b : forall 'd 'i 'm 'n,
  ('m >= 0 & 'm <= 31 & 'n >= 0 & 'n <= 31 & 'd >= 0 & 'd <= 31 & 'i >= 0 & ('i + 1) * 32 <= 128).
  (int('d), int('i), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm3_sm3tt1b (d, i, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = aget_V(m);
    let Vn : bits(128) = aget_V(n);
    let Vd : bits(128) = aget_V(d);
    WjPrime : bits(32) = undefined : bits(32);
    result : bits(128) = undefined : bits(128);
    TT1 : bits(32) = undefined : bits(32);
    SS2 : bits(32) = undefined : bits(32);
    let WjPrime = aget_Elem(Vm, i, 32);
    let SS2 = slice(Vn, 96, 32) ^ ROL(slice(Vd, 96, 32), 12);
    TT1 = (slice(Vd, 96, 32) & slice(Vd, 32, 32) | slice(Vd, 96, 32) & slice(Vd, 64, 32)) | slice(Vd, 32, 32) & slice(Vd, 64, 32);
    let TT1 = slice(TT1 + slice(Vd, 0, 32) + SS2 + WjPrime, 0, 32);
    result = __SetSlice_bits(128, 32, result, 0, slice(Vd, 32, 32));
    result = __SetSlice_bits(128, 32, result, 32, ROL(slice(Vd, 64, 32), 9));
    result = __SetSlice_bits(128, 32, result, 64, slice(Vd, 96, 32));
    let result = __SetSlice_bits(128, 32, result, 96, TT1);
    aset_V(d, result)
}

val vector_crypto_sm3_sm3tt1b_decode__0 : (bits(5), bits(5), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm3_sm3tt1b_decode__1 : (bits(5), bits(5), bits(2), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm3_sm3tt1b_decode = {
  vector_crypto_sm3_sm3tt1b_decode__0,
  vector_crypto_sm3_sm3tt1b_decode__1
}

function vector_crypto_sm3_sm3tt1b_decode__0 (Rd, Rn, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt1b(d, i, m, n)
}

function vector_crypto_sm3_sm3tt1b_decode__1 (Rd, Rn, opcode, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt1b(d, i, m, n)
}

val vector_crypto_sm3_sm3tt1a : forall 'd 'i 'm 'n,
  ('m >= 0 & 'm <= 31 & 'n >= 0 & 'n <= 31 & 'd >= 0 & 'd <= 31 & 'i >= 0 & ('i + 1) * 32 <= 128).
  (int('d), int('i), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm3_sm3tt1a (d, i, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = aget_V(m);
    let Vn : bits(128) = aget_V(n);
    let Vd : bits(128) = aget_V(d);
    WjPrime : bits(32) = undefined : bits(32);
    result : bits(128) = undefined : bits(128);
    TT1 : bits(32) = undefined : bits(32);
    SS2 : bits(32) = undefined : bits(32);
    let WjPrime = aget_Elem(Vm, i, 32);
    let SS2 = slice(Vn, 96, 32) ^ ROL(slice(Vd, 96, 32), 12);
    TT1 = slice(Vd, 32, 32) ^ slice(Vd, 96, 32) ^ slice(Vd, 64, 32);
    let TT1 = slice(TT1 + slice(Vd, 0, 32) + SS2 + WjPrime, 0, 32);
    result = __SetSlice_bits(128, 32, result, 0, slice(Vd, 32, 32));
    result = __SetSlice_bits(128, 32, result, 32, ROL(slice(Vd, 64, 32), 9));
    result = __SetSlice_bits(128, 32, result, 64, slice(Vd, 96, 32));
    let result = __SetSlice_bits(128, 32, result, 96, TT1);
    aset_V(d, result)
}

val vector_crypto_sm3_sm3tt1a_decode__0 : (bits(5), bits(5), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm3_sm3tt1a_decode__1 : (bits(5), bits(5), bits(2), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm3_sm3tt1a_decode = {
  vector_crypto_sm3_sm3tt1a_decode__0,
  vector_crypto_sm3_sm3tt1a_decode__1
}

function vector_crypto_sm3_sm3tt1a_decode__0 (Rd, Rn, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt1a(d, i, m, n)
}

function vector_crypto_sm3_sm3tt1a_decode__1 (Rd, Rn, opcode, imm2, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'i = UInt(imm2);
    __PostDecode();
    vector_crypto_sm3_sm3tt1a(d, i, m, n)
}

val vector_crypto_sm3_sm3ss1 : forall 'a 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31) & ('a >= 0 & 'a <= 31).
  (int('a), int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm3_sm3ss1 (a, d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    let Vn : bits(128) = V(n);
    Vd : bits(128) = V(d);
    let Va : bits(128) = V(a);
    Vd = __SetSlice_bits(128, 32, Vd, 96, ROL(ROL(slice(Vn, 96, 32), 12) + slice(Vm, 96, 32) + slice(Va, 96, 32), 7));
    let Vd = __SetSlice_bits(128, 96, Vd, 0, Zeros());
    V(d) = Vd
}

val vector_crypto_sm3_sm3ss1_decode__0 : (bits(5), bits(5), bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm3_sm3ss1_decode__1 : (bits(5), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm3_sm3ss1_decode = {
  vector_crypto_sm3_sm3ss1_decode__0,
  vector_crypto_sm3_sm3ss1_decode__1
}

function vector_crypto_sm3_sm3ss1_decode__0 (Rd, Rn, Ra, Rm, Op0) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'a = UInt(Ra);
    __PostDecode();
    vector_crypto_sm3_sm3ss1(a, d, m, n)
}

function vector_crypto_sm3_sm3ss1_decode__1 (Rd, Rn, Ra, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'a = UInt(Ra);
    __PostDecode();
    vector_crypto_sm3_sm3ss1(a, d, m, n)
}

val vector_crypto_sm3_sm3partw2 : forall 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm3_sm3partw2 (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    let Vn : bits(128) = V(n);
    let Vd : bits(128) = V(d);
    result : bits(128) = undefined : bits(128);
    tmp : bits(128) = undefined : bits(128);
    tmp2 : bits(32) = undefined : bits(32);
    let tmp = __SetSlice_bits(128, 128, tmp, 0, Vn ^ (((ROL(slice(Vm, 96, 32), 7) @ ROL(slice(Vm, 64, 32), 7)) @ ROL(slice(Vm, 32, 32), 7)) @ ROL(slice(Vm, 0, 32), 7)));
    result = __SetSlice_bits(128, 128, result, 0, slice(Vd, 0, 128) ^ slice(tmp, 0, 128));
    tmp2 = ROL(slice(tmp, 0, 32), 15);
    let tmp2 = (tmp2 ^ ROL(tmp2, 15)) ^ ROL(tmp2, 23);
    let result = __SetSlice_bits(128, 32, result, 96, slice(result, 96, 32) ^ tmp2);
    V(d) = result
}

val vector_crypto_sm3_sm3partw2_decode__0 : (bits(5), bits(5), bits(2), bits(1), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm3_sm3partw2_decode__1 : (bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm3_sm3partw2_decode = {
  vector_crypto_sm3_sm3partw2_decode__0,
  vector_crypto_sm3_sm3partw2_decode__1
}

function vector_crypto_sm3_sm3partw2_decode__0 (Rd, Rn, opcode, O, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sm3_sm3partw2(d, m, n)
}

function vector_crypto_sm3_sm3partw2_decode__1 (Rd, Rn, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sm3_sm3partw2(d, m, n)
}

val vector_crypto_sm3_sm3partw1 : forall 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sm3_sm3partw1 (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    let Vn : bits(128) = V(n);
    let Vd : bits(128) = V(d);
    result : bits(128) = undefined : bits(128);
    result = __SetSlice_bits(128, 96, result, 0, slice(Vd ^ Vn, 0, 96) ^ ((ROL(slice(Vm, 96, 32), 15) @ ROL(slice(Vm, 64, 32), 15)) @ ROL(slice(Vm, 32, 32), 15)));
    foreach (i from 0 to 3 by 1 in inc) {
        if i == 3 then {
            result = __SetSlice_bits(128, 32, result, 96, slice(Vd ^ Vn, 96, 32) ^ ROL(slice(result, 0, 32), 15))
        };
        result = __SetSlice_bits(128, 32, result, 32 * i, (slice(result, 32 * i, 32) ^ ROL(slice(result, 32 * i, 32), 15)) ^ ROL(slice(result, 32 * i, 32), 23))
    };
    V(d) = result
}

val vector_crypto_sm3_sm3partw1_decode__0 : (bits(5), bits(5), bits(2), bits(1), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sm3_sm3partw1_decode__1 : (bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sm3_sm3partw1_decode = {
  vector_crypto_sm3_sm3partw1_decode__0,
  vector_crypto_sm3_sm3partw1_decode__1
}

function vector_crypto_sm3_sm3partw1_decode__0 (Rd, Rn, opcode, O, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sm3_sm3partw1(d, m, n)
}

function vector_crypto_sm3_sm3partw1_decode__1 (Rd, Rn, Rm) = {
    __unconditional = true;
    if ~(HaveSM3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sm3_sm3partw1(d, m, n)
}

val vector_crypto_sha512_sha512su1 : forall 'd 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha512_sha512su1 (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    sig1 : bits(64) = undefined : bits(64);
    Vtmp : bits(128) = undefined : bits(128);
    let X : bits(128) = V(n);
    let Y : bits(128) = V(m);
    let W : bits(128) = V(d);
    sig1 = (ROR(slice(X, 64, 64), 19) ^ ROR(slice(X, 64, 64), 61)) ^ (0b000000 @ slice(X, 70, 58));
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 64, slice(W, 64, 64) + sig1 + slice(Y, 64, 64));
    let sig1 = (ROR(slice(X, 0, 64), 19) ^ ROR(slice(X, 0, 64), 61)) ^ (0b000000 @ slice(X, 6, 58));
    let Vtmp = __SetSlice_bits(128, 64, Vtmp, 0, slice(W, 0, 64) + sig1 + slice(Y, 0, 64));
    V(d) = Vtmp
}

val vector_crypto_sha512_sha512su1_decode__0 : (bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sha512_sha512su1_decode__1 : (bits(5), bits(5), bits(2), bits(1), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sha512_sha512su1_decode = {
  vector_crypto_sha512_sha512su1_decode__0,
  vector_crypto_sha512_sha512su1_decode__1
}

function vector_crypto_sha512_sha512su1_decode__0 (Rd, Rn, Rm) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha512_sha512su1(d, m, n)
}

function vector_crypto_sha512_sha512su1_decode__1 (Rd, Rn, opcode, O, Rm) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha512_sha512su1(d, m, n)
}

val vector_crypto_sha512_sha512su0 : forall 'd 'n,
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha512_sha512su0 (d, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    sig0 : bits(64) = undefined : bits(64);
    Vtmp : bits(128) = undefined : bits(128);
    let X : bits(128) = V(n);
    let W : bits(128) = V(d);
    sig0 = (ROR(slice(W, 64, 64), 1) ^ ROR(slice(W, 64, 64), 8)) ^ (0b0000000 @ slice(W, 71, 57));
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 0, slice(W, 0, 64) + sig0);
    let sig0 = (ROR(slice(X, 0, 64), 1) ^ ROR(slice(X, 0, 64), 8)) ^ (0b0000000 @ slice(X, 7, 57));
    let Vtmp = __SetSlice_bits(128, 64, Vtmp, 64, slice(W, 64, 64) + sig0);
    V(d) = Vtmp
}

val vector_crypto_sha512_sha512su0_decode__0 : (bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sha512_sha512su0_decode__1 : (bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sha512_sha512su0_decode = {
  vector_crypto_sha512_sha512su0_decode__0,
  vector_crypto_sha512_sha512su0_decode__1
}

function vector_crypto_sha512_sha512su0_decode__0 (Rd, Rn, opcode) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    __PostDecode();
    vector_crypto_sha512_sha512su0(d, n)
}

function vector_crypto_sha512_sha512su0_decode__1 (Rd, Rn) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    __PostDecode();
    vector_crypto_sha512_sha512su0(d, n)
}

val vector_crypto_sha512_sha512h : forall 'd 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha512_sha512h (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    Vtmp : bits(128) = undefined : bits(128);
    MSigma1 : bits(64) = undefined : bits(64);
    tmp : bits(64) = undefined : bits(64);
    let X : bits(128) = V(n);
    let Y : bits(128) = V(m);
    let W : bits(128) = V(d);
    MSigma1 = (ROR(slice(Y, 64, 64), 14) ^ ROR(slice(Y, 64, 64), 18)) ^ ROR(slice(Y, 64, 64), 41);
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 64, (slice(Y, 64, 64) & slice(X, 0, 64)) ^ (~(slice(Y, 64, 64)) & slice(X, 64, 64)));
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 64, slice(Vtmp, 64, 64) + MSigma1 + slice(W, 64, 64));
    let tmp = slice(Vtmp, 64, 64) + slice(Y, 0, 64);
    let MSigma1 = (ROR(tmp, 14) ^ ROR(tmp, 18)) ^ ROR(tmp, 41);
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 0, (tmp & slice(Y, 64, 64)) ^ (~(tmp) & slice(X, 0, 64)));
    let Vtmp = __SetSlice_bits(128, 64, Vtmp, 0, slice(Vtmp, 0, 64) + MSigma1 + slice(W, 0, 64));
    V(d) = Vtmp
}

val vector_crypto_sha512_sha512h_decode__0 : (bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sha512_sha512h_decode__1 : (bits(5), bits(5), bits(2), bits(1), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sha512_sha512h_decode = {
  vector_crypto_sha512_sha512h_decode__0,
  vector_crypto_sha512_sha512h_decode__1
}

function vector_crypto_sha512_sha512h_decode__0 (Rd, Rn, Rm) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha512_sha512h(d, m, n)
}

function vector_crypto_sha512_sha512h_decode__1 (Rd, Rn, opcode, O, Rm) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha512_sha512h(d, m, n)
}

val vector_crypto_sha512_sha512h2 : forall 'd 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha512_sha512h2 (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    Vtmp : bits(128) = undefined : bits(128);
    NSigma0 : bits(64) = undefined : bits(64);
    let tmp = undefined : bits(64);
    let X : bits(128) = V(n);
    let Y : bits(128) = V(m);
    let W : bits(128) = V(d);
    NSigma0 = (ROR(slice(Y, 0, 64), 28) ^ ROR(slice(Y, 0, 64), 34)) ^ ROR(slice(Y, 0, 64), 39);
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 64, ((slice(X, 0, 64) & slice(Y, 64, 64)) ^ (slice(X, 0, 64) & slice(Y, 0, 64))) ^ (slice(Y, 64, 64) & slice(Y, 0, 64)));
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 64, slice(Vtmp, 64, 64) + NSigma0 + slice(W, 64, 64));
    let NSigma0 = (ROR(slice(Vtmp, 64, 64), 28) ^ ROR(slice(Vtmp, 64, 64), 34)) ^ ROR(slice(Vtmp, 64, 64), 39);
    Vtmp = __SetSlice_bits(128, 64, Vtmp, 0, ((slice(Vtmp, 64, 64) & slice(Y, 0, 64)) ^ (slice(Vtmp, 64, 64) & slice(Y, 64, 64))) ^ (slice(Y, 64, 64) & slice(Y, 0, 64)));
    let Vtmp = __SetSlice_bits(128, 64, Vtmp, 0, slice(Vtmp, 0, 64) + NSigma0 + slice(W, 0, 64));
    V(d) = Vtmp
}

val vector_crypto_sha512_sha512h2_decode__0 : (bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sha512_sha512h2_decode__1 : (bits(5), bits(5), bits(2), bits(1), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sha512_sha512h2_decode = {
  vector_crypto_sha512_sha512h2_decode__0,
  vector_crypto_sha512_sha512h2_decode__1
}

function vector_crypto_sha512_sha512h2_decode__0 (Rd, Rn, Rm) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha512_sha512h2(d, m, n)
}

function vector_crypto_sha512_sha512h2_decode__1 (Rd, Rn, opcode, O, Rm) = {
    __unconditional = true;
    if ~(HaveSHA512Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha512_sha512h2(d, m, n)
}

val vector_crypto_sha3op_sha256sched1 : forall 'd 'm 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha256sched1 (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let operand1 : bits(128) = V(d);
    let operand2 : bits(128) = V(n);
    let operand3 : bits(128) = V(m);
    result : bits(128) = undefined : bits(128);
    let T0 : bits(128) = slice(operand3, 0, 32) @ slice(operand2, 32, 96);
    T1 : bits(64) = undefined : bits(64);
    elt : bits(32) = undefined : bits(32);
    T1 = slice(operand3, 64, 64);
    foreach (e from 0 to 1 by 1 in inc) {
        elt = aget_Elem(T1, e, 32);
        elt = (ROR(elt, 17) ^ ROR(elt, 19)) ^ LSR(elt, 10);
        elt = elt + aget_Elem(operand1, e, 32) + aget_Elem(T0, e, 32);
        result = aset_Elem(result, e, 32, elt)
    };
    let T1 = slice(result, 0, 64);
    foreach (e from 2 to 3 by 1 in inc) {
        elt = aget_Elem(T1, e - 2, 32);
        elt = (ROR(elt, 17) ^ ROR(elt, 19)) ^ LSR(elt, 10);
        elt = elt + aget_Elem(operand1, e, 32) + aget_Elem(T0, e, 32);
        result = aset_Elem(result, e, 32, elt)
    };
    V(d) = result
}

val vector_crypto_sha3op_sha256sched1_decode : (bits(5), bits(5), bits(3), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha256sched1_decode (Rd, Rn, opcode, Rm, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if ~(HaveSHA256Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha3op_sha256sched1(d, m, n)
}

val vector_crypto_sha3op_sha256hash : forall 'd 'm 'n ('part1 : Bool),
  ('d >= 0 & 'd <= 31 | not('part1)) & ('n >= 0 & 'n <= 31 | not('part1)) & ('m >= 0 & 'm <= 31 | not('part1)) & ('n >= 0 & 'n <= 31 | not(not('part1))) & ('d >= 0 & 'd <= 31 | not(not('part1))) & ('m >= 0 & 'm <= 31 | not(not('part1))).
  (int('d), int('m), int('n), bool('part1)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha256hash (d, m, n, part1) = {
    AArch64_CheckFPAdvSIMDEnabled();
    result : bits(128) = undefined : bits(128);
    if part1 then {
        result = SHA256hash(V(d), V(n), V(m), true)
    } else {
        result = SHA256hash(V(n), V(d), V(m), false)
    };
    V(d) = result
}

val vector_crypto_sha3op_sha256hash_decode : (bits(5), bits(5), bits(1), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha256hash_decode (Rd, Rn, P, Rm, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if ~(HaveSHA256Ext()) then {
        throw(Error_Undefined())
    };
    let part1 = P == 0b0;
    __PostDecode();
    vector_crypto_sha3op_sha256hash(d, m, n, part1)
}

val vector_crypto_sha3op_sha1sched0 : forall 'd 'm 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1sched0 (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let operand1 : bits(128) = V(d);
    let operand2 : bits(128) = V(n);
    let operand3 : bits(128) = V(m);
    result : bits(128) = undefined : bits(128);
    result = slice(operand2, 0, 64) @ slice(operand1, 64, 64);
    let result = (result ^ operand1) ^ operand3;
    V(d) = result
}

val vector_crypto_sha3op_sha1sched0_decode : (bits(5), bits(5), bits(3), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1sched0_decode (Rd, Rn, opcode, Rm, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if ~(HaveSHA1Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha3op_sha1sched0(d, m, n)
}

val vector_crypto_sha3op_sha1hash_parity : forall 'd 'm 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1hash_parity (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    X : bits(128) = V(d);
    Y : bits(32) = V(n);
    let W : bits(128) = V(m);
    t : bits(32) = undefined : bits(32);
    foreach (e from 0 to 3 by 1 in inc) {
        t = SHAparity(slice(X, 32, 32), slice(X, 64, 32), slice(X, 96, 32));
        Y = Y + ROL(slice(X, 0, 32), 5) + t + aget_Elem(W, e, 32);
        X = __SetSlice_bits(128, 32, X, 32, ROL(slice(X, 32, 32), 30));
        let __tc1 : bits(160) = ROL(Y @ X, 32);
        Y = slice(__tc1, 128, 32);
        X = slice(__tc1, 0, 128)
    };
    V(d) = X
}

val vector_crypto_sha3op_sha1hash_parity_decode : (bits(5), bits(5), bits(3), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1hash_parity_decode (Rd, Rn, opcode, Rm, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if ~(HaveSHA1Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha3op_sha1hash_parity(d, m, n)
}

val vector_crypto_sha3op_sha1hash_majority : forall 'd 'm 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1hash_majority (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    X : bits(128) = V(d);
    Y : bits(32) = V(n);
    let W : bits(128) = V(m);
    t : bits(32) = undefined : bits(32);
    foreach (e from 0 to 3 by 1 in inc) {
        t = SHAmajority(slice(X, 32, 32), slice(X, 64, 32), slice(X, 96, 32));
        Y = Y + ROL(slice(X, 0, 32), 5) + t + aget_Elem(W, e, 32);
        X = __SetSlice_bits(128, 32, X, 32, ROL(slice(X, 32, 32), 30));
        let __tc1 : bits(160) = ROL(Y @ X, 32);
        Y = slice(__tc1, 128, 32);
        X = slice(__tc1, 0, 128)
    };
    V(d) = X
}

val vector_crypto_sha3op_sha1hash_majority_decode : (bits(5), bits(5), bits(3), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1hash_majority_decode (Rd, Rn, opcode, Rm, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if ~(HaveSHA1Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha3op_sha1hash_majority(d, m, n)
}

val vector_crypto_sha3op_sha1hash_choose : forall 'd 'm 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1hash_choose (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    X : bits(128) = V(d);
    Y : bits(32) = V(n);
    let W : bits(128) = V(m);
    t : bits(32) = undefined : bits(32);
    foreach (e from 0 to 3 by 1 in inc) {
        t = SHAchoose(slice(X, 32, 32), slice(X, 64, 32), slice(X, 96, 32));
        Y = Y + ROL(slice(X, 0, 32), 5) + t + aget_Elem(W, e, 32);
        X = __SetSlice_bits(128, 32, X, 32, ROL(slice(X, 32, 32), 30));
        let __tc1 : bits(160) = ROL(Y @ X, 32);
        Y = slice(__tc1, 128, 32);
        X = slice(__tc1, 0, 128)
    };
    V(d) = X
}

val vector_crypto_sha3op_sha1hash_choose_decode : (bits(5), bits(5), bits(3), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3op_sha1hash_choose_decode (Rd, Rn, opcode, Rm, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if ~(HaveSHA1Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha3op_sha1hash_choose(d, m, n)
}

val vector_crypto_sha3_xar : forall 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), bits(6), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3_xar (d, imm6, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    let Vn : bits(128) = V(n);
    let tmp : bits(128) = Vn ^ Vm;
    V(d) = ROR(slice(tmp, 64, 64), UInt(imm6)) @ ROR(slice(tmp, 0, 64), UInt(imm6))
}

val vector_crypto_sha3_xar_decode : (bits(5), bits(5), bits(6), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3_xar_decode (Rd, Rn, imm6, Rm) = {
    __unconditional = true;
    if ~(HaveSHA3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha3_xar(d, imm6, m, n)
}

val vector_crypto_sha3_rax1 : forall 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3_rax1 (d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    let Vn : bits(128) = V(n);
    V(d) = Vn ^ (ROL(slice(Vm, 64, 64), 1) @ ROL(slice(Vm, 0, 64), 1))
}

val vector_crypto_sha3_rax1_decode__0 : (bits(5), bits(5), bits(2), bits(1), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sha3_rax1_decode__1 : (bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sha3_rax1_decode = {
  vector_crypto_sha3_rax1_decode__0,
  vector_crypto_sha3_rax1_decode__1
}

function vector_crypto_sha3_rax1_decode__0 (Rd, Rn, opcode, O, Rm) = {
    __unconditional = true;
    if ~(HaveSHA3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha3_rax1(d, m, n)
}

function vector_crypto_sha3_rax1_decode__1 (Rd, Rn, Rm) = {
    __unconditional = true;
    if ~(HaveSHA3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    __PostDecode();
    vector_crypto_sha3_rax1(d, m, n)
}

val vector_crypto_sha3_eor3 : forall 'a 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('a >= 0 & 'a <= 31) & ('d >= 0 & 'd <= 31).
  (int('a), int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3_eor3 (a, d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    let Vn : bits(128) = V(n);
    let Va : bits(128) = V(a);
    V(d) = (Vn ^ Vm) ^ Va
}

val vector_crypto_sha3_eor3_decode__0 : (bits(5), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sha3_eor3_decode__1 : (bits(5), bits(5), bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sha3_eor3_decode = {
  vector_crypto_sha3_eor3_decode__0,
  vector_crypto_sha3_eor3_decode__1
}

function vector_crypto_sha3_eor3_decode__0 (Rd, Rn, Ra, Rm) = {
    __unconditional = true;
    if ~(HaveSHA3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'a = UInt(Ra);
    __PostDecode();
    vector_crypto_sha3_eor3(a, d, m, n)
}

function vector_crypto_sha3_eor3_decode__1 (Rd, Rn, Ra, Rm, Op0) = {
    __unconditional = true;
    if ~(HaveSHA3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'a = UInt(Ra);
    __PostDecode();
    vector_crypto_sha3_eor3(a, d, m, n)
}

val vector_crypto_sha3_bcax : forall 'a 'd 'm 'n,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & ('a >= 0 & 'a <= 31) & ('d >= 0 & 'd <= 31).
  (int('a), int('d), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha3_bcax (a, d, m, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let Vm : bits(128) = V(m);
    let Vn : bits(128) = V(n);
    let Va : bits(128) = V(a);
    V(d) = Vn ^ (Vm & ~(Va))
}

val vector_crypto_sha3_bcax_decode__0 : (bits(5), bits(5), bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

val vector_crypto_sha3_bcax_decode__1 : (bits(5), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

overload vector_crypto_sha3_bcax_decode = {
  vector_crypto_sha3_bcax_decode__0,
  vector_crypto_sha3_bcax_decode__1
}

function vector_crypto_sha3_bcax_decode__0 (Rd, Rn, Ra, Rm, Op0) = {
    __unconditional = true;
    if ~(HaveSHA3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'a = UInt(Ra);
    __PostDecode();
    vector_crypto_sha3_bcax(a, d, m, n)
}

function vector_crypto_sha3_bcax_decode__1 (Rd, Rn, Ra, Rm) = {
    __unconditional = true;
    if ~(HaveSHA3Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'a = UInt(Ra);
    __PostDecode();
    vector_crypto_sha3_bcax(a, d, m, n)
}

val vector_crypto_sha2op_sha256sched0 : forall 'd 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31).
  (int('d), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha2op_sha256sched0 (d, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let operand1 : bits(128) = V(d);
    let operand2 : bits(128) = V(n);
    result : bits(128) = undefined : bits(128);
    let T : bits(128) = slice(operand2, 0, 32) @ slice(operand1, 32, 96);
    elt : bits(32) = undefined : bits(32);
    foreach (e from 0 to 3 by 1 in inc) {
        elt = aget_Elem(T, e, 32);
        elt = (ROR(elt, 7) ^ ROR(elt, 18)) ^ LSR(elt, 3);
        result = aset_Elem(result, e, 32, elt + aget_Elem(operand1, e, 32))
    };
    V(d) = result
}

val vector_crypto_sha2op_sha256sched0_decode : (bits(5), bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha2op_sha256sched0_decode (Rd, Rn, opcode, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if ~(HaveSHA256Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha2op_sha256sched0(d, n)
}

val vector_crypto_sha2op_sha1sched1 : forall 'd 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31).
  (int('d), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha2op_sha1sched1 (d, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let operand1 : bits(128) = V(d);
    let operand2 : bits(128) = V(n);
    result : bits(128) = undefined : bits(128);
    let T : bits(128) = operand1 ^ LSR(operand2, 32);
    result = __SetSlice_bits(128, 32, result, 0, ROL(slice(T, 0, 32), 1));
    result = __SetSlice_bits(128, 32, result, 32, ROL(slice(T, 32, 32), 1));
    result = __SetSlice_bits(128, 32, result, 64, ROL(slice(T, 64, 32), 1));
    let result = __SetSlice_bits(128, 32, result, 96, ROL(slice(T, 96, 32), 1) ^ ROL(slice(T, 0, 32), 2));
    V(d) = result
}

val vector_crypto_sha2op_sha1sched1_decode : (bits(5), bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha2op_sha1sched1_decode (Rd, Rn, opcode, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if ~(HaveSHA1Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha2op_sha1sched1(d, n)
}

val vector_crypto_sha2op_sha1hash : forall 'd 'n,
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha2op_sha1hash (d, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let operand : bits(32) = V(n);
    V(d) = ROL(operand, 30)
}

val vector_crypto_sha2op_sha1hash_decode : (bits(5), bits(5), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_sha2op_sha1hash_decode (Rd, Rn, opcode, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if ~(HaveSHA1Ext()) then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_crypto_sha2op_sha1hash(d, n)
}

val vector_crypto_aes_round : forall 'd ('decrypt : Bool) 'n,
  ('d >= 0 & 'd <= 31) & ('n >= 0 & 'n <= 31).
  (int('d), bool('decrypt), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_aes_round (d, decrypt, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let operand1 : bits(128) = V(d);
    let operand2 : bits(128) = V(n);
    result : bits(128) = undefined : bits(128);
    result = operand1 ^ operand2;
    if decrypt then {
        result = AESInvSubBytes(AESInvShiftRows(result))
    } else {
        result = AESSubBytes(AESShiftRows(result))
    };
    V(d) = result
}

val vector_crypto_aes_round_decode : (bits(5), bits(5), bits(1), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_aes_round_decode (Rd, Rn, D, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if ~(HaveAESExt()) then {
        throw(Error_Undefined())
    };
    let decrypt = D == 0b1;
    __PostDecode();
    vector_crypto_aes_round(d, decrypt, n)
}

val vector_crypto_aes_mix : forall 'd ('decrypt : Bool) 'n,
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), bool('decrypt), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_aes_mix (d, decrypt, n) = {
    AArch64_CheckFPAdvSIMDEnabled();
    let operand : bits(128) = V(n);
    result : bits(128) = undefined : bits(128);
    if decrypt then {
        result = AESInvMixColumns(operand)
    } else {
        result = AESMixColumns(operand)
    };
    V(d) = result
}

val vector_crypto_aes_mix_decode : (bits(5), bits(5), bits(1), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_crypto_aes_mix_decode (Rd, Rn, D, size) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if ~(HaveAESExt()) then {
        throw(Error_Undefined())
    };
    let decrypt = D == 0b1;
    __PostDecode();
    vector_crypto_aes_mix(d, decrypt, n)
}

val vector_transfer_vector_table : forall 'd 'datasize 'elements ('is_tbl : Bool) 'm 'n 'regs,
  'regs >= 0 & 'datasize >= 0 & (0 <= 'n & 'n <= 31 & 0 <= 'm & 'm <= 31 & 0 <= 'd & 'd <= 31).
  (int('d), int('datasize), int('elements), bool('is_tbl), int('m), int('n), int('regs)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_table (d, datasize, elements, is_tbl, m, n__arg, regs) = {
    n : range(0, 31) = n__arg;
    CheckFPAdvSIMDEnabled64();
    let indices : bits('datasize) = aget_V(m);
    table : bits(128 * 'regs) = Zeros();
    result : bits('datasize) = undefined : bits('datasize);
    index : int = undefined : int;
    foreach (i from 0 to (regs - 1) by 1 in inc) {
        table = __SetSlice_bits(128 * regs, 128, table, 128 * i, aget_V(n));
        n = (n + 1) % 32
    };
    result = if is_tbl then Zeros() else aget_V(d);
    foreach (i from 0 to (elements - 1) by 1 in inc) {
        assert(i >= 0 & (i + 1) * 8 <= datasize);
        let index = UInt(aget_Elem(indices, i, 8));
        if index < 16 * regs then {
            result = aset_Elem(result, i, 8, aget_Elem(table, index, 8))
        }
    };
    aset_V(d, result)
}

val vector_transfer_vector_table_decode : (bits(5), bits(5), bits(1), bits(2), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_table_decode (Rd, Rn, op, len, Rm, op2, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / 8;
    let 'regs = UInt(len) + 1;
    let is_tbl = op == 0b0;
    __PostDecode();
    vector_transfer_vector_table(d, datasize, elements, is_tbl, m, n, regs)
}

val vector_transfer_vector_permute_zip : forall 'd 'datasize 'esize 'm 'n 'pairs 'part,
  'datasize >= 0 & ('n >= 0 & 'n <= 31 & 'm >= 0 & 'm <= 31 & 'd >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('m), int('n), int('pairs), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_permute_zip (d, datasize, esize, m, n, pairs, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = aget_V(n);
    let operand2 : bits('datasize) = aget_V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let 'base : {'n, 'n == 'part * 'pairs. int('n)} = part * pairs;
    foreach (p from 0 to (pairs - 1) by 1 in inc) {
        assert(constraint(('base + 'loop_p >= 0 & 'esize >= 0 & ('base + 'loop_p + 1) * 'esize <= 'datasize)));
        result = aset_Elem(result, 2 * p + 0, esize, aget_Elem(operand1, base + p, esize));
        result = aset_Elem(result, 2 * p + 1, esize, aget_Elem(operand2, base + p, esize))
    };
    aset_V(d, result)
}

val vector_transfer_vector_permute_zip_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_permute_zip_decode (Rd, Rn, op, Rm, size, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'part = UInt(op);
    let 'pairs = elements / 2;
    __PostDecode();
    vector_transfer_vector_permute_zip(d, datasize, esize, m, n, pairs, part)
}

val vector_transfer_vector_permute_unzip : forall 'd 'datasize 'elements 'esize 'm 'n 'part,
  'datasize >= 0 & ('n >= 0 & 'n <= 31 & 'm >= 0 & 'm <= 31 & 'd >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_permute_unzip (d, datasize, elements, esize, m, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operandl : bits('datasize) = aget_V(n);
    let operandh : bits('datasize) = aget_V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let zipped : bits(2 * 'datasize) = operandh @ operandl;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        assert(constraint((2 * 'loop_e + 'part >= 0 & 'esize >= 0 & (2 * 'loop_e + 'part + 1) * 'esize <= 2 * 'datasize)));
        result = aset_Elem(result, e, esize, aget_Elem(zipped, 2 * e + part, esize))
    };
    aset_V(d, result)
}

val vector_transfer_vector_permute_unzip_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_permute_unzip_decode (Rd, Rn, op, Rm, size, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'part = UInt(op);
    __PostDecode();
    vector_transfer_vector_permute_unzip(d, datasize, elements, esize, m, n, part)
}

val vector_transfer_vector_permute_transpose : forall 'd 'datasize 'esize 'm 'n 'pairs 'part,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('m), int('n), int('pairs), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_permute_transpose (d, datasize, esize, m, n, pairs, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    foreach (p from 0 to (pairs - 1) by 1 in inc) {
        result = aset_Elem(result, 2 * p + 0, esize, aget_Elem(operand1, 2 * p + part, esize));
        result = aset_Elem(result, 2 * p + 1, esize, aget_Elem(operand2, 2 * p + part, esize))
    };
    V(d) = result
}

val vector_transfer_vector_permute_transpose_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_permute_transpose_decode (Rd, Rn, op, Rm, size, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'part = UInt(op);
    let 'pairs = elements / 2;
    __PostDecode();
    vector_transfer_vector_permute_transpose(d, datasize, esize, m, n, pairs, part)
}

val vector_transfer_vector_insert : forall 'd 'dst_index 'esize 'idxdsize 'n 'src_index,
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31) & ('idxdsize >= 0 & 'esize >= 0).
  (int('d), int('dst_index), int('esize), int('idxdsize), int('n), int('src_index)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_insert (d, dst_index, esize, idxdsize, n, src_index) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('idxdsize) = V(n);
    result : bits(128) = undefined : bits(128);
    result = V(d);
    let result = aset_Elem(result, dst_index, esize, aget_Elem(operand, src_index, esize));
    V(d) = result
}

val vector_transfer_vector_insert_decode : (bits(5), bits(5), bits(4), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_insert_decode (Rd, Rn, imm4, imm5, op, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'size = LowestSetBit(imm5);
    if size > 3 then {
        throw(Error_Undefined())
    };
    let 'dst_index = UInt(slice(imm5, size + 1, negate(size) + 4));
    let 'src_index = UInt(slice(imm4, size, negate(size) + 4));
    let 'idxdsize = if [imm4[3]] == 0b1 then 128 else 64;
    let 'esize = shl_int(8, size);
    assert(constraint(('_idxdsize >= 0 & '_esize >= 0)));
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_transfer_vector_insert(d, dst_index, esize, idxdsize, n, src_index)
}

val vector_transfer_vector_extract : forall 'd 'datasize 'm 'n 'position,
  ('m >= 0 & 'm <= 31) & ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 'datasize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('m), int('n), int('position)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_extract (d, datasize, m, n, position) = {
    CheckFPAdvSIMDEnabled64();
    let hi : bits('datasize) = V(m);
    let lo : bits('datasize) = V(n);
    let concat : bits(2 * 'datasize) = hi @ lo;
    V(d) = slice(concat, position, datasize)
}

val vector_transfer_vector_extract_decode : (bits(5), bits(5), bits(4), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_extract_decode (Rd, Rn, imm4, Rm, op2, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if Q == 0b0 & [imm4[3]] == 0b1 then {
        throw(Error_Undefined())
    };
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'position = shl_int(UInt(imm4), 3);
    __PostDecode();
    vector_transfer_vector_extract(d, datasize, m, n, position)
}

val vector_transfer_vector_cpydup_sisd : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'n,
  ('n >= 0 & 'n <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_cpydup_sisd (d, datasize, elements, esize, idxdsize, index, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('idxdsize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let element : bits('esize) = aget_Elem(operand, index, esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        result = aset_Elem(result, e, esize, element)
    };
    V(d) = result
}

val vector_transfer_vector_cpydup_sisd_decode : (bits(5), bits(5), bits(4), bits(5), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_cpydup_sisd_decode (Rd, Rn, imm4, imm5, op) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'size = LowestSetBit(imm5);
    if size > 3 then {
        throw(Error_Undefined())
    };
    let 'index = UInt(slice(imm5, size + 1, negate(size) + 4));
    let 'idxdsize = if [imm5[4]] == 0b1 then 128 else 64;
    let 'esize = shl_int(8, size);
    let 'datasize = esize;
    let 'elements = 1;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_esize >= 0));
    assert(constraint(('_idxdsize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_transfer_vector_cpydup_sisd(d, datasize, elements, esize, idxdsize, index, n)
}

val vector_transfer_vector_cpydup_simd_decode : (bits(5), bits(5), bits(4), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_vector_cpydup_simd_decode (Rd, Rn, imm4, imm5, op, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'size = LowestSetBit(imm5);
    if size > 3 then {
        throw(Error_Undefined())
    };
    let 'index = UInt(slice(imm5, size + 1, negate(size) + 4));
    let 'idxdsize = if [imm5[4]] == 0b1 then 128 else 64;
    if size == 3 & Q == 0b0 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, size);
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_datasize >= 0));
    assert(constraint(('_idxdsize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_transfer_vector_cpydup_sisd(d, datasize, elements, esize, idxdsize, index, n)
}

val vector_transfer_integer_move_unsigned : forall 'd 'datasize 'esize 'idxdsize 'index 'n,
  ('n >= 0 & 'n <= 31) & ('idxdsize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('idxdsize), int('index), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_move_unsigned (d, datasize, esize, idxdsize, index, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('idxdsize) = V(n);
    X(d) = ZeroExtend(aget_Elem(operand, index, esize), datasize)
}

val vector_transfer_integer_move_unsigned_decode : (bits(5), bits(5), bits(1), bits(1), bits(2), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_move_unsigned_decode (Rd, Rn, imm4_0_, imm4_1_, imm4_3_2_, imm5, op, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    size : int = undefined : int;
    match Q @ imm5 {
      [bitzero] @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ [bitone] => {
          size = 0
      },
      [bitzero] @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ [bitone] @ [bitzero] => {
          size = 1
      },
      [bitzero] @ _ : bits(1) @ _ : bits(1) @ [bitone] @ [bitzero] @ [bitzero] => {
          size = 2
      },
      [bitone] @ _ : bits(1) @ [bitone] @ [bitzero] @ [bitzero] @ [bitzero] => {
          size = 3
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'size = size;
    assert(constraint('size in {0, 1, 2, 3}));
    let 'idxdsize : {|128, 64|} = if [imm5[4]] == 0b1 then 128 else 64;
    let 'index = UInt(slice(imm5, size + 1, negate(size) + 4));
    let 'esize = shl_int(8, size);
    let 'datasize : {|64, 32|} = if Q == 0b1 then 64 else 32;
    __PostDecode();
    assert((index + 1) * esize <= idxdsize);
    vector_transfer_integer_move_unsigned(d, datasize, esize, idxdsize, index, n)
}

val vector_transfer_integer_move_signed : forall 'd 'datasize 'esize 'idxdsize 'index 'n,
  ('n >= 0 & 'n <= 31) & ('idxdsize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('idxdsize), int('index), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_move_signed (d, datasize, esize, idxdsize, index, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('idxdsize) = V(n);
    X(d) = SignExtend(aget_Elem(operand, index, esize), datasize)
}

val vector_transfer_integer_move_signed_decode : (bits(5), bits(5), bits(1), bits(1), bits(2), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_move_signed_decode (Rd, Rn, imm4_0_, imm4_1_, imm4_3_2_, imm5, op, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    size : int = undefined : int;
    match Q @ imm5 {
      _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ [bitone] => {
          size = 0
      },
      _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ [bitone] @ [bitzero] => {
          size = 1
      },
      [bitone] @ _ : bits(1) @ _ : bits(1) @ [bitone] @ [bitzero] @ [bitzero] => {
          size = 2
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'size = size;
    assert(constraint('size in {0, 1, 2}));
    let 'idxdsize : {|128, 64|} = if [imm5[4]] == 0b1 then 128 else 64;
    let 'index = UInt(slice(imm5, size + 1, negate(size) + 4));
    let 'esize = shl_int(8, size);
    let 'datasize : {|64, 32|} = if Q == 0b1 then 64 else 32;
    __PostDecode();
    assert((index + 1) * esize <= idxdsize);
    vector_transfer_integer_move_signed(d, datasize, esize, idxdsize, index, n)
}

val vector_transfer_integer_insert : forall 'd 'datasize 'esize 'index 'n,
  ('n >= 0 & 'n <= 31 & 'esize in {8, 16, 32, 64}) & ('d >= 0 & 'd <= 31) & 'datasize >= 0.
  (int('d), int('datasize), int('esize), int('index), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_insert (d, datasize, esize, index, n) = {
    CheckFPAdvSIMDEnabled64();
    let element : bits('esize) = X(n);
    result : bits('datasize) = undefined : bits('datasize);
    result = V(d);
    let result = aset_Elem(result, index, esize, element);
    V(d) = result
}

val vector_transfer_integer_insert_decode : (bits(5), bits(5), bits(4), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_insert_decode (Rd, Rn, imm4, imm5, op, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'size = LowestSetBit(imm5);
    if size > 3 then {
        throw(Error_Undefined())
    };
    let 'index = UInt(slice(imm5, size + 1, negate(size) + 4));
    let 'esize = shl_int(8, size);
    let 'datasize = 128;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_n >= 0 & '_n <= 31 & '_esize in {8, 16, 32, 64})));
    __PostDecode();
    vector_transfer_integer_insert(d, datasize, esize, index, n)
}

val vector_transfer_integer_dup : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31 & 'esize in {8, 16, 32, 64}) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_dup (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let element : bits('esize) = X(n);
    result : bits('datasize) = undefined : bits('datasize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        result = aset_Elem(result, e, esize, element)
    };
    V(d) = result
}

val vector_transfer_integer_dup_decode : (bits(5), bits(5), bits(4), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_transfer_integer_dup_decode (Rd, Rn, imm4, imm5, op, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'size = LowestSetBit(imm5);
    if size > 3 then {
        throw(Error_Undefined())
    };
    if size == 3 & Q == 0b0 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, size);
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_datasize >= 0));
    assert(constraint(('_n >= 0 & '_n <= 31 & '_esize in {8, 16, 32, 64})));
    __PostDecode();
    vector_transfer_integer_dup(d, datasize, elements, esize, n)
}

val vector_shift_right_sisd : forall ('accumulate : Bool) 'd 'datasize 'elements 'esize 'n ('round : Bool) 'shift ('unsigned : Bool),
  'datasize >= 0 & ('n >= 0 & 'n <= 31 & 'd >= 0 & 'd <= 31).
  (bool('accumulate), int('d), int('datasize), int('elements), int('esize), int('n), bool('round), int('shift), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_right_sisd (accumulate, d, datasize, elements, esize, n, round, shift, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = aget_V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let 'round_const = if round then shl_int(1, shift - 1) else 0;
    element : int = undefined : int;
    let operand2 : bits('datasize) = if accumulate then aget_V(d) else Zeros();
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        assert(constraint(('loop_e >= 0 & 'esize >= 0 & ('loop_e + 1) * 'esize <= 'datasize)));
        element = shr_int(asl_Int(aget_Elem(operand, e, esize), unsigned) + round_const, shift);
        result = aset_Elem(result, e, esize, aget_Elem(operand2, e, esize) + __GetSlice_int(esize, element, 0))
    };
    aset_V(d, result)
}

val vector_shift_right_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_right_sisd_decode (Rd, Rn, o0, o1, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if [immh[3]] != 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, 3);
    let 'datasize = esize;
    let 'elements = 1;
    let 'shift = esize * 2 - UInt(immh @ immb);
    let unsigned = U == 0b1;
    let round = o1 == 0b1;
    let accumulate = o0 == 0b1;
    __PostDecode();
    vector_shift_right_sisd(accumulate, d, datasize, elements, esize, n, round, shift, unsigned)
}

val vector_shift_right_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_right_simd_decode (Rd, Rn, o0, o1, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if ([immh[3]] @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'shift = esize * 2 - UInt(immh @ immb);
    let unsigned = U == 0b1;
    let round = o1 == 0b1;
    let accumulate = o0 == 0b1;
    __PostDecode();
    vector_shift_right_sisd(accumulate, d, datasize, elements, esize, n, round, shift, unsigned)
}

val vector_shift_rightnarrow_uniform_sisd : forall 'd 'datasize 'elements 'esize 'n 'part ('round : Bool) 'shift ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part), bool('round), int('shift), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_uniform_sisd (d, datasize, elements, esize, n, part, round, shift, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let 'round_const = if round then shl_int(1, shift - 1) else 0;
    element : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = shr_int(asl_Int(aget_Elem(operand, e, 2 * esize), unsigned) + round_const, shift);
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SatQ(element, esize, unsigned);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    Vpart(d, part) = result
}

val vector_shift_rightnarrow_uniform_sisd_decode : (bits(5), bits(5), bits(1), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_uniform_sisd_decode (Rd, Rn, op, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_Undefined())
    };
    if [immh[3]] == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = esize;
    let 'elements = 1;
    let 'part = 0;
    let 'shift = 2 * esize - UInt(immh @ immb);
    let round = op == 0b1;
    let unsigned = U == 0b1;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint((2 * '_esize >= 0 & 2 * '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_rightnarrow_uniform_sisd(d, datasize, elements, esize, n, part, round, shift, unsigned)
}

val vector_shift_rightnarrow_uniform_simd_decode : (bits(5), bits(5), bits(1), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_uniform_simd_decode (Rd, Rn, op, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if [immh[3]] == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let 'shift = 2 * esize - UInt(immh @ immb);
    let round = op == 0b1;
    let unsigned = U == 0b1;
    assert(constraint(('_d >= 0 & '_d <= 31 & '_part in {0, 1})));
    assert(constraint(2 * '_esize >= 0));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_rightnarrow_uniform_sisd(d, datasize, elements, esize, n, part, round, shift, unsigned)
}

val vector_shift_rightnarrow_nonuniform_sisd : forall 'd 'datasize 'elements 'esize 'n 'part ('round : Bool) 'shift,
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part), bool('round), int('shift)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_nonuniform_sisd (d, datasize, elements, esize, n, part, round, shift) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let 'round_const = if round then shl_int(1, shift - 1) else 0;
    element : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = shr_int(SInt(aget_Elem(operand, e, 2 * esize)) + round_const, shift);
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = UnsignedSatQ(element, esize);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    Vpart(d, part) = result
}

val vector_shift_rightnarrow_nonuniform_sisd_decode : (bits(5), bits(5), bits(1), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_nonuniform_sisd_decode (Rd, Rn, op, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_Undefined())
    };
    if [immh[3]] == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = esize;
    let 'elements = 1;
    let 'part = 0;
    let 'shift = 2 * esize - UInt(immh @ immb);
    let round = op == 0b1;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint((2 * '_esize >= 0 & 2 * '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_rightnarrow_nonuniform_sisd(d, datasize, elements, esize, n, part, round, shift)
}

val vector_shift_rightnarrow_nonuniform_simd_decode : (bits(5), bits(5), bits(1), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_nonuniform_simd_decode (Rd, Rn, op, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if [immh[3]] == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let 'shift = 2 * esize - UInt(immh @ immb);
    let round = op == 0b1;
    assert(constraint(('_d >= 0 & '_d <= 31 & '_part in {0, 1})));
    assert(constraint(2 * '_esize >= 0));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_rightnarrow_nonuniform_sisd(d, datasize, elements, esize, n, part, round, shift)
}

val vector_shift_rightnarrow_logical : forall 'd 'datasize 'elements 'esize 'n 'part ('round : Bool) 'shift,
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part), bool('round), int('shift)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_logical (d, datasize, elements, esize, n, part, round, shift) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let 'round_const = if round then shl_int(1, shift - 1) else 0;
    element : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = shr_int(UInt(aget_Elem(operand, e, 2 * esize)) + round_const, shift);
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, element, 0))
    };
    Vpart(d, part) = result
}

val vector_shift_rightnarrow_logical_decode : (bits(5), bits(5), bits(1), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightnarrow_logical_decode (Rd, Rn, op, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if [immh[3]] == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let 'shift = 2 * esize - UInt(immh @ immb);
    let round = op == 0b1;
    assert(constraint(('_d >= 0 & '_d <= 31 & '_part in {0, 1})));
    assert(constraint(2 * '_esize >= 0));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_rightnarrow_logical(d, datasize, elements, esize, n, part, round, shift)
}

val vector_shift_rightinsert_sisd : forall 'd 'datasize 'elements 'esize 'n 'shift,
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31) & ('shift >= 0 & 'esize >= 0) & 'datasize >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('n), int('shift)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightinsert_sisd (d, datasize, elements, esize, n, shift) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    let mask : bits('esize) = LSR(Ones(esize), shift);
    shifted : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        shifted = LSR(aget_Elem(operand, e, esize), shift);
        result = aset_Elem(result, e, esize, aget_Elem(operand2, e, esize) & ~(mask) | shifted)
    };
    V(d) = result
}

val vector_shift_rightinsert_sisd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightinsert_sisd_decode (Rd, Rn, opcode, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if [immh[3]] != 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, 3);
    let 'datasize = esize;
    let 'elements = 1;
    let 'shift = esize * 2 - UInt(immh @ immb);
    assert(constraint('_esize >= 0));
    assert(constraint(('_esize * 2 - '_shift >= 0 & '_esize >= 0)));
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_rightinsert_sisd(d, datasize, elements, esize, n, shift)
}

val vector_shift_rightinsert_simd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_rightinsert_simd_decode (Rd, Rn, opcode, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if ([immh[3]] @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'shift = esize * 2 - UInt(immh @ immb);
    assert(constraint('_datasize >= 0));
    assert(constraint(('_esize * 2 - '_shift >= 0 & '_esize >= 0)));
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_rightinsert_sisd(d, datasize, elements, esize, n, shift)
}

val vector_shift_left_sisd : forall 'd 'datasize 'elements 'esize 'n 'shift,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & 'shift >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('shift)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_left_sisd (d, datasize, elements, esize, n, shift) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        result = aset_Elem(result, e, esize, LSL(aget_Elem(operand, e, esize), shift))
    };
    V(d) = result
}

val vector_shift_left_sisd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_left_sisd_decode (Rd, Rn, opcode, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if [immh[3]] != 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, 3);
    let 'datasize = esize;
    let 'elements = 1;
    let 'shift = UInt(immh @ immb) - esize;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_shift - '_esize >= 0));
    assert(constraint(('_esize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_left_sisd(d, datasize, elements, esize, n, shift)
}

val vector_shift_left_simd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_left_simd_decode (Rd, Rn, opcode, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if ([immh[3]] @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'shift = UInt(immh @ immb) - esize;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_shift - '_esize >= 0));
    assert(constraint(('_datasize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_left_sisd(d, datasize, elements, esize, n, shift)
}

val vector_shift_leftsat_sisd : forall 'd 'datasize ('dst_unsigned : Bool) 'elements 'esize 'n 'shift ('src_unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), bool('dst_unsigned), int('elements), int('esize), int('n), int('shift), bool('src_unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftsat_sisd (d, datasize, dst_unsigned, elements, esize, n, shift, src_unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = shl_int(asl_Int(aget_Elem(operand, e, esize), src_unsigned), shift);
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SatQ(element, esize, dst_unsigned);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_shift_leftsat_sisd_decode : (bits(5), bits(5), bits(1), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftsat_sisd_decode (Rd, Rn, op, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = esize;
    let 'elements = 1;
    let 'shift = UInt(immh @ immb) - esize;
    src_unsigned : bool = undefined : bool;
    dst_unsigned : bool = undefined : bool;
    match op @ U {
      0b00 => {
          throw(Error_Undefined())
      },
      0b01 => {
          src_unsigned = false;
          dst_unsigned = true
      },
      0b10 => {
          src_unsigned = false;
          dst_unsigned = false
      },
      0b11 => {
          src_unsigned = true;
          dst_unsigned = true
      }
    };
    let dst_unsigned = dst_unsigned;
    let src_unsigned = src_unsigned;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_esize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_leftsat_sisd(d, datasize, dst_unsigned, elements, esize, n, shift, src_unsigned)
}

val vector_shift_leftsat_simd_decode : (bits(5), bits(5), bits(1), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftsat_simd_decode (Rd, Rn, op, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if ([immh[3]] @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'shift = UInt(immh @ immb) - esize;
    src_unsigned : bool = undefined : bool;
    dst_unsigned : bool = undefined : bool;
    match op @ U {
      0b00 => {
          throw(Error_Undefined())
      },
      0b01 => {
          src_unsigned = false;
          dst_unsigned = true
      },
      0b10 => {
          src_unsigned = false;
          dst_unsigned = false
      },
      0b11 => {
          src_unsigned = true;
          dst_unsigned = true
      }
    };
    let dst_unsigned = dst_unsigned;
    let src_unsigned = src_unsigned;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_datasize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_leftsat_sisd(d, datasize, dst_unsigned, elements, esize, n, shift, src_unsigned)
}

val vector_shift_leftlong : forall 'd 'datasize 'elements 'esize 'n 'part 'shift ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part), int('shift), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftlong (d, datasize, elements, esize, n, part, shift, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = Vpart(n, part);
    result : bits(2 * 'datasize) = undefined : bits('datasize * 2);
    element : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = shl_int(asl_Int(aget_Elem(operand, e, esize), unsigned), shift);
        result = aset_Elem(result, e, 2 * esize, __GetSlice_int(2 * esize, element, 0))
    };
    V(d) = result
}

val vector_shift_leftlong_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftlong_decode (Rd, Rn, opcode, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if [immh[3]] == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let 'shift = UInt(immh @ immb) - esize;
    let unsigned = U == 0b1;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_esize >= 0));
    assert(constraint(('_n >= 0 & '_n <= 31 & '_part in {0, 1})));
    __PostDecode();
    vector_shift_leftlong(d, datasize, elements, esize, n, part, shift, unsigned)
}

val vector_shift_leftinsert_sisd : forall 'd 'datasize 'elements 'esize 'n 'shift,
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31) & ('shift >= 0 & 'esize >= 0) & 'datasize >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('n), int('shift)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftinsert_sisd (d, datasize, elements, esize, n, shift) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    let mask : bits('esize) = LSL(Ones(esize), shift);
    shifted : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        shifted = LSL(aget_Elem(operand, e, esize), shift);
        result = aset_Elem(result, e, esize, aget_Elem(operand2, e, esize) & ~(mask) | shifted)
    };
    V(d) = result
}

val vector_shift_leftinsert_sisd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftinsert_sisd_decode (Rd, Rn, opcode, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if [immh[3]] != 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, 3);
    let 'datasize = esize;
    let 'elements = 1;
    let 'shift = UInt(immh @ immb) - esize;
    assert(constraint('_esize >= 0));
    assert(constraint(('_shift - '_esize >= 0 & '_esize >= 0)));
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_leftinsert_sisd(d, datasize, elements, esize, n, shift)
}

val vector_shift_leftinsert_simd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_leftinsert_simd_decode (Rd, Rn, opcode, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if ([immh[3]] @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, HighestSetBit(immh));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'shift = UInt(immh @ immb) - esize;
    assert(constraint('_datasize >= 0));
    assert(constraint(('_shift - '_esize >= 0 & '_esize >= 0)));
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_leftinsert_sisd(d, datasize, elements, esize, n, shift)
}

val vector_shift_conv_int_sisd : forall 'd 'datasize 'elements 'esize 'fracbits 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('fracbits), int('n), FPRounding, bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_conv_int_sisd (d, datasize, elements, esize, fracbits, n, rounding, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FixedToFP(element, fracbits, unsigned, FPCR, rounding))
    };
    V(d) = result
}

val vector_shift_conv_int_sisd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_conv_int_sisd_decode (Rd, Rn, opcode, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (immh & 0xE) == 0x0 | (immh & 0xE) == 0x2 & ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'esize = if (immh & 0x8) == 0x8 then 64 else if (immh & 0xC) == 0x4 then 32 else 16;
    let 'datasize = esize;
    let 'elements = 1;
    let 'fracbits = esize * 2 - UInt(immh @ immb);
    let unsigned = U == 0b1;
    let rounding = FPRoundingMode(FPCR);
    __PostDecode();
    vector_shift_conv_int_sisd(d, datasize, elements, esize, fracbits, n, rounding, unsigned)
}

val vector_shift_conv_int_simd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_conv_int_simd_decode (Rd, Rn, opcode, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if (immh & 0xE) == 0x0 | (immh & 0xE) == 0x2 & ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    if ([immh[3]] @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = if (immh & 0x8) == 0x8 then 64 else if (immh & 0xC) == 0x4 then 32 else 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'fracbits = esize * 2 - UInt(immh @ immb);
    let unsigned = U == 0b1;
    let rounding = FPRoundingMode(FPCR);
    __PostDecode();
    vector_shift_conv_int_sisd(d, datasize, elements, esize, fracbits, n, rounding, unsigned)
}

val vector_shift_conv_float_sisd : forall 'd 'datasize 'elements 'esize 'fracbits 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & 'fracbits >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('fracbits), int('n), FPRounding, bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_conv_float_sisd (d, datasize, elements, esize, fracbits, n, rounding, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPToFixed(element, fracbits, unsigned, FPCR, rounding))
    };
    V(d) = result
}

val vector_shift_conv_float_sisd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_conv_float_sisd_decode (Rd, Rn, opcode, immb, immh, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (immh & 0xE) == 0x0 | (immh & 0xE) == 0x2 & ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'esize = if (immh & 0x8) == 0x8 then 64 else if (immh & 0xC) == 0x4 then 32 else 16;
    let 'datasize = esize;
    let 'elements = 1;
    let 'fracbits = esize * 2 - UInt(immh @ immb);
    let unsigned = U == 0b1;
    let rounding = FPRounding_ZERO;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_esize * 2 - '_fracbits >= 0));
    assert(constraint(('_esize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_conv_float_sisd(d, datasize, elements, esize, fracbits, n, rounding, unsigned)
}

val vector_shift_conv_float_simd_decode : (bits(5), bits(5), bits(5), bits(3), bits(4), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_shift_conv_float_simd_decode (Rd, Rn, opcode, immb, immh, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if immh == 0x0 then {
        throw(Error_See("asimdimm"))
    };
    if (immh & 0xE) == 0x0 | (immh & 0xE) == 0x2 & ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    if ([immh[3]] @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = if (immh & 0x8) == 0x8 then 64 else if (immh & 0xC) == 0x4 then 32 else 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'fracbits = esize * 2 - UInt(immh @ immb);
    let unsigned = U == 0b1;
    let rounding = FPRounding_ZERO;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_esize * 2 - '_fracbits >= 0));
    assert(constraint(('_datasize >= 0 & '_esize >= 0)));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_shift_conv_float_sisd(d, datasize, elements, esize, fracbits, n, rounding, unsigned)
}

val vector_reduce_intmax : forall 'd 'datasize 'elements 'esize ('min : Bool) 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), bool('min), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_intmax (d, datasize, elements, esize, min, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    maxmin : int = undefined : int;
    element : int = undefined : int;
    maxmin = asl_Int(aget_Elem(operand, 0, esize), unsigned);
    foreach (e from 1 to (elements - 1) by 1 in inc) {
        element = asl_Int(aget_Elem(operand, e, esize), unsigned);
        maxmin = if min then min(maxmin, element) else max(maxmin, element)
    };
    V(d) = __GetSlice_int(esize, maxmin, 0)
}

val vector_reduce_intmax_decode : (bits(5), bits(5), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_intmax_decode (Rd, Rn, op, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b100 then {
        throw(Error_Undefined())
    };
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    let min = op == 0b1;
    __PostDecode();
    vector_reduce_intmax(d, datasize, elements, esize, min, n, unsigned)
}

val vector_reduce_fp16maxnm_sisd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16maxnm_sisd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}

val vector_reduce_fp16maxnm_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16maxnm_sisd_decode (Rd, Rn, opcode, sz, o1, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = if o1 == 0b1 then ReduceOp_FMINNUM else ReduceOp_FMAXNUM;
    __PostDecode();
    vector_reduce_fp16maxnm_sisd(d, datasize, esize, n, op)
}

val vector_reduce_fpmaxnm_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fpmaxnm_sisd_decode (Rd, Rn, opcode, sz, o1, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = if o1 == 0b1 then ReduceOp_FMINNUM else ReduceOp_FMAXNUM;
    __PostDecode();
    vector_reduce_fp16maxnm_sisd(d, datasize, esize, n, op)
}

val vector_reduce_fp16maxnm_simd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16maxnm_simd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}

val vector_reduce_fp16maxnm_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16maxnm_simd_decode (Rd, Rn, opcode, o1, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let op = if o1 == 0b1 then ReduceOp_FMINNUM else ReduceOp_FMAXNUM;
    __PostDecode();
    vector_reduce_fp16maxnm_simd(d, datasize, esize, n, op)
}

val vector_reduce_fpmaxnm_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fpmaxnm_simd_decode (Rd, Rn, opcode, sz, o1, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) != 0b01 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let op = if o1 == 0b1 then ReduceOp_FMINNUM else ReduceOp_FMAXNUM;
    __PostDecode();
    vector_reduce_fp16maxnm_simd(d, datasize, esize, n, op)
}

val vector_reduce_fp16max_sisd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16max_sisd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}

val vector_reduce_fp16max_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16max_sisd_decode (Rd, Rn, opcode, sz, o1, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = if o1 == 0b1 then ReduceOp_FMIN else ReduceOp_FMAX;
    __PostDecode();
    vector_reduce_fp16max_sisd(d, datasize, esize, n, op)
}

val vector_reduce_fpmax_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fpmax_sisd_decode (Rd, Rn, opcode, sz, o1, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = if o1 == 0b1 then ReduceOp_FMIN else ReduceOp_FMAX;
    __PostDecode();
    vector_reduce_fp16max_sisd(d, datasize, esize, n, op)
}

val vector_reduce_fp16max_simd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16max_simd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}

val vector_reduce_fp16max_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16max_simd_decode (Rd, Rn, opcode, o1, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let op = if o1 == 0b1 then ReduceOp_FMIN else ReduceOp_FMAX;
    __PostDecode();
    vector_reduce_fp16max_simd(d, datasize, esize, n, op)
}

val vector_reduce_fpmax_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fpmax_simd_decode (Rd, Rn, opcode, sz, o1, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) != 0b01 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let op = if o1 == 0b1 then ReduceOp_FMIN else ReduceOp_FMAX;
    __PostDecode();
    vector_reduce_fp16max_simd(d, datasize, esize, n, op)
}

val vector_reduce_fp16add_sisd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16add_sisd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}

val vector_reduce_fp16add_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fp16add_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = ReduceOp_FADD;
    __PostDecode();
    vector_reduce_fp16add_sisd(d, datasize, esize, n, op)
}

val vector_reduce_fpadd_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_fpadd_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = ReduceOp_FADD;
    __PostDecode();
    vector_reduce_fp16add_sisd(d, datasize, esize, n, op)
}

val vector_reduce_add_sisd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_add_sisd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}

val vector_reduce_add_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_add_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size != 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = ReduceOp_ADD;
    __PostDecode();
    vector_reduce_add_sisd(d, datasize, esize, n, op)
}

val vector_reduce_add_simd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_add_simd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}

val vector_reduce_add_simd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_add_simd_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b100 then {
        throw(Error_Undefined())
    };
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let op = ReduceOp_ADD;
    __PostDecode();
    vector_reduce_add_simd(d, datasize, esize, n, op)
}

val vector_reduce_addlong : forall 'd 'datasize 'elements 'esize 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_addlong (d, datasize, elements, esize, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    sum : int = undefined : int;
    sum = asl_Int(aget_Elem(operand, 0, esize), unsigned);
    foreach (e from 1 to (elements - 1) by 1 in inc) {
        sum = sum + asl_Int(aget_Elem(operand, e, esize), unsigned)
    };
    V(d) = __GetSlice_int(2 * esize, sum, 0)
}

val vector_reduce_addlong_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_reduce_addlong_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b100 then {
        throw(Error_Undefined())
    };
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_reduce_addlong(d, datasize, elements, esize, n, unsigned)
}

val vector_logical : forall 'datasize 'rd,
  'datasize >= 0 & ('rd >= 0 & 'rd <= 31).
  (int('datasize), bits('datasize), ImmediateOp, int('rd)) -> unit effect {escape, rreg, undef, wreg}

function vector_logical (datasize, imm, operation, rd) = {
    CheckFPAdvSIMDEnabled64();
    operand : bits('datasize) = undefined : bits('datasize);
    result : bits('datasize) = undefined : bits('datasize);
    match operation {
      ImmediateOp_MOVI => {
          result = imm
      },
      ImmediateOp_MVNI => {
          result = ~(imm)
      },
      ImmediateOp_ORR => {
          operand = V(rd);
          result = operand | imm
      },
      ImmediateOp_BIC => {
          operand = V(rd);
          result = operand & ~(imm)
      }
    };
    let result = result;
    V(rd) = result
}

val vector_logical_decode : (bits(5), bits(1), bits(1), bits(1), bits(1), bits(1), bits(1), bits(4), bits(1), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_logical_decode (Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q) = {
    __unconditional = true;
    let 'rd = UInt(Rd);
    let 'datasize = if Q == 0b1 then 128 else 64;
    imm : bits('datasize) = undefined : bits('datasize);
    imm64 : bits(64) = undefined : bits(64);
    operation : ImmediateOp = undefined : ImmediateOp;
    match cmode @ op {
      [bitzero] @ _ : bits(1) @ _ : bits(1) @ [bitzero] @ [bitzero] => {
          operation = ImmediateOp_MOVI
      },
      [bitzero] @ _ : bits(1) @ _ : bits(1) @ [bitzero] @ [bitone] => {
          operation = ImmediateOp_MVNI
      },
      [bitzero] @ _ : bits(1) @ _ : bits(1) @ [bitone] @ [bitzero] => {
          operation = ImmediateOp_ORR
      },
      [bitzero] @ _ : bits(1) @ _ : bits(1) @ [bitone] @ [bitone] => {
          operation = ImmediateOp_BIC
      },
      [bitone] @ [bitzero] @ _ : bits(1) @ [bitzero] @ [bitzero] => {
          operation = ImmediateOp_MOVI
      },
      [bitone] @ [bitzero] @ _ : bits(1) @ [bitzero] @ [bitone] => {
          operation = ImmediateOp_MVNI
      },
      [bitone] @ [bitzero] @ _ : bits(1) @ [bitone] @ [bitzero] => {
          operation = ImmediateOp_ORR
      },
      [bitone] @ [bitzero] @ _ : bits(1) @ [bitone] @ [bitone] => {
          operation = ImmediateOp_BIC
      },
      [bitone] @ [bitone] @ [bitzero] @ _ : bits(1) @ [bitzero] => {
          operation = ImmediateOp_MOVI
      },
      [bitone] @ [bitone] @ [bitzero] @ _ : bits(1) @ [bitone] => {
          operation = ImmediateOp_MVNI
      },
      [bitone] @ [bitone] @ [bitone] @ [bitzero] @ _ : bits(1) => {
          operation = ImmediateOp_MOVI
      },
      0b11110 => {
          operation = ImmediateOp_MOVI
      },
      0b11111 => {
          if Q == 0b0 then {
              throw(Error_Undefined())
          };
          operation = ImmediateOp_MOVI
      }
    };
    let operation = operation;
    let imm64 = AdvSIMDExpandImm(op, cmode, ((((((a @ b) @ c) @ d) @ e) @ f) @ g) @ h);
    let imm = replicate_bits(imm64, datasize / 64);
    __PostDecode();
    vector_logical(datasize, imm, operation, rd)
}

val vector_fp16_movi : forall 'datasize 'rd,
  'datasize >= 0 & ('rd >= 0 & 'rd <= 31).
  (int('datasize), bits('datasize), int('rd)) -> unit effect {escape, rreg, undef, wreg}

function vector_fp16_movi (datasize, imm, rd) = {
    CheckFPAdvSIMDEnabled64();
    V(rd) = imm
}

val vector_fp16_movi_decode : (bits(5), bits(1), bits(1), bits(1), bits(1), bits(1), bits(1), bits(4), bits(1), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_fp16_movi_decode (Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'rd = UInt(Rd);
    let 'datasize = if Q == 0b1 then 128 else 64;
    imm : bits('datasize) = undefined : bits('datasize);
    let imm8 = ((((((a @ b) @ c) @ d) @ e) @ f) @ g) @ h;
    let imm16 : bits(16) = ((([imm8[7]] @ ~([imm8[6]])) @ replicate_bits([imm8[6]], 2)) @ slice(imm8, 0, 6)) @ Zeros(6);
    let imm = replicate_bits(imm16, datasize / 16);
    __PostDecode();
    vector_fp16_movi(datasize, imm, rd)
}

val vector_arithmetic_unary_special_sqrtfp16 : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtfp16 (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPSqrt(element, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_unary_special_sqrt_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrt_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_sqrtfp16(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_sqrtfp16_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtfp16_decode (Rd, Rn, opcode, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_sqrtfp16(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_sqrtest_int : forall 'd 'datasize 'elements 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtest_int (d, datasize, elements, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits(32) = undefined : bits(32);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, 32);
        result = aset_Elem(result, e, 32, UnsignedRSqrtEstimate(element))
    };
    V(d) = result
}

val vector_arithmetic_unary_special_sqrtest_int_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtest_int_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = 32;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_sqrtest_int(d, datasize, elements, n)
}

val vector_arithmetic_unary_special_sqrtest_fp16_sisd : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtest_fp16_sisd (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPRSqrtEstimate(element, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_unary_special_sqrtest_fp16_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtest_fp16_sisd_decode (Rd, Rn, opcode, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_unary_special_sqrtest_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_sqrtest_fp16_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtest_fp16_simd_decode (Rd, Rn, opcode, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_sqrtest_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_sqrtest_float_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtest_float_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_unary_special_sqrtest_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_sqrtest_float_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_sqrtest_float_simd_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_sqrtest_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_recip_int : forall 'd 'datasize 'elements 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_recip_int (d, datasize, elements, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits(32) = undefined : bits(32);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, 32);
        result = aset_Elem(result, e, 32, UnsignedRecipEstimate(element))
    };
    V(d) = result
}

val vector_arithmetic_unary_special_recip_int_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_recip_int_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = 32;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_recip_int(d, datasize, elements, n)
}

val vector_arithmetic_unary_special_recip_fp16_sisd : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_recip_fp16_sisd (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPRecipEstimate(element, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_unary_special_recip_fp16_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_recip_fp16_sisd_decode (Rd, Rn, opcode, size_1_, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_unary_special_recip_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_recip_fp16_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_recip_fp16_simd_decode (Rd, Rn, opcode, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_recip_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_recip_float_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_recip_float_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_unary_special_recip_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_recip_float_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_recip_float_simd_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_special_recip_fp16_sisd(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_frecpxfp16 : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_frecpxfp16 (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPRecpX(element, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_unary_special_frecpx_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_frecpx_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_unary_special_frecpxfp16(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_special_frecpxfp16_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_special_frecpxfp16_decode (Rd, Rn, opcode, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_unary_special_frecpxfp16(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_shift : forall 'd 'datasize 'elements 'esize 'n 'part 'shift ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part), int('shift), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_shift (d, datasize, elements, esize, n, part, shift, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = Vpart(n, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = shl_int(asl_Int(aget_Elem(operand, e, esize), unsigned), shift);
        result = aset_Elem(result, e, 2 * esize, __GetSlice_int(2 * esize, element, 0))
    };
    V(d) = result
}

val vector_arithmetic_unary_shift_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_shift_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let 'shift = esize;
    let unsigned = false;
    __PostDecode();
    vector_arithmetic_unary_shift(d, datasize, elements, esize, n, part, shift, unsigned)
}

val vector_arithmetic_unary_rev : forall 'containers 'd 'datasize 'elements_per_container 'esize 'n,
  'datasize >= 0 & ('n >= 0 & 'n <= 31 & 'd >= 0 & 'd <= 31).
  (int('containers), int('d), int('datasize), int('elements_per_container), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_rev (containers, d, datasize, elements_per_container, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = aget_V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : int = 0;
    rev_element : int = undefined : int;
    foreach (c from 0 to (containers - 1) by 1 in inc) {
        rev_element = element + elements_per_container - 1;
        foreach (e from 0 to (elements_per_container - 1) by 1 in inc) {
            let 're = rev_element;
            let 'e = element;
            assert(constraint(('e >= 0 & 'esize >= 0 & ('e + 1) * 'esize <= 'datasize)));
            result = aset_Elem(result, re, esize, aget_Elem(operand, e, esize));
            element = element + 1;
            rev_element = rev_element - 1
        }
    };
    aset_V(d, result)
}

val vector_arithmetic_unary_rev_decode : (bits(5), bits(5), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_rev_decode (Rd, Rn, o0, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
    let op : bits(2) = o0 @ U;
    if UInt(op) + UInt(size) >= 3 then {
        throw(Error_Undefined())
    };
    container_size : int = undefined : int;
    match op {
      0b10 => {
          container_size = 16
      },
      0b01 => {
          container_size = 32
      },
      0b00 => {
          container_size = 64
      }
    };
    let 'container_size = container_size;
    assert(constraint('container_size in {16, 32, 64}));
    let 'containers : {'n, 'n == div('datasize, 'container_size). int('n)} = datasize / container_size;
    let 'elements_per_container : {'n, 'n == div('container_size, 'esize). int('n)} = container_size / esize;
    __PostDecode();
    vector_arithmetic_unary_rev(containers, d, datasize, elements_per_container, esize, n)
}

val vector_arithmetic_unary_rbit : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_rbit (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    rev : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        foreach (i from 0 to (esize - 1) by 1 in inc) {
            rev = __SetSlice_bits(esize, 1, rev, esize - 1 - i, [element[i]])
        };
        result = aset_Elem(result, e, esize, rev)
    };
    V(d) = result
}

val vector_arithmetic_unary_rbit_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_rbit_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 8;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / 8;
    __PostDecode();
    vector_arithmetic_unary_rbit(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_not : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_not (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, ~(element))
    };
    V(d) = result
}

val vector_arithmetic_unary_not_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_not_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 8;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / 8;
    __PostDecode();
    vector_arithmetic_unary_not(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_fp16_round : forall 'd 'datasize 'elements 'esize ('exact : Bool) 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), bool('exact), int('n), FPRounding) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_round (d, datasize, elements, esize, exact, n, rounding) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPRoundInt(element, FPCR, rounding, exact))
    };
    V(d) = result
}

val vector_arithmetic_unary_fp16_round_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_round_decode (Rd, Rn, o1, o2, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    exact : bool = false;
    rounding : FPRounding = undefined : FPRounding;
    match (U @ o1) @ o2 {
      [bitzero] @ _ : bits(1) @ _ : bits(1) => {
          rounding = FPDecodeRounding(o1 @ o2)
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
    let rounding = rounding;
    __PostDecode();
    vector_arithmetic_unary_fp16_round(d, datasize, elements, esize, exact, n, rounding)
}

val vector_arithmetic_unary_float_round_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_round_decode (Rd, Rn, o1, sz, o2, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    exact : bool = false;
    rounding : FPRounding = undefined : FPRounding;
    match (U @ o1) @ o2 {
      [bitzero] @ _ : bits(1) @ _ : bits(1) => {
          rounding = FPDecodeRounding(o1 @ o2)
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
    let rounding = rounding;
    __PostDecode();
    vector_arithmetic_unary_fp16_round(d, datasize, elements, esize, exact, n, rounding)
}

val vector_arithmetic_unary_fp16_conv_int_sisd : forall 'd 'datasize 'elements 'esize 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_int_sisd (d, datasize, elements, esize, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let rounding = FPRoundingMode(FPCR);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FixedToFP(element, 0, unsigned, FPCR, rounding))
    };
    V(d) = result
}

val vector_arithmetic_unary_fp16_conv_int_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_int_sisd_decode (Rd, Rn, opcode, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_int_sisd(d, datasize, elements, esize, n, unsigned)
}

val vector_arithmetic_unary_fp16_conv_int_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_int_simd_decode (Rd, Rn, opcode, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_int_sisd(d, datasize, elements, esize, n, unsigned)
}

val vector_arithmetic_unary_float_conv_int_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_conv_int_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_int_sisd(d, datasize, elements, esize, n, unsigned)
}

val vector_arithmetic_unary_float_conv_int_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_conv_int_simd_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_int_sisd(d, datasize, elements, esize, n, unsigned)
}

val vector_arithmetic_unary_fp16_conv_float_tieaway_sisd : forall 'd 'datasize 'elements 'esize 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), FPRounding, bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (d, datasize, elements, esize, n, rounding, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPToFixed(element, 0, unsigned, FPCR, rounding))
    };
    V(d) = result
}

val vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode (Rd, Rn, opcode, size_1_, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    let rounding = FPRounding_TIEAWAY;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode (Rd, Rn, opcode, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let rounding = FPRounding_TIEAWAY;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    let rounding = FPRounding_TIEAWAY;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_float_conv_float_tieaway_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_conv_float_tieaway_simd_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let rounding = FPRounding_TIEAWAY;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_fp16_conv_float_bulk_sisd : forall 'd 'datasize 'elements 'esize 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), FPRounding, bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_float_bulk_sisd (d, datasize, elements, esize, n, rounding, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPToFixed(element, 0, unsigned, FPCR, rounding))
    };
    V(d) = result
}

val vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode (Rd, Rn, o1, o2, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    let rounding = FPDecodeRounding(o1 @ o2);
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode (Rd, Rn, o1, o2, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let rounding = FPDecodeRounding(o1 @ o2);
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_float_conv_float_bulk_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_conv_float_bulk_sisd_decode (Rd, Rn, o1, sz, o2, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    let rounding = FPDecodeRounding(o1 @ o2);
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_float_conv_float_bulk_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_conv_float_bulk_simd_decode (Rd, Rn, o1, sz, o2, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let rounding = FPDecodeRounding(o1 @ o2);
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd(d, datasize, elements, esize, n, rounding, unsigned)
}

val vector_arithmetic_unary_float_xtn_sisd : forall 'd 'datasize 'elements 'esize 'n 'part,
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_xtn_sisd (d, datasize, elements, esize, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        result = aset_Elem(result, e, esize, FPConvert(aget_Elem(operand, e, 2 * esize), FPCR, FPRounding_ODD))
    };
    Vpart(d, part) = result
}

val vector_arithmetic_unary_float_xtn_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_xtn_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if sz == 0b0 then {
        throw(Error_Undefined())
    };
    let 'esize = 32;
    let 'datasize = esize;
    let 'elements = 1;
    let 'part = 0;
    __PostDecode();
    vector_arithmetic_unary_float_xtn_sisd(d, datasize, elements, esize, n, part)
}

val vector_arithmetic_unary_float_xtn_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_xtn_simd_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if sz == 0b0 then {
        throw(Error_Undefined())
    };
    let 'esize = 32;
    let 'datasize = 64;
    let 'elements = 2;
    let 'part = UInt(Q);
    __PostDecode();
    vector_arithmetic_unary_float_xtn_sisd(d, datasize, elements, esize, n, part)
}

val vector_arithmetic_unary_float_widen : forall 'd 'datasize 'elements 'esize 'n 'part,
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_widen (d, datasize, elements, esize, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = Vpart(n, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        result = aset_Elem(result, e, 2 * esize, FPConvert(aget_Elem(operand, e, esize), FPCR))
    };
    V(d) = result
}

val vector_arithmetic_unary_float_widen_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_widen_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(16, UInt(sz));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    assert(constraint(('_d >= 0 & '_d <= 31)));
    assert(constraint('_esize >= 0));
    assert(constraint(('_n >= 0 & '_n <= 31 & '_part in {0, 1})));
    __PostDecode();
    vector_arithmetic_unary_float_widen(d, datasize, elements, esize, n, part)
}

val vector_arithmetic_unary_float_round_frint_32_64 : forall 'd 'datasize 'elements 'esize 'intsize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & 'intsize in {32, 64} & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('intsize), int('n), FPRounding) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_round_frint_32_64 (d, datasize, elements, esize, intsize, n, rounding) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPRoundIntN(element, FPCR, rounding, intsize))
    };
    V(d) = result
}

val vector_arithmetic_unary_float_round_frint_32_64_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_round_frint_32_64_decode (Rd, Rn, op, sz, U, Q) = {
    __unconditional = true;
    if ~(HaveFrintExt()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let 'intsize = if op == 0b0 then 32 else 64;
    let rounding = if U == 0b0 then FPRounding_ZERO else FPRoundingMode(FPCR);
    __PostDecode();
    vector_arithmetic_unary_float_round_frint_32_64(d, datasize, elements, esize, intsize, n, rounding)
}

val vector_arithmetic_unary_float_narrow : forall 'd 'datasize 'elements 'esize 'n 'part,
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_narrow (d, datasize, elements, esize, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        result = aset_Elem(result, e, esize, FPConvert(aget_Elem(operand, e, 2 * esize), FPCR))
    };
    Vpart(d, part) = result
}

val vector_arithmetic_unary_float_narrow_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_float_narrow_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(16, UInt(sz));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    assert(constraint(('_d >= 0 & '_d <= 31 & '_part in {0, 1})));
    assert(constraint(2 * '_esize >= 0));
    assert(constraint(('_n >= 0 & '_n <= 31)));
    __PostDecode();
    vector_arithmetic_unary_float_narrow(d, datasize, elements, esize, n, part)
}

val vector_arithmetic_unary_extract_sqxtun_sisd : forall 'd 'datasize 'elements 'esize 'n 'part,
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_sqxtun_sisd (d, datasize, elements, esize, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, 2 * esize);
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = UnsignedSatQ(SInt(element), esize);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    Vpart(d, part) = result
}

val vector_arithmetic_unary_extract_sqxtun_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_sqxtun_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'part = 0;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_unary_extract_sqxtun_sisd(d, datasize, elements, esize, n, part)
}

val vector_arithmetic_unary_extract_sqxtun_simd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_sqxtun_simd_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_extract_sqxtun_sisd(d, datasize, elements, esize, n, part)
}

val vector_arithmetic_unary_extract_sat_sisd : forall 'd 'datasize 'elements 'esize 'n 'part ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_sat_sisd (d, datasize, elements, esize, n, part, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, 2 * esize);
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SatQ(asl_Int(element, unsigned), esize, unsigned);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    Vpart(d, part) = result
}

val vector_arithmetic_unary_extract_sat_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_sat_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'part = 0;
    let 'elements = 1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_extract_sat_sisd(d, datasize, elements, esize, n, part, unsigned)
}

val vector_arithmetic_unary_extract_sat_simd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_sat_simd_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_extract_sat_sisd(d, datasize, elements, esize, n, part, unsigned)
}

val vector_arithmetic_unary_extract_nosat : forall 'd 'datasize 'elements 'esize 'n 'part,
  ('n >= 0 & 'n <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_nosat (d, datasize, elements, esize, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits(2 * 'datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, 2 * esize);
        result = aset_Elem(result, e, esize, slice(element, 0, esize))
    };
    Vpart(d, part) = result
}

val vector_arithmetic_unary_extract_nosat_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_extract_nosat_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_unary_extract_nosat(d, datasize, elements, esize, n, part)
}

val vector_arithmetic_unary_diffneg_sat_sisd : forall 'd 'datasize 'elements 'esize 'n ('neg : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), bool('neg)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_sat_sisd (d, datasize, elements, esize, n, neg) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = SInt(aget_Elem(operand, e, esize));
        if neg then {
            element = negate(element)
        } else {
            element = abs(element)
        };
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SignedSatQ(element, esize);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_unary_diffneg_sat_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_sat_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let neg = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_diffneg_sat_sisd(d, datasize, elements, esize, n, neg)
}

val vector_arithmetic_unary_diffneg_sat_simd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_sat_simd_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let neg = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_diffneg_sat_sisd(d, datasize, elements, esize, n, neg)
}

val vector_arithmetic_unary_diffneg_int_sisd : forall 'd 'datasize 'elements 'esize 'n ('neg : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), bool('neg)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_int_sisd (d, datasize, elements, esize, n, neg) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = SInt(aget_Elem(operand, e, esize));
        if neg then {
            element = negate(element)
        } else {
            element = abs(element)
        };
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, element, 0))
    };
    V(d) = result
}

val vector_arithmetic_unary_diffneg_int_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_int_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size != 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let neg = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_diffneg_int_sisd(d, datasize, elements, esize, n, neg)
}

val vector_arithmetic_unary_diffneg_int_simd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_int_simd_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let neg = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_diffneg_int_sisd(d, datasize, elements, esize, n, neg)
}

val vector_arithmetic_unary_diffneg_fp16 : forall 'd 'datasize 'elements 'esize 'n ('neg : Bool),
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n), bool('neg)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_fp16 (d, datasize, elements, esize, n, neg) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        if neg then {
            element = FPNeg(element)
        } else {
            element = FPAbs(element)
        };
        result = aset_Elem(result, e, esize, element)
    };
    V(d) = result
}

val vector_arithmetic_unary_diffneg_fp16_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_fp16_decode (Rd, Rn, opcode, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let neg = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_diffneg_fp16(d, datasize, elements, esize, n, neg)
}

val vector_arithmetic_unary_diffneg_float_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_diffneg_float_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let neg = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_diffneg_fp16(d, datasize, elements, esize, n, neg)
}

val vector_arithmetic_unary_cnt : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cnt (d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    count : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        count = BitCount(aget_Elem(operand, e, esize));
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, count, 0))
    };
    V(d) = result
}

val vector_arithmetic_unary_cnt_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cnt_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size != 0b00 then {
        throw(Error_Undefined())
    };
    let 'esize = 8;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / 8;
    __PostDecode();
    vector_arithmetic_unary_cnt(d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_int_lessthan_sisd : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (CompareOp, int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_int_lessthan_sisd (comparison, d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : int = undefined : int;
    test_passed : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = SInt(aget_Elem(operand, e, esize));
        match comparison {
          CompareOp_GT => {
              test_passed = element > 0
          },
          CompareOp_GE => {
              test_passed = element >= 0
          },
          CompareOp_EQ => {
              test_passed = element == 0
          },
          CompareOp_LE => {
              test_passed = element <= 0
          },
          CompareOp_LT => {
              test_passed = element < 0
          }
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones() else Zeros())
    };
    V(d) = result
}

val vector_arithmetic_unary_cmp_int_lessthan_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_int_lessthan_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size != 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let comparison = CompareOp_LT;
    __PostDecode();
    vector_arithmetic_unary_cmp_int_lessthan_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_int_lessthan_simd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_int_lessthan_simd_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let comparison = CompareOp_LT;
    __PostDecode();
    vector_arithmetic_unary_cmp_int_lessthan_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_int_bulk_sisd : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (CompareOp, int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_int_bulk_sisd (comparison, d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    element : int = undefined : int;
    test_passed : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = SInt(aget_Elem(operand, e, esize));
        match comparison {
          CompareOp_GT => {
              test_passed = element > 0
          },
          CompareOp_GE => {
              test_passed = element >= 0
          },
          CompareOp_EQ => {
              test_passed = element == 0
          },
          CompareOp_LE => {
              test_passed = element <= 0
          },
          CompareOp_LT => {
              test_passed = element < 0
          }
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones() else Zeros())
    };
    V(d) = result
}

val vector_arithmetic_unary_cmp_int_bulk_sisd_decode : (bits(5), bits(5), bits(1), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_int_bulk_sisd_decode (Rd, Rn, op, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size != 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    comparison : CompareOp = undefined : CompareOp;
    match op @ U {
      0b00 => {
          comparison = CompareOp_GT
      },
      0b01 => {
          comparison = CompareOp_GE
      },
      0b10 => {
          comparison = CompareOp_EQ
      },
      0b11 => {
          comparison = CompareOp_LE
      }
    };
    let comparison = comparison;
    __PostDecode();
    vector_arithmetic_unary_cmp_int_bulk_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_int_bulk_simd_decode : (bits(5), bits(5), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_int_bulk_simd_decode (Rd, Rn, op, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    comparison : CompareOp = undefined : CompareOp;
    match op @ U {
      0b00 => {
          comparison = CompareOp_GT
      },
      0b01 => {
          comparison = CompareOp_GE
      },
      0b10 => {
          comparison = CompareOp_EQ
      },
      0b11 => {
          comparison = CompareOp_LE
      }
    };
    let comparison = comparison;
    __PostDecode();
    vector_arithmetic_unary_cmp_int_bulk_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_fp16_lessthan_sisd : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (CompareOp, int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_fp16_lessthan_sisd (comparison, d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let zero : bits('esize) = FPZero(0b0);
    element : bits('esize) = undefined : bits('esize);
    test_passed : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        match comparison {
          CompareOp_GT => {
              test_passed = FPCompareGT(element, zero, FPCR)
          },
          CompareOp_GE => {
              test_passed = FPCompareGE(element, zero, FPCR)
          },
          CompareOp_EQ => {
              test_passed = FPCompareEQ(element, zero, FPCR)
          },
          CompareOp_LE => {
              test_passed = FPCompareGE(zero, element, FPCR)
          },
          CompareOp_LT => {
              test_passed = FPCompareGT(zero, element, FPCR)
          }
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones() else Zeros())
    };
    V(d) = result
}

val vector_arithmetic_unary_cmp_fp16_lessthan_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_fp16_lessthan_sisd_decode (Rd, Rn, opcode, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    let comparison = CompareOp_LT;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_lessthan_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_fp16_lessthan_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_fp16_lessthan_simd_decode (Rd, Rn, opcode, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let comparison = CompareOp_LT;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_lessthan_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_float_lessthan_sisd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_float_lessthan_sisd_decode (Rd, Rn, opcode, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    let comparison = CompareOp_LT;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_lessthan_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_float_lessthan_simd_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_float_lessthan_simd_decode (Rd, Rn, opcode, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let comparison = CompareOp_LT;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_lessthan_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_fp16_bulk_sisd : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (CompareOp, int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_fp16_bulk_sisd (comparison, d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let zero : bits('esize) = FPZero(0b0);
    element : bits('esize) = undefined : bits('esize);
    test_passed : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        match comparison {
          CompareOp_GT => {
              test_passed = FPCompareGT(element, zero, FPCR)
          },
          CompareOp_GE => {
              test_passed = FPCompareGE(element, zero, FPCR)
          },
          CompareOp_EQ => {
              test_passed = FPCompareEQ(element, zero, FPCR)
          },
          CompareOp_LE => {
              test_passed = FPCompareGE(zero, element, FPCR)
          },
          CompareOp_LT => {
              test_passed = FPCompareGT(zero, element, FPCR)
          }
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones() else Zeros())
    };
    V(d) = result
}

val vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode (Rd, Rn, op, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    comparison : CompareOp = undefined : CompareOp;
    match op @ U {
      0b00 => {
          comparison = CompareOp_GT
      },
      0b01 => {
          comparison = CompareOp_GE
      },
      0b10 => {
          comparison = CompareOp_EQ
      },
      0b11 => {
          comparison = CompareOp_LE
      }
    };
    let comparison = comparison;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_bulk_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_fp16_bulk_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_fp16_bulk_simd_decode (Rd, Rn, op, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    comparison : CompareOp = undefined : CompareOp;
    match op @ U {
      0b00 => {
          comparison = CompareOp_GT
      },
      0b01 => {
          comparison = CompareOp_GE
      },
      0b10 => {
          comparison = CompareOp_EQ
      },
      0b11 => {
          comparison = CompareOp_LE
      }
    };
    let comparison = comparison;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_bulk_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_float_bulk_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_float_bulk_sisd_decode (Rd, Rn, op, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    comparison : CompareOp = undefined : CompareOp;
    match op @ U {
      0b00 => {
          comparison = CompareOp_GT
      },
      0b01 => {
          comparison = CompareOp_GE
      },
      0b10 => {
          comparison = CompareOp_EQ
      },
      0b11 => {
          comparison = CompareOp_LE
      }
    };
    let comparison = comparison;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_bulk_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_cmp_float_bulk_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_cmp_float_bulk_simd_decode (Rd, Rn, op, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    comparison : CompareOp = undefined : CompareOp;
    match op @ U {
      0b00 => {
          comparison = CompareOp_GT
      },
      0b01 => {
          comparison = CompareOp_GE
      },
      0b10 => {
          comparison = CompareOp_EQ
      },
      0b11 => {
          comparison = CompareOp_LE
      }
    };
    let comparison = comparison;
    __PostDecode();
    vector_arithmetic_unary_cmp_fp16_bulk_sisd(comparison, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_clsz : forall 'd 'datasize 'elements 'esize 'n,
  ('n >= 0 & 'n <= 31) & ('datasize >= 0 & 'esize >= 0) & 'esize >= 1 & ('d >= 0 & 'd <= 31).
  (CountOp, int('d), int('datasize), int('elements), int('esize), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_clsz (countop, d, datasize, elements, esize, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    count : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if countop == CountOp_CLS then {
            count = CountLeadingSignBits(aget_Elem(operand, e, esize))
        } else {
            count = CountLeadingZeroBits(aget_Elem(operand, e, esize))
        };
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, count, 0))
    };
    V(d) = result
}

val vector_arithmetic_unary_clsz_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_clsz_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let countop = if U == 0b1 then CountOp_CLZ else CountOp_CLS;
    __PostDecode();
    vector_arithmetic_unary_clsz(countop, d, datasize, elements, esize, n)
}

val vector_arithmetic_unary_add_saturating_sisd : forall 'd 'datasize 'elements 'esize 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_add_saturating_sisd (d, datasize, elements, esize, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    let operand2 : bits('datasize) = V(d);
    op1 : int = undefined : int;
    op2 : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        op1 = asl_Int(aget_Elem(operand, e, esize), ~(unsigned));
        op2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SatQ(op1 + op2, esize, unsigned);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_unary_add_saturating_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_add_saturating_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_add_saturating_sisd(d, datasize, elements, esize, n, unsigned)
}

val vector_arithmetic_unary_add_saturating_simd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_add_saturating_simd_decode (Rd, Rn, opcode, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_add_saturating_sisd(d, datasize, elements, esize, n, unsigned)
}

val vector_arithmetic_unary_add_pairwise : forall ('acc : Bool) 'd 'datasize 'elements 'esize 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('d >= 0 & 'd <= 31 | not('acc)) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (bool('acc), int('d), int('datasize), int('elements), int('esize), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_add_pairwise (acc, d, datasize, elements, esize, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    result : bits('datasize) = undefined : bits('datasize);
    sum : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    op1 : int = undefined : int;
    op2 : int = undefined : int;
    result = if acc then V(d) else Zeros();
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        op1 = asl_Int(aget_Elem(operand, 2 * e + 0, esize), unsigned);
        op2 = asl_Int(aget_Elem(operand, 2 * e + 1, esize), unsigned);
        sum = __GetSlice_int(2 * esize, op1 + op2, 0);
        result = aset_Elem(result, e, 2 * esize, aget_Elem(result, e, 2 * esize) + sum)
    };
    V(d) = result
}

val vector_arithmetic_unary_add_pairwise_decode : (bits(5), bits(5), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_unary_add_pairwise_decode (Rd, Rn, op, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / (2 * esize);
    let acc = op == 0b1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_unary_add_pairwise(acc, d, datasize, elements, esize, n, unsigned)
}

val vector_arithmetic_binary_uniform_sub_saturating_sisd : forall 'd 'datasize 'elements 'esize 'm 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_saturating_sisd (d, datasize, elements, esize, m, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    diff : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        diff = element1 - element2;
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SatQ(diff, esize, unsigned);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_sub_saturating_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_saturating_sisd_decode (Rd, Rn, opcode, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_sub_saturating_sisd(d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_sub_saturating_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_saturating_simd_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_sub_saturating_sisd(d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_sub_int : forall 'd 'datasize 'elements 'esize 'm 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_int (d, datasize, elements, esize, m, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    diff : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        diff = element1 - element2;
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, diff, 1))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_sub_int_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_int_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_sub_int(d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_sub_fp16_sisd : forall ('abs : Bool) 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (bool('abs), int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_fp16_sisd (abs, d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    diff : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        diff = FPSub(element1, element2, FPCR);
        result = aset_Elem(result, e, esize, if abs then FPAbs(diff) else diff)
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_sub_fp16_sisd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_fp16_sisd_decode (Rd, Rn, opcode, Rm, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    let abs = true;
    __PostDecode();
    vector_arithmetic_binary_uniform_sub_fp16_sisd(abs, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_sub_fp16_simd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_fp16_simd_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let abs = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_sub_fp16_sisd(abs, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_sub_fp_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_fp_sisd_decode (Rd, Rn, opcode, Rm, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    let abs = true;
    __PostDecode();
    vector_arithmetic_binary_uniform_sub_fp16_sisd(abs, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_sub_fp_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_sub_fp_simd_decode (Rd, Rn, opcode, Rm, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let abs = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_sub_fp16_sisd(abs, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_shift_sisd : forall 'd 'datasize 'elements 'esize 'm 'n ('rounding : Bool) ('saturating : Bool) ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('rounding), bool('saturating), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_shift_sisd (d, datasize, elements, esize, m, n, rounding, saturating, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    round_const : int = 0;
    shift : int = undefined : int;
    element : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        shift = SInt(slice(aget_Elem(operand2, e, esize), 0, 8));
        if rounding then {
            round_const = shl_int(1, negate(shift) - 1)
        };
        element = shl_int(asl_Int(aget_Elem(operand1, e, esize), unsigned) + round_const, shift);
        if saturating then {
            __tc1 : bits('esize) = undefined : bits('esize);
            (__tc1, sat) = SatQ(element, esize, unsigned);
            result = aset_Elem(result, e, esize, __tc1);
            if sat then {
                FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
            }
        } else {
            result = aset_Elem(result, e, esize, __GetSlice_int(esize, element, 0))
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_shift_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_shift_sisd_decode (Rd, Rn, S, R, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let unsigned = U == 0b1;
    let rounding = R == 0b1;
    let saturating = S == 0b1;
    if S == 0b0 & size != 0b11 then {
        throw(Error_Undefined())
    };
    __PostDecode();
    vector_arithmetic_binary_uniform_shift_sisd(d, datasize, elements, esize, m, n, rounding, saturating, unsigned)
}

val vector_arithmetic_binary_uniform_shift_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_shift_simd_decode (Rd, Rn, S, R, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    let rounding = R == 0b1;
    let saturating = S == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_shift_sisd(d, datasize, elements, esize, m, n, rounding, saturating, unsigned)
}

val vector_arithmetic_binary_uniform_rsqrtsfp16_sisd : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_rsqrtsfp16_sisd (d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        result = aset_Elem(result, e, esize, FPRSqrtStepFused(element1, element2))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_rsqrts_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_rsqrts_sisd_decode (Rd, Rn, opcode, Rm, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_binary_uniform_rsqrtsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_rsqrts_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_rsqrts_simd_decode (Rd, Rn, opcode, Rm, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_rsqrtsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_rsqrtsfp16_sisd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_rsqrtsfp16_sisd_decode (Rd, Rn, opcode, Rm, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_binary_uniform_rsqrtsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_rsqrtsfp16_simd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_rsqrtsfp16_simd_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_rsqrtsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_recpsfp16_sisd : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_recpsfp16_sisd (d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        result = aset_Elem(result, e, esize, FPRecipStepFused(element1, element2))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_recps_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_recps_sisd_decode (Rd, Rn, opcode, Rm, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_binary_uniform_recpsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_recps_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_recps_simd_decode (Rd, Rn, opcode, Rm, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_recpsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_recpsfp16_sisd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_recpsfp16_sisd_decode (Rd, Rn, opcode, Rm, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_binary_uniform_recpsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_recpsfp16_simd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_recpsfp16_simd_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_recpsfp16_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_mul_int_product : forall 'd 'datasize 'elements 'esize 'm 'n ('poly : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('poly)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_product (d, datasize, elements, esize, m, n, poly) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    product : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if poly then {
            product = slice(PolynomialMult(element1, element2), 0, esize)
        } else {
            product = __GetSlice_int(esize, UInt(element1) * UInt(element2), 0)
        };
        result = aset_Elem(result, e, esize, product)
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_int_product_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_product_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if U == 0b1 & size != 0b00 then {
        throw(Error_Undefined())
    };
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let poly = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_product(d, datasize, elements, esize, m, n, poly)
}

val vector_arithmetic_binary_uniform_mul_int_doubling_sisd : forall 'd 'datasize 'elements 'esize 'm 'n ('rounding : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('rounding)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_doubling_sisd (d, datasize, elements, esize, m, n, rounding) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let 'round_const = if rounding then shl_int(1, esize - 1) else 0;
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        element2 = SInt(aget_Elem(operand2, e, esize));
        product = 2 * element1 * element2 + round_const;
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SignedSatQ(shr_int(product, esize), esize);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode (Rd, Rn, opcode, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 | size == 0b00 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let rounding = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_doubling_sisd(d, datasize, elements, esize, m, n, rounding)
}

val vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 | size == 0b00 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let rounding = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_doubling_sisd(d, datasize, elements, esize, m, n, rounding)
}

val vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd : forall 'd 'datasize 'elements 'esize 'm 'n ('rounding : Bool) ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('rounding), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd (d, datasize, elements, esize, m, n, rounding, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    let 'rounding_const = if rounding then shl_int(1, esize - 1) else 0;
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    element3 : int = undefined : int;
    let 'product = undefined : int;
    sat : bool = undefined : bool;
    accum : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        element2 = SInt(aget_Elem(operand2, e, esize));
        element3 = SInt(aget_Elem(operand3, e, esize));
        if sub_op then {
            accum = shl_int(element3, esize) - 2 * (element1 * element2) + rounding_const
        } else {
            accum = shl_int(element3, esize) + 2 * (element1 * element2) + rounding_const
        };
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SignedSatQ(shr_int(accum, esize), esize);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode (Rd, Rn, S, Rm, size, U) = {
    __unconditional = true;
    if ~(HaveQRDMLAHExt()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 | size == 0b00 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let rounding = true;
    let sub_op = S == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd(d, datasize, elements, esize, m, n, rounding, sub_op)
}

val vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode (Rd, Rn, S, Rm, size, U, Q) = {
    __unconditional = true;
    if ~(HaveQRDMLAHExt()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 | size == 0b00 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let rounding = true;
    let sub_op = S == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd(d, datasize, elements, esize, m, n, rounding, sub_op)
}

val vector_arithmetic_binary_uniform_mul_int_dotp : forall 'd 'datasize 'elements 'esize 'm 'n ('signed : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & div('esize, 4) >= 0 | not('signed)) & ('datasize >= 0 & div('esize, 4) >= 0 | not(not('signed))).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('signed)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_dotp (d, datasize, elements, esize, m, n, signed) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    result = V(d);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        res : int = 0;
        element1 : int = undefined : int;
        element2 : int = undefined : int;
        foreach (i from 0 to 3 by 1 in inc) {
            if signed then {
                element1 = SInt(aget_Elem(operand1, 4 * e + i, esize / 4));
                element2 = SInt(aget_Elem(operand2, 4 * e + i, esize / 4))
            } else {
                element1 = UInt(aget_Elem(operand1, 4 * e + i, esize / 4));
                element2 = UInt(aget_Elem(operand2, 4 * e + i, esize / 4))
            };
            res = res + element1 * element2
        };
        result = aset_Elem(result, e, esize, aget_Elem(result, e, esize) + res)
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_int_dotp_decode__0 : (bits(5), bits(5), bits(4), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

val vector_arithmetic_binary_uniform_mul_int_dotp_decode__1 : (bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

overload vector_arithmetic_binary_uniform_mul_int_dotp_decode = {
  vector_arithmetic_binary_uniform_mul_int_dotp_decode__0,
  vector_arithmetic_binary_uniform_mul_int_dotp_decode__1
}

function vector_arithmetic_binary_uniform_mul_int_dotp_decode__0 (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    if ~(HaveDOTPExt()) then {
        throw(Error_Undefined())
    };
    if size != 0b10 then {
        throw(Error_Undefined())
    };
    let signed = U == 0b0;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_dotp(d, datasize, elements, esize, m, n, signed)
}

function vector_arithmetic_binary_uniform_mul_int_dotp_decode__1 (Rd, Rn, Rm, size, U, Q) = {
    __unconditional = true;
    if ~(HaveDOTPExt()) then {
        throw(Error_Undefined())
    };
    if size != 0b10 then {
        throw(Error_Undefined())
    };
    let signed = U == 0b0;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_dotp(d, datasize, elements, esize, m, n, signed)
}

val vector_arithmetic_binary_uniform_mul_int_accum : forall 'd 'datasize 'elements 'esize 'm 'n ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_accum (d, datasize, elements, esize, m, n, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    product : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        product = __GetSlice_int(esize, UInt(element1) * UInt(element2), 0);
        if sub_op then {
            result = aset_Elem(result, e, esize, aget_Elem(operand3, e, esize) - product)
        } else {
            result = aset_Elem(result, e, esize, aget_Elem(operand3, e, esize) + product)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_int_accum_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_int_accum_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_int_accum(d, datasize, elements, esize, m, n, sub_op)
}

val vector_arithmetic_binary_uniform_mul_fp16_product : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp16_product (d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        result = aset_Elem(result, e, esize, FPMul(element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_fp16_product_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp16_product_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_product(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_mul_fp_product_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_product_decode (Rd, Rn, opcode, Rm, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_product(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_mul_fp16_fused : forall 'd 'datasize 'elements 'esize 'm 'n ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp16_fused (d, datasize, elements, esize, m, n, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if sub_op then {
            element1 = FPNeg(element1)
        };
        result = aset_Elem(result, e, esize, FPMulAdd(aget_Elem(operand3, e, esize), element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_fp16_fused_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp16_fused_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = a == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_fused(d, datasize, elements, esize, m, n, sub_op)
}

val vector_arithmetic_binary_uniform_mul_fp_fused_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_fused_decode (Rd, Rn, opcode, Rm, sz, op, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = op == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_fused(d, datasize, elements, esize, m, n, sub_op)
}

val vector_arithmetic_binary_uniform_mul_fp16_extended_sisd : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp16_extended_sisd (d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        result = aset_Elem(result, e, esize, FPMulX(element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_decode (Rd, Rn, opcode, Rm, a, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_extended_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_mul_fp16_extended_simd_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp16_extended_simd_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_extended_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_mul_fp_extended_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_extended_sisd_decode (Rd, Rn, opcode, Rm, sz, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_extended_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_mul_fp_extended_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_extended_simd_decode (Rd, Rn, opcode, Rm, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp16_extended_sisd(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('sub_op : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & (div('datasize, 2) >= 0 & div('esize, 2) >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper (d, datasize, elements, esize, m, n, part, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits(div('datasize, 2)) = Vpart(n, part);
    let operand2 : bits(div('datasize, 2)) = Vpart(m, part);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits(div('esize, 2)) = undefined : bits(div('esize, 2));
    element2 : bits(div('esize, 2)) = undefined : bits(div('esize, 2));
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize / 2);
        element2 = aget_Elem(operand2, e, esize / 2);
        if sub_op then {
            element1 = FPNeg(element1)
        };
        result = aset_Elem(result, e, esize, FPMulAddH(aget_Elem(operand3, e, esize), element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper_decode (Rd, Rn, Rm, sz, S, Q) = {
    __unconditional = true;
    if ~(HaveFP16MulNoRoundingToFP32Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = 32;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = S == 0b1;
    let 'part = 1;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper(d, datasize, elements, esize, m, n, part, sub_op)
}

val vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('sub_op : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & (div('datasize, 2) >= 0 & div('esize, 2) >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower (d, datasize, elements, esize, m, n, part, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits(div('datasize, 2)) = Vpart(n, part);
    let operand2 : bits(div('datasize, 2)) = Vpart(m, part);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits(div('esize, 2)) = undefined : bits(div('esize, 2));
    element2 : bits(div('esize, 2)) = undefined : bits(div('esize, 2));
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize / 2);
        element2 = aget_Elem(operand2, e, esize / 2);
        if sub_op then {
            element1 = FPNeg(element1)
        };
        result = aset_Elem(result, e, esize, FPMulAddH(aget_Elem(operand3, e, esize), element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower_decode : (bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower_decode (Rd, Rn, Rm, sz, S, Q) = {
    __unconditional = true;
    if ~(HaveFP16MulNoRoundingToFP32Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'esize = 32;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = S == 0b1;
    let 'part = 0;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower(d, datasize, elements, esize, m, n, part, sub_op)
}

val vector_arithmetic_binary_uniform_mul_fp_complex : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_complex (d, datasize, elements, esize, m, n, rot) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    element3 : bits('esize) = undefined : bits('esize);
    element4 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements / 2 - 1) by 1 in inc) {
        match rot {
          0b00 => {
              element1 = aget_Elem(operand2, e * 2, esize);
              element2 = aget_Elem(operand1, e * 2, esize);
              element3 = aget_Elem(operand2, e * 2 + 1, esize);
              element4 = aget_Elem(operand1, e * 2, esize)
          },
          0b01 => {
              element1 = FPNeg(aget_Elem(operand2, e * 2 + 1, esize));
              element2 = aget_Elem(operand1, e * 2 + 1, esize);
              element3 = aget_Elem(operand2, e * 2, esize);
              element4 = aget_Elem(operand1, e * 2 + 1, esize)
          },
          0b10 => {
              element1 = FPNeg(aget_Elem(operand2, e * 2, esize));
              element2 = aget_Elem(operand1, e * 2, esize);
              element3 = FPNeg(aget_Elem(operand2, e * 2 + 1, esize));
              element4 = aget_Elem(operand1, e * 2, esize)
          },
          0b11 => {
              element1 = aget_Elem(operand2, e * 2 + 1, esize);
              element2 = aget_Elem(operand1, e * 2 + 1, esize);
              element3 = FPNeg(aget_Elem(operand2, e * 2, esize));
              element4 = aget_Elem(operand1, e * 2 + 1, esize)
          }
        };
        result = aset_Elem(result, e * 2, esize, FPMulAdd(aget_Elem(operand3, e * 2, esize), element2, element1, FPCR));
        result = aset_Elem(result, e * 2 + 1, esize, FPMulAdd(aget_Elem(operand3, e * 2 + 1, esize), element4, element3, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_mul_fp_complex_decode : (bits(5), bits(5), bits(2), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_mul_fp_complex_decode (Rd, Rn, rot, Rm, size, U, Q) = {
    __unconditional = true;
    if ~(HaveFCADDExt()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b00 then {
        throw(Error_Undefined())
    };
    if Q == 0b0 & size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    if ~(HaveFP16Ext()) & esize == 16 then {
        throw(Error_Undefined())
    };
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_mul_fp_complex(d, datasize, elements, esize, m, n, rot)
}

val vector_arithmetic_binary_uniform_maxmin_single : forall 'd 'datasize 'elements 'esize 'm ('minimum : Bool) 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), bool('minimum), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_single (d, datasize, elements, esize, m, minimum, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    maxmin : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        maxmin = if minimum then min(element1, element2) else max(element1, element2);
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, maxmin, 0))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_maxmin_single_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_single_decode (Rd, Rn, o1, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    let minimum = o1 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_maxmin_single(d, datasize, elements, esize, m, minimum, n, unsigned)
}

val vector_arithmetic_binary_uniform_maxmin_pair : forall 'd 'datasize 'elements 'esize 'm ('minimum : Bool) 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & (2 * 'datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), bool('minimum), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_pair (d, datasize, elements, esize, m, minimum, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    maxmin : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(concat, 2 * e, esize), unsigned);
        element2 = asl_Int(aget_Elem(concat, 2 * e + 1, esize), unsigned);
        maxmin = if minimum then min(element1, element2) else max(element1, element2);
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, maxmin, 0))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_maxmin_pair_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_pair_decode (Rd, Rn, o1, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    let minimum = o1 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_maxmin_pair(d, datasize, elements, esize, m, minimum, n, unsigned)
}

val vector_arithmetic_binary_uniform_maxmin_fp16_2008 : forall 'd 'datasize 'elements 'esize 'm ('minimum : Bool) 'n ('pair : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & (2 * 'datasize >= 0 & 'esize >= 0 | not('pair)) & ('datasize >= 0 & 'esize >= 0 | not(not('pair))) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), bool('minimum), int('n), bool('pair)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_fp16_2008 (d, datasize, elements, esize, m, minimum, n, pair) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if pair then {
            element1 = aget_Elem(concat, 2 * e, esize);
            element2 = aget_Elem(concat, 2 * e + 1, esize)
        } else {
            element1 = aget_Elem(operand1, e, esize);
            element2 = aget_Elem(operand2, e, esize)
        };
        if minimum then {
            result = aset_Elem(result, e, esize, FPMinNum(element1, element2, FPCR))
        } else {
            result = aset_Elem(result, e, esize, FPMaxNum(element1, element2, FPCR))
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode (Rd, Rn, Op3, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let pair = U == 0b1;
    let minimum = a == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_maxmin_fp16_2008(d, datasize, elements, esize, m, minimum, n, pair)
}

val vector_arithmetic_binary_uniform_maxmin_fp_2008_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_fp_2008_decode (Rd, Rn, opcode, Rm, sz, o1, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let pair = U == 0b1;
    let minimum = o1 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_maxmin_fp16_2008(d, datasize, elements, esize, m, minimum, n, pair)
}

val vector_arithmetic_binary_uniform_maxmin_fp16_1985 : forall 'd 'datasize 'elements 'esize 'm ('minimum : Bool) 'n ('pair : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & (2 * 'datasize >= 0 & 'esize >= 0 | not('pair)) & ('datasize >= 0 & 'esize >= 0 | not(not('pair))) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), bool('minimum), int('n), bool('pair)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_fp16_1985 (d, datasize, elements, esize, m, minimum, n, pair) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if pair then {
            element1 = aget_Elem(concat, 2 * e, esize);
            element2 = aget_Elem(concat, 2 * e + 1, esize)
        } else {
            element1 = aget_Elem(operand1, e, esize);
            element2 = aget_Elem(operand2, e, esize)
        };
        if minimum then {
            result = aset_Elem(result, e, esize, FPMin(element1, element2, FPCR))
        } else {
            result = aset_Elem(result, e, esize, FPMax(element1, element2, FPCR))
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode (Rd, Rn, opcode, Rm, o1, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let pair = U == 0b1;
    let minimum = o1 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_maxmin_fp16_1985(d, datasize, elements, esize, m, minimum, n, pair)
}

val vector_arithmetic_binary_uniform_maxmin_fp_1985_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_maxmin_fp_1985_decode (Rd, Rn, opcode, Rm, sz, o1, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let pair = U == 0b1;
    let minimum = o1 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_maxmin_fp16_1985(d, datasize, elements, esize, m, minimum, n, pair)
}

val vector_arithmetic_binary_uniform_logical_bsleor : forall 'd 'datasize 'm 'n,
  'datasize >= 0 & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('m), int('n), VBitOp) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_logical_bsleor (d, datasize, m, n, op) = {
    CheckFPAdvSIMDEnabled64();
    operand1 : bits('datasize) = undefined : bits('datasize);
    operand2 : bits('datasize) = undefined : bits('datasize);
    operand3 : bits('datasize) = undefined : bits('datasize);
    let operand4 : bits('datasize) = V(n);
    match op {
      VBitOp_VEOR => {
          operand1 = V(m);
          operand2 = Zeros();
          operand3 = Ones()
      },
      VBitOp_VBSL => {
          operand1 = V(m);
          operand2 = operand1;
          operand3 = V(d)
      },
      VBitOp_VBIT => {
          operand1 = V(d);
          operand2 = operand1;
          operand3 = V(m)
      },
      VBitOp_VBIF => {
          operand1 = V(d);
          operand2 = operand1;
          operand3 = ~(V(m))
      }
    };
    let operand3 = operand3;
    let operand2 = operand2;
    let operand1 = operand1;
    V(d) = operand1 ^ (operand2 ^ operand4 & operand3)
}

val vector_arithmetic_binary_uniform_logical_bsleor_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_logical_bsleor_decode (Rd, Rn, opcode, Rm, opc2, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 8;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    op : VBitOp = undefined : VBitOp;
    match opc2 {
      0b00 => {
          op = VBitOp_VEOR
      },
      0b01 => {
          op = VBitOp_VBSL
      },
      0b10 => {
          op = VBitOp_VBIT
      },
      0b11 => {
          op = VBitOp_VBIF
      }
    };
    let op = op;
    __PostDecode();
    vector_arithmetic_binary_uniform_logical_bsleor(d, datasize, m, n, op)
}

val vector_arithmetic_binary_uniform_logical_andorr : forall 'd 'datasize ('invert : Bool) 'm 'n,
  'datasize >= 0 & ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), bool('invert), int('m), int('n), LogicalOp) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_logical_andorr (d, datasize, invert, m, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    if invert then {
        operand2 = ~(operand2)
    };
    match op {
      LogicalOp_AND => {
          result = operand1 & operand2
      },
      LogicalOp_ORR => {
          result = operand1 | operand2
      }
    };
    let result = result;
    V(d) = result
}

val vector_arithmetic_binary_uniform_logical_andorr_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_logical_andorr_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 8;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let invert = [size[0]] == 0b1;
    let op = if [size[1]] == 0b1 then LogicalOp_ORR else LogicalOp_AND;
    __PostDecode();
    vector_arithmetic_binary_uniform_logical_andorr(d, datasize, invert, m, n, op)
}

val vector_arithmetic_binary_uniform_divfp16 : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_divfp16 (d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        result = aset_Elem(result, e, esize, FPDiv(element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_div_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_div_decode (Rd, Rn, opcode, Rm, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_divfp16(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_divfp16_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_divfp16_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_divfp16(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_diff : forall ('accumulate : Bool) 'd 'datasize 'elements 'esize 'm 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31 | not('accumulate)) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (bool('accumulate), int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_diff (accumulate, d, datasize, elements, esize, m, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    absdiff : bits('esize) = undefined : bits('esize);
    result = if accumulate then V(d) else Zeros();
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        absdiff = __GetSlice_int(esize, abs(element1 - element2), 0);
        result = aset_Elem(result, e, esize, aget_Elem(result, e, esize) + absdiff)
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_diff_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_diff_decode (Rd, Rn, ac, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    let accumulate = ac == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_diff(accumulate, d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_cmp_int_sisd : forall ('cmp_eq : Bool) 'd 'datasize 'elements 'esize 'm 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (bool('cmp_eq), int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_int_sisd (cmp_eq, d, datasize, elements, esize, m, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    test_passed : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        test_passed = if cmp_eq then element1 >= element2 else element1 > element2;
        result = aset_Elem(result, e, esize, if test_passed then Ones() else Zeros())
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_cmp_int_sisd_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_int_sisd_decode (Rd, Rn, eq, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size != 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let unsigned = U == 0b1;
    let cmp_eq = eq == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_int_sisd(cmp_eq, d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_cmp_int_simd_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_int_simd_decode (Rd, Rn, eq, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    let cmp_eq = eq == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_int_sisd(cmp_eq, d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_cmp_fp16_sisd : forall ('abs : Bool) 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (bool('abs), CompareOp, int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_fp16_sisd (abs, cmp, d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    test_passed : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if abs then {
            element1 = FPAbs(element1);
            element2 = FPAbs(element2)
        };
        match cmp {
          CompareOp_EQ => {
              test_passed = FPCompareEQ(element1, element2, FPCR)
          },
          CompareOp_GE => {
              test_passed = FPCompareGE(element1, element2, FPCR)
          },
          CompareOp_GT => {
              test_passed = FPCompareGT(element1, element2, FPCR)
          }
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones() else Zeros())
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode : (bits(5), bits(5), bits(1), bits(5), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode (Rd, Rn, ac, Rm, E, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    cmp : CompareOp = undefined : CompareOp;
    abs : bool = undefined : bool;
    match (E @ U) @ ac {
      0b000 => {
          cmp = CompareOp_EQ;
          abs = false
      },
      0b010 => {
          cmp = CompareOp_GE;
          abs = false
      },
      0b011 => {
          cmp = CompareOp_GE;
          abs = true
      },
      0b110 => {
          cmp = CompareOp_GT;
          abs = false
      },
      0b111 => {
          cmp = CompareOp_GT;
          abs = true
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let abs = abs;
    let cmp = cmp;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_fp16_sisd(abs, cmp, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_cmp_fp16_simd_decode : (bits(5), bits(5), bits(1), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_fp16_simd_decode (Rd, Rn, ac, Rm, E, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    cmp : CompareOp = undefined : CompareOp;
    abs : bool = undefined : bool;
    match (E @ U) @ ac {
      0b000 => {
          cmp = CompareOp_EQ;
          abs = false
      },
      0b010 => {
          cmp = CompareOp_GE;
          abs = false
      },
      0b011 => {
          cmp = CompareOp_GE;
          abs = true
      },
      0b110 => {
          cmp = CompareOp_GT;
          abs = false
      },
      0b111 => {
          cmp = CompareOp_GT;
          abs = true
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let abs = abs;
    let cmp = cmp;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_fp16_sisd(abs, cmp, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_cmp_fp_sisd_decode : (bits(5), bits(5), bits(1), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_fp_sisd_decode (Rd, Rn, ac, Rm, sz, E, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    cmp : CompareOp = undefined : CompareOp;
    abs : bool = undefined : bool;
    match (E @ U) @ ac {
      0b000 => {
          cmp = CompareOp_EQ;
          abs = false
      },
      0b010 => {
          cmp = CompareOp_GE;
          abs = false
      },
      0b011 => {
          cmp = CompareOp_GE;
          abs = true
      },
      0b110 => {
          cmp = CompareOp_GT;
          abs = false
      },
      0b111 => {
          cmp = CompareOp_GT;
          abs = true
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let abs = abs;
    let cmp = cmp;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_fp16_sisd(abs, cmp, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_cmp_fp_simd_decode : (bits(5), bits(5), bits(1), bits(5), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_fp_simd_decode (Rd, Rn, ac, Rm, sz, E, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    cmp : CompareOp = undefined : CompareOp;
    abs : bool = undefined : bool;
    match (E @ U) @ ac {
      0b000 => {
          cmp = CompareOp_EQ;
          abs = false
      },
      0b010 => {
          cmp = CompareOp_GE;
          abs = false
      },
      0b011 => {
          cmp = CompareOp_GE;
          abs = true
      },
      0b110 => {
          cmp = CompareOp_GT;
          abs = false
      },
      0b111 => {
          cmp = CompareOp_GT;
          abs = true
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let abs = abs;
    let cmp = cmp;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_fp16_sisd(abs, cmp, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_cmp_bitwise_sisd : forall ('and_test : Bool) 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (bool('and_test), int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_bitwise_sisd (and_test, d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    test_passed : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if and_test then {
            test_passed = ~(IsZero(element1 & element2))
        } else {
            test_passed = element1 == element2
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones() else Zeros())
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode (Rd, Rn, opcode, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size != 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let and_test = U == 0b0;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_bitwise_sisd(and_test, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let and_test = U == 0b0;
    __PostDecode();
    vector_arithmetic_binary_uniform_cmp_bitwise_sisd(and_test, d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_add_wrapping_single_sisd : forall 'd 'datasize 'elements 'esize 'm 'n ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_wrapping_single_sisd (d, datasize, elements, esize, m, n, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if sub_op then {
            result = aset_Elem(result, e, esize, element1 - element2)
        } else {
            result = aset_Elem(result, e, esize, element1 + element2)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode (Rd, Rn, opcode, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size != 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let sub_op = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_wrapping_single_sisd(d, datasize, elements, esize, m, n, sub_op)
}

val vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_wrapping_single_sisd(d, datasize, elements, esize, m, n, sub_op)
}

val vector_arithmetic_binary_uniform_add_wrapping_pair : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & (2 * 'datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_wrapping_pair (d, datasize, elements, esize, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(concat, 2 * e, esize);
        element2 = aget_Elem(concat, 2 * e + 1, esize);
        result = aset_Elem(result, e, esize, element1 + element2)
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_add_wrapping_pair_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_wrapping_pair_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_wrapping_pair(d, datasize, elements, esize, m, n)
}

val vector_arithmetic_binary_uniform_add_saturating_sisd : forall 'd 'datasize 'elements 'esize 'm 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_saturating_sisd (d, datasize, elements, esize, m, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    sum : int = undefined : int;
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        sum = element1 + element2;
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SatQ(sum, esize, unsigned);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_add_saturating_sisd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_saturating_sisd_decode (Rd, Rn, opcode, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_saturating_sisd(d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_add_saturating_simd_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_saturating_simd_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (size @ Q) == 0b110 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_saturating_sisd(d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_add_halving_truncating : forall 'd 'datasize 'elements 'esize 'm 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_halving_truncating (d, datasize, elements, esize, m, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    sum : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        sum = element1 + element2;
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, sum, 1))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_add_halving_truncating_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_halving_truncating_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_halving_truncating(d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_add_halving_rounding : forall 'd 'datasize 'elements 'esize 'm 'n ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_halving_rounding (d, datasize, elements, esize, m, n, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, element1 + element2 + 1, 1))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_add_halving_rounding_decode : (bits(5), bits(5), bits(5), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_halving_rounding_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_halving_rounding(d, datasize, elements, esize, m, n, unsigned)
}

val vector_arithmetic_binary_uniform_add_fp16 : forall 'd 'datasize 'elements 'esize 'm 'n ('pair : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & (2 * 'datasize >= 0 & 'esize >= 0 | not('pair)) & ('datasize >= 0 & 'esize >= 0 | not(not('pair))) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bool('pair)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_fp16 (d, datasize, elements, esize, m, n, pair) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if pair then {
            element1 = aget_Elem(concat, 2 * e, esize);
            element2 = aget_Elem(concat, 2 * e + 1, esize)
        } else {
            element1 = aget_Elem(operand1, e, esize);
            element2 = aget_Elem(operand2, e, esize)
        };
        result = aset_Elem(result, e, esize, FPAdd(element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_add_fp_decode : (bits(5), bits(5), bits(5), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_fp_decode (Rd, Rn, opcode, Rm, sz, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let pair = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_fp16(d, datasize, elements, esize, m, n, pair)
}

val vector_arithmetic_binary_uniform_add_fp16_decode : (bits(5), bits(5), bits(3), bits(5), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_fp16_decode (Rd, Rn, opcode, Rm, a, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let pair = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_fp16(d, datasize, elements, esize, m, n, pair)
}

val vector_arithmetic_binary_uniform_add_fp_complex : forall 'd 'datasize 'elements 'esize 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_fp_complex (d, datasize, elements, esize, m, n, rot) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element3 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements / 2 - 1) by 1 in inc) {
        match rot {
          0b0 => {
              element1 = FPNeg(aget_Elem(operand2, e * 2 + 1, esize));
              element3 = aget_Elem(operand2, e * 2, esize)
          },
          0b1 => {
              element1 = aget_Elem(operand2, e * 2 + 1, esize);
              element3 = FPNeg(aget_Elem(operand2, e * 2, esize))
          }
        };
        result = aset_Elem(result, e * 2, esize, FPAdd(aget_Elem(operand1, e * 2, esize), element1, FPCR));
        result = aset_Elem(result, e * 2 + 1, esize, FPAdd(aget_Elem(operand1, e * 2 + 1, esize), element3, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_uniform_add_fp_complex_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_uniform_add_fp_complex_decode (Rd, Rn, rot, Rm, size, U, Q) = {
    __unconditional = true;
    if ~(HaveFCADDExt()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b00 then {
        throw(Error_Undefined())
    };
    if Q == 0b0 & size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    if ~(HaveFP16Ext()) & esize == 16 then {
        throw(Error_Undefined())
    };
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_uniform_add_fp_complex(d, datasize, elements, esize, m, n, rot)
}

val vector_arithmetic_binary_element_mul_long : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n 'part ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), int('part), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_long (d, datasize, elements, esize, idxdsize, index, m, n, part, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('idxdsize) = V(m);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    let element2 = asl_Int(aget_Elem(operand2, index, esize), unsigned);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        product = __GetSlice_int(2 * esize, element1 * element2, 0);
        result = aset_Elem(result, e, 2 * esize, product)
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mul_long_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_long_decode (Rd, Rn, H, opcode, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {'n, 'n == 64. int('n)} = 64;
    let 'part = UInt(Q);
    let 'elements : {'n, 'n == div('datasize, 'esize). int('n)} = datasize / esize;
    let unsigned : bool = U == 0b1;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_long(d, datasize, elements, esize, idxdsize, index, m, n, part, unsigned)
}

val vector_arithmetic_binary_element_mul_int : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_int (d, datasize, elements, esize, idxdsize, index, m, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('idxdsize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits('esize) = undefined : bits('esize);
    let element2 = UInt(aget_Elem(operand2, index, esize));
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = UInt(aget_Elem(operand1, e, esize));
        product = __GetSlice_int(esize, element1 * element2, 0);
        result = aset_Elem(result, e, esize, product)
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mul_int_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_int_decode (Rd, Rn, H, opcode, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
    let 'elements : {'n, 'n == div('datasize, 'esize). int('n)} = datasize / esize;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_int(d, datasize, elements, esize, idxdsize, index, m, n)
}

val vector_arithmetic_binary_element_mul_high_sisd : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n ('round : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), bool('round)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_high_sisd (d, datasize, elements, esize, idxdsize, index, m, n, round) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('idxdsize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let 'round_const = if round then shl_int(1, esize - 1) else 0;
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : int = undefined : int;
    sat : bool = undefined : bool;
    let element2 = SInt(aget_Elem(operand2, index, esize));
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        product = 2 * element1 * element2 + round_const;
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SignedSatQ(shr_int(product, esize), esize);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mul_high_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_high_sisd_decode (Rd, Rn, H, op, Rm, M, L, size, U) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {'n, 'n == 'esize. int('n)} = esize;
    let 'elements : {'n, 'n == 1. int('n)} = 1;
    let round : bool = op == 0b1;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_high_sisd(d, datasize, elements, esize, idxdsize, index, m, n, round)
}

val vector_arithmetic_binary_element_mul_high_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_high_simd_decode (Rd, Rn, H, op, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
    let 'elements : {'n, 'n == div('datasize, 'esize). int('n)} = datasize / esize;
    let round : bool = op == 0b1;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_high_sisd(d, datasize, elements, esize, idxdsize, index, m, n, round)
}

val vector_arithmetic_binary_element_mul_fp16_sisd : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm ('mulx_op : Bool) 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), bool('mulx_op), int('n)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_fp16_sisd (d, datasize, elements, esize, idxdsize, index, m, mulx_op, n) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('idxdsize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    let element2 : bits('esize) = aget_Elem(operand2, index, esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        if mulx_op then {
            result = aset_Elem(result, e, esize, FPMulX(element1, element2, FPCR))
        } else {
            result = aset_Elem(result, e, esize, FPMul(element1, element2, FPCR))
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mul_fp16_sisd_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_fp16_sisd_decode (Rd, Rn, H, opcode, Rm, M, L, size, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'idxdsize = if H == 0b1 then 128 else 64;
    let index = UInt((H @ L) @ M);
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    let mulx_op = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mul_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, mulx_op, n)
}

val vector_arithmetic_binary_element_mul_fp16_simd_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_fp16_simd_decode (Rd, Rn, H, opcode, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'idxdsize = if H == 0b1 then 128 else 64;
    let index = UInt((H @ L) @ M);
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let mulx_op = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mul_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, mulx_op, n)
}

val vector_arithmetic_binary_element_mul_fp_sisd_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_fp_sisd_decode (Rd, Rn, H, opcode, Rm, M, L, sz, U) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    let Rmhi : bits(1) = M;
    match sz @ L {
      [bitzero] @ _ : bits(1) => {
          index = UInt(H @ L)
      },
      0b10 => {
          index = UInt(H)
      },
      0b11 => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize : {'n, 'n == 'esize. int('n)} = esize;
    let 'elements : {'n, 'n == 1. int('n)} = 1;
    let mulx_op : bool = U == 0b1;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, mulx_op, n)
}

val vector_arithmetic_binary_element_mul_fp_simd_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_fp_simd_decode (Rd, Rn, H, opcode, Rm, M, L, sz, U, Q) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    let Rmhi : bits(1) = M;
    match sz @ L {
      [bitzero] @ _ : bits(1) => {
          index = UInt(H @ L)
      },
      0b10 => {
          index = UInt(H)
      },
      0b11 => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
    let 'elements : {'n, 'n == div('datasize, 'esize). int('n)} = datasize / esize;
    let mulx_op : bool = U == 0b1;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, mulx_op, n)
}

val vector_arithmetic_binary_element_mul_double_sisd : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n 'part,
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_double_sisd (d, datasize, elements, esize, idxdsize, index, m, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('idxdsize) = V(m);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    sat : bool = undefined : bool;
    let element2 = SInt(aget_Elem(operand2, index, esize));
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        (product, sat) = SignedSatQ(2 * element1 * element2, 2 * esize);
        result = aset_Elem(result, e, 2 * esize, product);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mul_double_sisd_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_double_sisd_decode (Rd, Rn, H, opcode, Rm, M, L, size, U) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {'n, 'n == 'esize. int('n)} = esize;
    let 'elements : {'n, 'n == 1. int('n)} = 1;
    let 'part : {'n, 'n == 0. int('n)} = 0;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_double_sisd(d, datasize, elements, esize, idxdsize, index, m, n, part)
}

val vector_arithmetic_binary_element_mul_double_simd_decode : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mul_double_simd_decode (Rd, Rn, H, opcode, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {'n, 'n == 64. int('n)} = 64;
    let 'part = UInt(Q);
    let 'elements : {'n, 'n == div('datasize, 'esize). int('n)} = datasize / esize;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mul_double_sisd(d, datasize, elements, esize, idxdsize, index, m, n, part)
}

val vector_arithmetic_binary_element_mulacc_mul_norounding_i_upper : forall 'd 'datasize 'elements 'esize 'index 'm 'n 'part ('sub_op : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & div('esize, 2) >= 0 & div('datasize, 2) >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('index), int('m), int('n), int('part), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_mul_norounding_i_upper (d, datasize, elements, esize, index, m, n, part, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits(div('datasize, 2)) = Vpart(n, part);
    let operand2 : bits(128) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits(div('esize, 2)) = undefined : bits(div('esize, 2));
    let element2 : bits(div('esize, 2)) = aget_Elem(operand2, index, esize / 2);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize / 2);
        if sub_op then {
            element1 = FPNeg(element1)
        };
        result = aset_Elem(result, e, esize, FPMulAddH(aget_Elem(operand3, e, esize), element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_mul_norounding_i_upper_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_mul_norounding_i_upper_decode (Rd, Rn, H, S, Rm, M, L, sz, Q) = {
    __unconditional = true;
    if ~(HaveFP16MulNoRoundingToFP32Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(0b0 @ Rm);
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'index = UInt((H @ L) @ M);
    let 'esize = 32;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = S == 0b1;
    let 'part = 1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_mul_norounding_i_upper(d, datasize, elements, esize, index, m, n, part, sub_op)
}

val vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower : forall 'd 'datasize 'elements 'esize 'index 'm 'n 'part ('sub_op : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & div('esize, 2) >= 0 & div('datasize, 2) >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('index), int('m), int('n), int('part), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower (d, datasize, elements, esize, index, m, n, part, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits(div('datasize, 2)) = Vpart(n, part);
    let operand2 : bits(128) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits(div('esize, 2)) = undefined : bits(div('esize, 2));
    let element2 : bits(div('esize, 2)) = aget_Elem(operand2, index, esize / 2);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize / 2);
        if sub_op then {
            element1 = FPNeg(element1)
        };
        result = aset_Elem(result, e, esize, FPMulAddH(aget_Elem(operand3, e, esize), element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower_decode (Rd, Rn, H, S, Rm, M, L, sz, Q) = {
    __unconditional = true;
    if ~(HaveFP16MulNoRoundingToFP32Ext()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(0b0 @ Rm);
    if sz == 0b1 then {
        throw(Error_Undefined())
    };
    let 'index = UInt((H @ L) @ M);
    let 'esize = 32;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = S == 0b1;
    let 'part = 0;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower(d, datasize, elements, esize, index, m, n, part, sub_op)
}

val vector_arithmetic_binary_element_mulacc_long : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n 'part ('sub_op : Bool) ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), int('part), bool('sub_op), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_long (d, datasize, elements, esize, idxdsize, index, m, n, part, sub_op, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('idxdsize) = V(m);
    let operand3 : bits(2 * 'datasize) = V(d);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    let element2 = asl_Int(aget_Elem(operand2, index, esize), unsigned);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        product = __GetSlice_int(2 * esize, element1 * element2, 0);
        if sub_op then {
            result = aset_Elem(result, e, 2 * esize, aget_Elem(operand3, e, 2 * esize) - product)
        } else {
            result = aset_Elem(result, e, 2 * esize, aget_Elem(operand3, e, 2 * esize) + product)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_long_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_long_decode (Rd, Rn, H, o2, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    let 'idxdsize : {|128, 64|} = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let 'index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize : {'n, 'n == 64. int('n)} = 64;
    let 'part = UInt(Q);
    let 'elements : {'n, 'n == div('datasize, 'esize). int('n)} = datasize / esize;
    let unsigned : bool = U == 0b1;
    let sub_op : bool = o2 == 0b1;
    __PostDecode();
    assert(index >= 0 & esize >= 0 & (index + 1) * esize <= idxdsize);
    vector_arithmetic_binary_element_mulacc_long(d, datasize, elements, esize, idxdsize, index, m, n, part, sub_op, unsigned)
}

val vector_arithmetic_binary_element_mulacc_int : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_int (d, datasize, elements, esize, idxdsize, index, m, n, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('idxdsize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits('esize) = undefined : bits('esize);
    let element2 = UInt(aget_Elem(operand2, index, esize));
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = UInt(aget_Elem(operand1, e, esize));
        product = __GetSlice_int(esize, element1 * element2, 0);
        if sub_op then {
            result = aset_Elem(result, e, esize, aget_Elem(operand3, e, esize) - product)
        } else {
            result = aset_Elem(result, e, esize, aget_Elem(operand3, e, esize) + product)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_int_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_int_decode (Rd, Rn, H, o2, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    let 'idxdsize = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let Rmhi = Rmhi;
    let index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = o2 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_int(d, datasize, elements, esize, idxdsize, index, m, n, sub_op)
}

val vector_arithmetic_binary_element_mulacc_high_sisd : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n ('rounding : Bool) ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), bool('rounding), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_high_sisd (d, datasize, elements, esize, idxdsize, index, m, n, rounding, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('idxdsize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    let 'rounding_const = if rounding then shl_int(1, esize - 1) else 0;
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    element3 : int = undefined : int;
    let 'product = undefined : int;
    sat : bool = undefined : bool;
    let element2 = SInt(aget_Elem(operand2, index, esize));
    accum : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        element3 = SInt(aget_Elem(operand3, e, esize));
        if sub_op then {
            accum = shl_int(element3, esize) - 2 * (element1 * element2) + rounding_const
        } else {
            accum = shl_int(element3, esize) + 2 * (element1 * element2) + rounding_const
        };
        __tc1 : bits('esize) = undefined : bits('esize);
        (__tc1, sat) = SignedSatQ(shr_int(accum, esize), esize);
        result = aset_Elem(result, e, esize, __tc1);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_high_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_high_sisd_decode (Rd, Rn, H, S, Rm, M, L, size, U) = {
    __unconditional = true;
    if ~(HaveQRDMLAHExt()) then {
        throw(Error_Undefined())
    };
    let 'idxdsize = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let Rmhi = Rmhi;
    let index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let rounding = true;
    let sub_op = S == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_high_sisd(d, datasize, elements, esize, idxdsize, index, m, n, rounding, sub_op)
}

val vector_arithmetic_binary_element_mulacc_high_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_high_simd_decode (Rd, Rn, H, S, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    if ~(HaveQRDMLAHExt()) then {
        throw(Error_Undefined())
    };
    let 'idxdsize = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let Rmhi = Rmhi;
    let index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let rounding = true;
    let sub_op = S == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_high_sisd(d, datasize, elements, esize, idxdsize, index, m, n, rounding, sub_op)
}

val vector_arithmetic_binary_element_mulacc_fp16_sisd : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_fp16_sisd (d, datasize, elements, esize, idxdsize, index, m, n, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('idxdsize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    let element2 : bits('esize) = aget_Elem(operand2, index, esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        if sub_op then {
            element1 = FPNeg(element1)
        };
        result = aset_Elem(result, e, esize, FPMulAdd(aget_Elem(operand3, e, esize), element1, element2, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_fp16_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_fp16_sisd_decode (Rd, Rn, H, o2, Rm, M, L, size, U) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'idxdsize = if H == 0b1 then 128 else 64;
    let index = UInt((H @ L) @ M);
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = esize;
    let 'elements = 1;
    let sub_op = o2 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, n, sub_op)
}

val vector_arithmetic_binary_element_mulacc_fp16_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_fp16_simd_decode (Rd, Rn, H, o2, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    if ~(HaveFP16Ext()) then {
        throw(Error_Undefined())
    };
    let 'idxdsize = if H == 0b1 then 128 else 64;
    let index = UInt((H @ L) @ M);
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'esize = 16;
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = o2 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, n, sub_op)
}

val vector_arithmetic_binary_element_mulacc_fp_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_fp_sisd_decode (Rd, Rn, H, o2, Rm, M, L, sz, U) = {
    __unconditional = true;
    let 'idxdsize = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    let Rmhi = M;
    match sz @ L {
      [bitzero] @ _ : bits(1) => {
          index = UInt(H @ L)
      },
      0b10 => {
          index = UInt(H)
      },
      0b11 => {
          throw(Error_Undefined())
      }
    };
    let index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = esize;
    let 'elements = 1;
    let sub_op = o2 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, n, sub_op)
}

val vector_arithmetic_binary_element_mulacc_fp_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(1), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_fp_simd_decode (Rd, Rn, H, o2, Rm, M, L, sz, U, Q) = {
    __unconditional = true;
    let 'idxdsize = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    let Rmhi = M;
    match sz @ L {
      [bitzero] @ _ : bits(1) => {
          index = UInt(H @ L)
      },
      0b10 => {
          index = UInt(H)
      },
      0b11 => {
          throw(Error_Undefined())
      }
    };
    let index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    if (sz @ Q) == 0b10 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(32, UInt(sz));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    let sub_op = o2 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_fp16_sisd(d, datasize, elements, esize, idxdsize, index, m, n, sub_op)
}

val vector_arithmetic_binary_element_mulacc_double_sisd : forall 'd 'datasize 'elements 'esize 'idxdsize 'index 'm 'n 'part ('sub_op : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('idxdsize >= 0 & 'esize >= 0) & 'datasize >= 0.
  (int('d), int('datasize), int('elements), int('esize), int('idxdsize), int('index), int('m), int('n), int('part), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_double_sisd (d, datasize, elements, esize, idxdsize, index, m, n, part, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('idxdsize) = V(m);
    let operand3 : bits(2 * 'datasize) = V(d);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    accum : int = undefined : int;
    sat1 : bool = undefined : bool;
    sat2 : bool = undefined : bool;
    let element2 = SInt(aget_Elem(operand2, index, esize));
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        (product, sat1) = SignedSatQ(2 * element1 * element2, 2 * esize);
        if sub_op then {
            accum = SInt(aget_Elem(operand3, e, 2 * esize)) - SInt(product)
        } else {
            accum = SInt(aget_Elem(operand3, e, 2 * esize)) + SInt(product)
        };
        __tc1 : bits(2 * 'esize) = undefined : bits(2 * 'esize);
        (__tc1, sat2) = SignedSatQ(accum, 2 * esize);
        result = aset_Elem(result, e, 2 * esize, __tc1);
        if sat1 | sat2 then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_double_sisd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_double_sisd_decode (Rd, Rn, H, o2, Rm, M, L, size, U) = {
    __unconditional = true;
    let 'idxdsize = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let Rmhi = Rmhi;
    let index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let 'part = 0;
    let sub_op = o2 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_double_sisd(d, datasize, elements, esize, idxdsize, index, m, n, part, sub_op)
}

val vector_arithmetic_binary_element_mulacc_double_simd_decode : (bits(5), bits(5), bits(1), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_double_simd_decode (Rd, Rn, H, o2, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    let 'idxdsize = if H == 0b1 then 128 else 64;
    index : int = undefined : int;
    Rmhi : bits(1) = undefined : bits(1);
    match size {
      0b01 => {
          index = UInt((H @ L) @ M);
          Rmhi = 0b0
      },
      0b10 => {
          index = UInt(H @ L);
          Rmhi = M
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    let Rmhi = Rmhi;
    let index = index;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rmhi @ Rm);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let sub_op = o2 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_element_mulacc_double_sisd(d, datasize, elements, esize, idxdsize, index, m, n, part, sub_op)
}

val vector_arithmetic_binary_element_mulacc_complex : forall 'd 'datasize 'elements 'esize 'index 'm 'n,
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('index), int('m), int('n), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_complex (d, datasize, elements, esize, index, m, n, rot) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits('datasize) = V(m);
    let operand3 : bits('datasize) = V(d);
    result : bits('datasize) = undefined : bits('datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    element3 : bits('esize) = undefined : bits('esize);
    element4 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements / 2 - 1) by 1 in inc) {
        match rot {
          0b00 => {
              element1 = aget_Elem(operand2, index * 2, esize);
              element2 = aget_Elem(operand1, e * 2, esize);
              element3 = aget_Elem(operand2, index * 2 + 1, esize);
              element4 = aget_Elem(operand1, e * 2, esize)
          },
          0b01 => {
              element1 = FPNeg(aget_Elem(operand2, index * 2 + 1, esize));
              element2 = aget_Elem(operand1, e * 2 + 1, esize);
              element3 = aget_Elem(operand2, index * 2, esize);
              element4 = aget_Elem(operand1, e * 2 + 1, esize)
          },
          0b10 => {
              element1 = FPNeg(aget_Elem(operand2, index * 2, esize));
              element2 = aget_Elem(operand1, e * 2, esize);
              element3 = FPNeg(aget_Elem(operand2, index * 2 + 1, esize));
              element4 = aget_Elem(operand1, e * 2, esize)
          },
          0b11 => {
              element1 = aget_Elem(operand2, index * 2 + 1, esize);
              element2 = aget_Elem(operand1, e * 2 + 1, esize);
              element3 = FPNeg(aget_Elem(operand2, index * 2, esize));
              element4 = aget_Elem(operand1, e * 2 + 1, esize)
          }
        };
        result = aset_Elem(result, e * 2, esize, FPMulAdd(aget_Elem(operand3, e * 2, esize), element2, element1, FPCR));
        result = aset_Elem(result, e * 2 + 1, esize, FPMulAdd(aget_Elem(operand3, e * 2 + 1, esize), element4, element3, FPCR))
    };
    V(d) = result
}

val vector_arithmetic_binary_element_mulacc_complex_decode : (bits(5), bits(5), bits(1), bits(2), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_mulacc_complex_decode (Rd, Rn, H, rot, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    if ~(HaveFCADDExt()) then {
        throw(Error_Undefined())
    };
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(M @ Rm);
    if size == 0b00 | size == 0b11 then {
        throw(Error_Undefined())
    };
    index : int = undefined : int;
    if size == 0b01 then {
        index = UInt(H @ L)
    };
    if size == 0b10 then {
        index = UInt(H)
    };
    let 'index = index;
    let 'esize = shl_int(8, UInt(size));
    if ~(HaveFP16Ext()) & esize == 16 then {
        throw(Error_Undefined())
    };
    let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
    let 'elements : {'n, 'n == div('datasize, 'esize). int('n)} = datasize / esize;
    if size == 0b10 & (L == 0b1 | Q == 0b0) then {
        throw(Error_Undefined())
    };
    if (size == 0b01 & H == 0b1) & Q == 0b0 then {
        throw(Error_Undefined())
    };
    __PostDecode();
    assert(index * 2 >= 0 & esize >= 0 & (index * 2 + 2) * esize <= datasize);
    vector_arithmetic_binary_element_mulacc_complex(d, datasize, elements, esize, index, m, n, rot)
}

val vector_arithmetic_binary_element_dotp : forall 'd 'datasize 'elements 'esize 'index 'm 'n ('signed : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & div('esize, 4) >= 0 | not('signed)) & ('datasize >= 0 & div('esize, 4) >= 0 | not(not('signed))).
  (int('d), int('datasize), int('elements), int('esize), int('index), int('m), int('n), bool('signed)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_element_dotp (d, datasize, elements, esize, index, m, n, signed) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = V(n);
    let operand2 : bits(128) = V(m);
    result : bits('datasize) = V(d);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        res : int = 0;
        element1 : int = undefined : int;
        element2 : int = undefined : int;
        foreach (i from 0 to 3 by 1 in inc) {
            if signed then {
                element1 = SInt(aget_Elem(operand1, 4 * e + i, esize / 4));
                element2 = SInt(aget_Elem(operand2, 4 * index + i, esize / 4))
            } else {
                element1 = UInt(aget_Elem(operand1, 4 * e + i, esize / 4));
                element2 = UInt(aget_Elem(operand2, 4 * index + i, esize / 4))
            };
            res = res + element1 * element2
        };
        result = aset_Elem(result, e, esize, aget_Elem(result, e, esize) + res)
    };
    V(d) = result
}

val vector_arithmetic_binary_element_dotp_decode__0 : (bits(5), bits(5), bits(1), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

val vector_arithmetic_binary_element_dotp_decode__1 : (bits(5), bits(5), bits(1), bits(4), bits(4), bits(1), bits(1), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

overload vector_arithmetic_binary_element_dotp_decode = {
  vector_arithmetic_binary_element_dotp_decode__0,
  vector_arithmetic_binary_element_dotp_decode__1
}

function vector_arithmetic_binary_element_dotp_decode__0 (Rd, Rn, H, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    if ~(HaveDOTPExt()) then {
        throw(Error_Undefined())
    };
    if size != 0b10 then {
        throw(Error_Undefined())
    };
    let signed = U == 0b0;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(M @ Rm);
    let 'index = UInt(H @ L);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_element_dotp(d, datasize, elements, esize, index, m, n, signed)
}

function vector_arithmetic_binary_element_dotp_decode__1 (Rd, Rn, H, opcode, Rm, M, L, size, U, Q) = {
    __unconditional = true;
    if ~(HaveDOTPExt()) then {
        throw(Error_Undefined())
    };
    if size != 0b10 then {
        throw(Error_Undefined())
    };
    let signed = U == 0b0;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(M @ Rm);
    let 'index = UInt(H @ L);
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = if Q == 0b1 then 128 else 64;
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_element_dotp(d, datasize, elements, esize, index, m, n, signed)
}

val vector_arithmetic_binary_disparate_mul_product : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_product (d, datasize, elements, esize, m, n, part, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('datasize) = Vpart(m, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        result = aset_Elem(result, e, 2 * esize, __GetSlice_int(2 * esize, element1 * element2, 0))
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_mul_product_decode : (bits(5), bits(5), bits(1), bits(1), bits(1), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_product_decode (Rd, Rn, opcode_0_, opcode_1_, opcode_2_, opcode_3_, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_mul_product(d, datasize, elements, esize, m, n, part, unsigned)
}

val vector_arithmetic_binary_disparate_mul_poly : forall 'd 'datasize 'elements 'esize 'm 'n 'part,
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_poly (d, datasize, elements, esize, m, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('datasize) = Vpart(m, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : bits('esize) = undefined : bits('esize);
    element2 : bits('esize) = undefined : bits('esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        result = aset_Elem(result, e, 2 * esize, PolynomialMult(element1, element2))
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_mul_poly_decode : (bits(5), bits(5), bits(4), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_poly_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b01 | size == 0b10 then {
        throw(Error_Undefined())
    };
    if size == 0b11 & ~(HaveBit128PMULLExt()) then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_disparate_mul_poly(d, datasize, elements, esize, m, n, part)
}

val vector_arithmetic_binary_disparate_mul_double_sisd : forall 'd 'datasize 'elements 'esize 'm 'n 'part,
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_double_sisd (d, datasize, elements, esize, m, n, part) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('datasize) = Vpart(m, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    sat : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        element2 = SInt(aget_Elem(operand2, e, esize));
        (product, sat) = SignedSatQ(2 * element1 * element2, 2 * esize);
        result = aset_Elem(result, e, 2 * esize, product);
        if sat then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_mul_double_sisd_decode : (bits(5), bits(5), bits(4), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_double_sisd_decode (Rd, Rn, opcode, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b00 | size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let 'part = 0;
    __PostDecode();
    vector_arithmetic_binary_disparate_mul_double_sisd(d, datasize, elements, esize, m, n, part)
}

val vector_arithmetic_binary_disparate_mul_double_simd_decode : (bits(5), bits(5), bits(4), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_double_simd_decode (Rd, Rn, opcode, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b00 | size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    __PostDecode();
    vector_arithmetic_binary_disparate_mul_double_sisd(d, datasize, elements, esize, m, n, part)
}

val vector_arithmetic_binary_disparate_mul_dmacc_sisd : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('sub_op : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_dmacc_sisd (d, datasize, elements, esize, m, n, part, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('datasize) = Vpart(m, part);
    let operand3 : bits(2 * 'datasize) = V(d);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    accum : int = undefined : int;
    sat1 : bool = undefined : bool;
    sat2 : bool = undefined : bool;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = SInt(aget_Elem(operand1, e, esize));
        element2 = SInt(aget_Elem(operand2, e, esize));
        (product, sat1) = SignedSatQ(2 * element1 * element2, 2 * esize);
        if sub_op then {
            accum = SInt(aget_Elem(operand3, e, 2 * esize)) - SInt(product)
        } else {
            accum = SInt(aget_Elem(operand3, e, 2 * esize)) + SInt(product)
        };
        __tc1 : bits(2 * 'esize) = undefined : bits(2 * 'esize);
        (__tc1, sat2) = SignedSatQ(accum, 2 * esize);
        result = aset_Elem(result, e, 2 * esize, __tc1);
        if sat1 | sat2 then {
            FPSR = __SetSlice_bits(32, 1, FPSR, 27, 0b1)
        }
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode (Rd, Rn, o1, Rm, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b00 | size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize;
    let 'elements = 1;
    let 'part = 0;
    let sub_op = o1 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_mul_dmacc_sisd(d, datasize, elements, esize, m, n, part, sub_op)
}

val vector_arithmetic_binary_disparate_mul_dmacc_simd_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_dmacc_simd_decode (Rd, Rn, o1, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b00 | size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let sub_op = o1 == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_mul_dmacc_sisd(d, datasize, elements, esize, m, n, part, sub_op)
}

val vector_arithmetic_binary_disparate_mul_accum : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('sub_op : Bool) ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31) & ('datasize >= 0 & 'esize >= 0).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('sub_op), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_accum (d, datasize, elements, esize, m, n, part, sub_op, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('datasize) = Vpart(m, part);
    let operand3 : bits(2 * 'datasize) = V(d);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    product : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    accum : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        product = __GetSlice_int(2 * esize, element1 * element2, 0);
        if sub_op then {
            accum = aget_Elem(operand3, e, 2 * esize) - product
        } else {
            accum = aget_Elem(operand3, e, 2 * esize) + product
        };
        result = aset_Elem(result, e, 2 * esize, accum)
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_mul_accum_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_mul_accum_decode (Rd, Rn, o1, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let sub_op = o1 == 0b1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_mul_accum(d, datasize, elements, esize, m, n, part, sub_op, unsigned)
}

val vector_arithmetic_binary_disparate_diff : forall ('accumulate : Bool) 'd 'datasize 'elements 'esize 'm 'n 'part ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('d >= 0 & 'd <= 31 | not('accumulate)) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (bool('accumulate), int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_diff (accumulate, d, datasize, elements, esize, m, n, part, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('datasize) = Vpart(m, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    absdiff : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    result = if accumulate then V(d) else Zeros();
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        absdiff = __GetSlice_int(2 * esize, abs(element1 - element2), 0);
        result = aset_Elem(result, e, 2 * esize, aget_Elem(result, e, 2 * esize) + absdiff)
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_diff_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_diff_decode (Rd, Rn, op, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let accumulate = op == 0b0;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_diff(accumulate, d, datasize, elements, esize, m, n, part, unsigned)
}

val vector_arithmetic_binary_disparate_addsub_wide : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('sub_op : Bool) ('unsigned : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31 & 'part in {0, 1}) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('sub_op), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_addsub_wide (d, datasize, elements, esize, m, n, part, sub_op, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits(2 * 'datasize) = V(n);
    let operand2 : bits('datasize) = Vpart(m, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    sum : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, 2 * esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        if sub_op then {
            sum = element1 - element2
        } else {
            sum = element1 + element2
        };
        result = aset_Elem(result, e, 2 * esize, __GetSlice_int(2 * esize, sum, 0))
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_addsub_wide_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_addsub_wide_decode (Rd, Rn, o1, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let sub_op = o1 == 0b1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_addsub_wide(d, datasize, elements, esize, m, n, part, sub_op, unsigned)
}

val vector_arithmetic_binary_disparate_addsub_narrow : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('round : Bool) ('sub_op : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31) & (2 * 'datasize >= 0 & 2 * 'esize >= 0) & ('d >= 0 & 'd <= 31 & 'part in {0, 1}).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('round), bool('sub_op)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_addsub_narrow (d, datasize, elements, esize, m, n, part, round, sub_op) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits(2 * 'datasize) = V(n);
    let operand2 : bits(2 * 'datasize) = V(m);
    result : bits('datasize) = undefined : bits('datasize);
    let 'round_const = if round then shl_int(1, esize - 1) else 0;
    element1 : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    element2 : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    sum : bits(2 * 'esize) = undefined : bits(2 * 'esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, 2 * esize);
        element2 = aget_Elem(operand2, e, 2 * esize);
        if sub_op then {
            sum = element1 - element2
        } else {
            sum = element1 + element2
        };
        sum = sum + round_const;
        result = aset_Elem(result, e, esize, slice(sum, esize, esize))
    };
    Vpart(d, part) = result
}

val vector_arithmetic_binary_disparate_addsub_narrow_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_addsub_narrow_decode (Rd, Rn, o1, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let sub_op = o1 == 0b1;
    let round = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_addsub_narrow(d, datasize, elements, esize, m, n, part, round, sub_op)
}

val vector_arithmetic_binary_disparate_addsub_long : forall 'd 'datasize 'elements 'esize 'm 'n 'part ('sub_op : Bool) ('unsigned : Bool),
  ('n >= 0 & 'n <= 31 & 'part in {0, 1}) & ('m >= 0 & 'm <= 31) & ('datasize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('elements), int('esize), int('m), int('n), int('part), bool('sub_op), bool('unsigned)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_addsub_long (d, datasize, elements, esize, m, n, part, sub_op, unsigned) = {
    CheckFPAdvSIMDEnabled64();
    let operand1 : bits('datasize) = Vpart(n, part);
    let operand2 : bits('datasize) = Vpart(m, part);
    result : bits(2 * 'datasize) = undefined : bits(2 * 'datasize);
    element1 : int = undefined : int;
    element2 : int = undefined : int;
    sum : int = undefined : int;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), unsigned);
        if sub_op then {
            sum = element1 - element2
        } else {
            sum = element1 + element2
        };
        result = aset_Elem(result, e, 2 * esize, __GetSlice_int(2 * esize, sum, 0))
    };
    V(d) = result
}

val vector_arithmetic_binary_disparate_addsub_long_decode : (bits(5), bits(5), bits(1), bits(5), bits(2), bits(1), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function vector_arithmetic_binary_disparate_addsub_long_decode (Rd, Rn, o1, Rm, size, U, Q) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    if size == 0b11 then {
        throw(Error_Undefined())
    };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = 64;
    let 'part = UInt(Q);
    let 'elements = datasize / esize;
    let sub_op = o1 == 0b1;
    let unsigned = U == 0b1;
    __PostDecode();
    vector_arithmetic_binary_disparate_addsub_long(d, datasize, elements, esize, m, n, part, sub_op, unsigned)
}
