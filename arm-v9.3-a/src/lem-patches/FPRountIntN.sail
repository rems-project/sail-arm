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

val FPRoundIntN : forall ('N 'intsize : Int), 'N in {32, 64}.
  (implicit('N), bits('N), bits(64), FPRounding, int('intsize)) -> bits('N) effect {escape, rreg, undef, wmem, wreg}

function FPRoundIntN (N, op, fpcr, rounding, intsize) = {
    error : real = undefined;
    fptype : FPType = undefined;
    int_result : int = undefined;
    overflow : bool = undefined;
    real_result : real = undefined;
    sign : bits(1) = undefined;
    value_name : real = undefined;
    assert(rounding != FPRounding_ODD);
    assert('N == 32 | 'N == 64);
    assert(intsize == 32 | intsize == 64);
    exp : int = undefined;
    result : bits('N) = undefined;
    round_up : bool = undefined;
    let 'E = if 'N == 32 then 8 else 11;
    let 'F = 'N - (E + 1);
    let altfp : bool = (HaveAltFP() & not_bool(UsingAArch32())) & [fpcr[1]] == 0b1;
    let fpexc : bool = not_bool(altfp);
    (fptype, sign, value_name) = FPUnpack__1(op, fpcr, fpexc);
    if fptype == FPType_SNaN | fptype == FPType_QNaN | fptype == FPType_Infinity then {
        if 'N == 32 then {
            let 'exp = 126 + intsize;
            result = (0b1 @ exp[E - 1 .. 0]) @ Zeros(F)
        } else {
            let 'exp = 1022 + intsize;
            result = (0b1 @ exp[E - 1 .. 0]) @ Zeros(F)
        };
        FPProcessException(FPExc_InvalidOp, fpcr)
    } else if fptype == FPType_Zero then {
        result = FPZero('N, sign)
    } else {
        int_result : int = RoundDown(value_name);
        error : real = value_name - Real(int_result);
        match rounding {
          FPRounding_TIEEVEN => {
              round_up = error > 0.5 | error == 0.5 & [int_result[0]] == 0b1
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
          },
          _ => ()
        };
        if round_up then {
            int_result = int_result + 1
        } else ();
        let 'int_result = int_result;
        let overflow : bool = int_result > pow2(intsize - 1) - 1 | int_result < negate(1) * pow2(intsize - 1);
        if overflow then {
            if 'N == 32 then {
                let 'exp = 126 + intsize;
                result = (0b1 @ exp[E - 1 .. 0]) @ Zeros(F)
            } else {
                let 'exp = 1022 + intsize;
                result = (0b1 @ exp[E - 1 .. 0]) @ Zeros(F)
            };
            FPProcessException(FPExc_InvalidOp, fpcr);
            error = 0.0
        } else {
            let real_result : real = Real(int_result);
            if real_result == 0.0 then {
                result = FPZero('N, sign)
            } else {
                result = FPRound('N, real_result, fpcr, FPRounding_ZERO)
            }
        };
        if error != 0.0 then {
            FPProcessException(FPExc_Inexact, fpcr)
        } else ()
    };
    return(result)
}
