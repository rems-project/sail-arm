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

val Auth : forall ('data 'is_combined : Bool).
  (bits(64), bits(64), bits(128), bool('data), bits(1), bool('is_combined)) -> bits(64) effect {escape, rreg, undef, wreg}

function Auth (ptr, modifier, K, data, key_number, is_combined) = {
    result : bits(64) = undefined;
    original_ptr : bits(64) = undefined;
    error_code : bits(2) = undefined;
    let tbi : bool = EffectiveTBI(ptr, not_bool(data), PSTATE.EL) == 0b1;
    let 'bottom_PAC_bit = CalculateBottomPACBit([ptr[55]]);
    let extfield : bits(64) = Replicate([ptr[55]], 64);
    if tbi then {
        assert(constraint((0 <= 56 - 'bottom_PAC_bit - 1 & 56 - 'bottom_PAC_bit - 1 < 64)));
        assert(constraint(0 <= 'bottom_PAC_bit - 1));
        original_ptr = (ptr[63 .. 56] @ extfield[56 - bottom_PAC_bit - 1 .. 0]) @ ptr[bottom_PAC_bit - 1 .. 0]
    } else {
        assert(constraint((0 <= 64 - 'bottom_PAC_bit - 1 & 64 - 'bottom_PAC_bit - 1 < 64)));
        assert(constraint(0 <= 'bottom_PAC_bit - 1));
        original_ptr = extfield[64 - bottom_PAC_bit - 1 .. 0] @ ptr[bottom_PAC_bit - 1 .. 0]
    };
    let PAC : bits(64) = ComputePAC(original_ptr, modifier, K[127 .. 64], K[63 .. 0]);
    if tbi then {
        if not_bool(HaveEnhancedPAC2()) then {
            assert(constraint((0 <= 'bottom_PAC_bit & 'bottom_PAC_bit <= 54)));
            if PAC[54 .. bottom_PAC_bit] == ptr[54 .. bottom_PAC_bit] then {
                result = original_ptr
            } else {
                let error_code : bits(2) = key_number @ not_vec(key_number);
                result = (original_ptr[63 .. 55] @ error_code) @ original_ptr[52 .. 0]
            }
        } else {
            result = ptr;
            assert(constraint((0 <= 'bottom_PAC_bit & 'bottom_PAC_bit <= 54)));
            result[54 .. bottom_PAC_bit] = EOR(result[54 .. bottom_PAC_bit], PAC[54 .. bottom_PAC_bit]);
            if HaveFPACCombined() | HaveFPAC() & not_bool(is_combined) then {
                if [result[55]] == 0b0 then {
                    if IsZero(result[54 .. bottom_PAC_bit]) then {
                        let error_code : bits(2) = (if data then 0b1 else 0b0) @ key_number;
                        AArch64_PACFailException(error_code)
                    }
                } else {
                    if IsOnes(result[54 .. bottom_PAC_bit]) then {
                        let error_code : bits(2) = (if data then 0b1 else 0b0) @ key_number;
                        AArch64_PACFailException(error_code)
                    }
                }
            }
        }
    } else {
        if not_bool(HaveEnhancedPAC2()) then {
            assert(constraint((0 <= 'bottom_PAC_bit & 'bottom_PAC_bit <= 54)));
            if PAC[54 .. bottom_PAC_bit] == ptr[54 .. bottom_PAC_bit] & PAC[63 .. 56] == ptr[63 .. 56] then {
                result = original_ptr
            } else {
                let error_code : bits(2) = key_number @ not_vec(key_number);
                result = ([original_ptr[63]] @ error_code) @ original_ptr[60 .. 0]
            }
        } else {
            result = ptr;
            assert(constraint((0 <= 'bottom_PAC_bit & 'bottom_PAC_bit <= 54)));
            result[54 .. bottom_PAC_bit] = EOR(result[54 .. bottom_PAC_bit], PAC[54 .. bottom_PAC_bit]);
            result[63 .. 56] = EOR(result[63 .. 56], PAC[63 .. 56]);
            if HaveFPACCombined() | HaveFPAC() & not_bool(is_combined) then {
                if [result[55]] == 0b0 then {
                    if IsZero(result[63 .. bottom_PAC_bit]) then {
                        let error_code : bits(2) = (if data then 0b1 else 0b0) @ key_number;
                        AArch64_PACFailException(error_code)
                    }
                } else {
                    if IsOnes(result[63 .. bottom_PAC_bit]) then {
                        let error_code : bits(2) = (if data then 0b1 else 0b0) @ key_number;
                        AArch64_PACFailException(error_code)
                    }
                }
            }
        }
    };
    return(result)
}
