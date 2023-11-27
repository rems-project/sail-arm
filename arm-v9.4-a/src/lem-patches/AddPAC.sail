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

// Rewrite some uses of variable-length bitvectors to make it more easily
// monomorphisable:
// - From EOR(ptr[54 .. bottom_PAC_bit], PAC[54 .. bottom_PAC_bit])
//   to EOR(ptr, PAC)[54 .. bottom_PAC_bit]
// - Initialisation of unusedbits_mask

val AddPAC : forall ('data : Bool).
  (bits(64), bits(64), bits(128), bool('data)) -> bits(64)

function AddPAC (ptr, modifier, K, data) = {
    result : bits(64) = undefined;
    ext_ptr : bits(64) = undefined;
    selbit : bits(1) = undefined;
    let isgeneric : bool = false;
    let tbi : bool = EffectiveTBI(ptr, not_bool(data), PSTATE.EL) == 0b1;
    let mtx : bool = EffectiveMTX(ptr, not_bool(data), PSTATE.EL) == 0b1;
    let 'top_bit = if tbi then 55 else 63;
    if PtrHasUpperAndLowerAddRanges() then {
        assert(S1TranslationRegime__1() == EL1 | S1TranslationRegime__1() == EL2);
        if S1TranslationRegime__1() == EL1 then {
            if data then {
                if TCR_EL1[TBI1] == 0b1 | TCR_EL1[TBI0] == 0b1 then {
                    selbit = [ptr[55]]
                } else {
                    selbit = [ptr[63]]
                }
            } else {
                if TCR_EL1[TBI1] == 0b1 & TCR_EL1[TBID1] == 0b0 | TCR_EL1[TBI0] == 0b1 & TCR_EL1[TBID0] == 0b0 then {
                    selbit = [ptr[55]]
                } else {
                    selbit = [ptr[63]]
                }
            }
        } else {
            if data then {
                if TCR_EL2[TBI1] == 0b1 | TCR_EL2[TBI0] == 0b1 then {
                    selbit = [ptr[55]]
                } else {
                    selbit = [ptr[63]]
                }
            } else {
                if TCR_EL2[TBI1] == 0b1 & TCR_EL2[TBID1] == 0b0 | TCR_EL2[TBI0] == 0b1 & TCR_EL2[TBID0] == 0b0 then {
                    selbit = [ptr[55]]
                } else {
                    selbit = [ptr[63]]
                }
            }
        }
    } else {
        selbit = if tbi then [ptr[55]] else [ptr[63]]
    };
    if HaveEnhancedPAC2() & ConstPACField() then {
        selbit = [ptr[55]]
    };
    let selbit = selbit;
    let 'bottom_PAC_bit = CalculateBottomPACBit(selbit);
    if tbi & bottom_PAC_bit >= 55 then {
        return(ptr)
    };
    let extfield : bits(64) = Replicate(selbit, 64);
    if tbi then {
        assert(constraint(56 - 'bottom_PAC_bit - 1 < 64));
        assert(constraint(0 <= 'bottom_PAC_bit - 1));
        ext_ptr = (ptr[63 .. 56] @ extfield[56 - bottom_PAC_bit - 1 .. 0]) @ ptr[bottom_PAC_bit - 1 .. 0]
    } else if mtx then {
        assert(constraint((0 <= 56 - 'bottom_PAC_bit - 1 & 56 - 'bottom_PAC_bit - 1 < 64)));
        assert(constraint(0 <= 'bottom_PAC_bit - 1));
        ext_ptr = ((extfield[63 .. 60] @ ptr[59 .. 56]) @ extfield[56 - bottom_PAC_bit - 1 .. 0]) @ ptr[bottom_PAC_bit - 1 .. 0]
    } else {
        assert(constraint((0 <= 64 - 'bottom_PAC_bit - 1 & 64 - 'bottom_PAC_bit - 1 < 64)));
        assert(constraint(0 <= 'bottom_PAC_bit - 1));
        ext_ptr = extfield[64 - bottom_PAC_bit - 1 .. 0] @ ptr[bottom_PAC_bit - 1 .. 0]
    };
    PAC : bits(64) = ComputePAC(ext_ptr, modifier, K[127 .. 64], K[63 .. 0], isgeneric);
    assert(constraint((0 <= 'bottom_PAC_bit & 'bottom_PAC_bit <= 54)));
    unusedbits_mask : bits(64) = Zeros(9) @ Ones(54 - bottom_PAC_bit + 1) @ Zeros(bottom_PAC_bit);
    // unusedbits_mask[54 .. bottom_PAC_bit] = Ones(54 - bottom_PAC_bit + 1);
    // foreach (i from 54 to bottom_PAC_bit by 1 in dec) {
    //     unusedbits_mask[i] = bitone
    // }
    if tbi then {
        unusedbits_mask[63 .. 56] = Ones(8)
    } else if mtx then {
        unusedbits_mask[63 .. 60] = Ones(4)
    } else ();
    if not_bool(IsZero(ptr & unusedbits_mask)) & (ptr & unusedbits_mask) != unusedbits_mask then {
        if HaveEnhancedPAC() then {
            PAC = 0x0000000000000000
        } else if not_bool(HaveEnhancedPAC2()) then {
            PAC[top_bit - 1] = Bit(not_vec([PAC[top_bit - 1]]))
        } else ()
    };
    if not_bool(HaveEnhancedPAC2()) then {
        if tbi then {
            assert(constraint((0 <= 'bottom_PAC_bit - 1 & 'bottom_PAC_bit - 1 < 64)));
            result = ((ptr[63 .. 56] @ selbit) @ PAC[54 .. bottom_PAC_bit]) @ ptr[bottom_PAC_bit - 1 .. 0]
        } else {
            assert(constraint((0 <= 'bottom_PAC_bit - 1 & 'bottom_PAC_bit - 1 < 64)));
            result = ((PAC[63 .. 56] @ selbit) @ PAC[54 .. bottom_PAC_bit]) @ ptr[bottom_PAC_bit - 1 .. 0];
            assert(not_bool(mtx))
        }
    } else {
        if tbi then {
            assert(constraint((0 <= 'bottom_PAC_bit - 1 & 'bottom_PAC_bit - 1 < 64)));
            result = ((ptr[63 .. 56] @ selbit) @ EOR(ptr, PAC)[54 .. bottom_PAC_bit]) @ ptr[bottom_PAC_bit - 1 .. 0]
        } else if mtx then {
            assert(constraint((0 <= 'bottom_PAC_bit - 1 & 'bottom_PAC_bit - 1 < 64)));
            result = (((EOR(ptr[63 .. 60], PAC[63 .. 60]) @ ptr[59 .. 56]) @ selbit) @ EOR(ptr, PAC)[54 .. bottom_PAC_bit]) @ ptr[bottom_PAC_bit - 1 .. 0]
        } else {
            assert(constraint((0 <= 'bottom_PAC_bit - 1 & 'bottom_PAC_bit - 1 < 64)));
            result = ((EOR(ptr[63 .. 56], PAC[63 .. 56]) @ selbit) @ EOR(ptr, PAC)[54 .. bottom_PAC_bit]) @ ptr[bottom_PAC_bit - 1 .. 0]
        }
    };
    return(result)
}
