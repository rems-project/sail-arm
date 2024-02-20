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

// Pull out length calculation, constrain M, and rewrite welem and telem so that we can monomorphise

val DecodeBitMasks_core : forall 'len 'esize 'M ('immediate : Bool),
  'len in {1, 2, 3, 4, 5, 6} & 'M in {32, 64} & 'M >= 'esize.
  (int('len), int('esize), bits(1), bits(6), bits(6), bool('immediate), int('M)) -> (bits('M), bits('M))

function DecodeBitMasks_core (len, esize, immN, imms, immr, immediate, M) = {
    assert(M >= (1 << len));
    let levels : bits(6) = zext_ones(6, len);
    if immediate & (imms & levels) == levels then {
        throw(Error_Undefined())
    };
    let 's = UInt(imms & levels);
    let 'r = UInt(immr & levels);
    let 'diff = s - r;
    let 'd = UInt(diff[len - 1 .. 0]);
    assert(constraint('esize >= 's + 1));
    let welem : bits('esize) = zext_ones(esize, s + 1);
    assert(constraint('esize >= 'd + 1));
    let telem : bits('esize) = zext_ones(esize, d + 1);
    assert(constraint('esize * div('M, 'esize) == 'M));
    let wmask : bits('M) = Replicate(ROR(welem, r), DIV(M, esize));
    let tmask : bits('M) = Replicate(telem, DIV(M, esize));
    return((wmask, tmask))
}

val DecodeBitMasks : forall 'M ('immediate : Bool), 'M in {32, 64}.
  (bits(1), bits(6), bits(6), bool('immediate), int('M)) -> (bits('M), bits('M))

function DecodeBitMasks (immN, imms, immr, immediate, M) = {
    let 'len = HighestSetBit(immN @ not_vec(imms));
    if len < 1 then {
        throw(Error_Undefined())
    };
    let 'esize = (1 << len);
    match len {
        1 => DecodeBitMasks_core(1, 2, immN, imms, immr, immediate, M),
        2 => DecodeBitMasks_core(2, 4, immN, imms, immr, immediate, M),
        3 => DecodeBitMasks_core(3, 8, immN, imms, immr, immediate, M),
        4 => DecodeBitMasks_core(4, 16, immN, imms, immr, immediate, M),
        5 => DecodeBitMasks_core(5, 32, immN, imms, immr, immediate, M),
        6 => {
	    assert('M == 64);
	    DecodeBitMasks_core(6, 64, immN, imms, immr, immediate, M)
	},
	_ => { assert(false); (Zeros(M), Zeros(M)) }
    }
}
