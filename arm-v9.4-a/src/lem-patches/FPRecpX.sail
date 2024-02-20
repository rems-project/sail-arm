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

// Add implicit parameter so that we can split on N

val FPRecpX : forall 'N, 'N in {16, 32, 64}.
  (implicit('N), bits('N), FPCRType) -> bits('N)

function FPRecpX (N, op, fpcr_in) = {
    fptype : FPType = undefined;
    sign : bits(1) = undefined;
    value_name : real = undefined;
    assert('N == 16 | 'N == 32 | 'N == 64);
    fpcr : bits(64) = fpcr_in.bits;
    esize : {|5, 8, 11|} = 5;
    match 'N {
      16 => {
          esize = 5
      },
      32 => {
          esize = 8
      },
      64 => {
          esize = 11
      },
      _ => ()
    };
    let 'esize = esize;
    result : bits('N) = undefined;
    exp : bits('esize) = undefined;
    let frac : bits('N - ('esize + 1)) = Zeros();
    let altfp : bool = HaveAltFP() & [fpcr[1]] == 0b1;
    let fpexc : bool = not_bool(altfp);
    if altfp then {
        (fpcr[0 .. 0] @ fpcr[24 .. 24]) = 0b11
    } else ();
    (fptype, sign, value_name) = FPUnpack__1(op, Mk_FPCRType(fpcr), fpexc);
    match 'N {
      16 => {
          assert(constraint((10 <= 10 + 'esize - 1 & 10 + 'esize - 1 < 'N)));
          exp = op[10 + esize - 1 .. 10]
      },
      32 => {
          assert(constraint((23 <= 23 + 'esize - 1 & 23 + 'esize - 1 < 'N)));
          exp = op[23 + esize - 1 .. 23]
      },
      64 => {
          exp = op[52 + esize - 1 .. 52]
      },
      _ => ()
    };
    let max_exp : bits('esize) = Ones(esize) - 1;
    if fptype == FPType_SNaN | fptype == FPType_QNaN then {
        result = FPProcessNaN__1(fptype, op, Mk_FPCRType(fpcr), fpexc)
    } else {
        if IsZero(exp) then {
            result = (sign @ max_exp) @ frac
        } else {
            result = (sign @ not_vec(exp)) @ frac
        }
    };
    return(result)
}
