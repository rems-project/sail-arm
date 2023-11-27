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

// Split fsize for monomorphisation

val execute_aarch64_instrs_float_convert_int_core : forall 'd 'fltsize 'fsize 'intsize ('is_unsigned : Bool) 'n 'part,
  ('part in {0, 1} & 0 <= 'n & 'n <= 31 & 'intsize in {32, 64} & 'fltsize in {16, 32, 64, 128} & 'fsize in {16, 32, 64, 128} & 0 <= 'd & 'd <= 31).
  (int('d), int('fltsize), int('fsize), int('intsize), int('n), FPConvOp, int('part), FPRounding, bool('is_unsigned), FPCRType, bool) -> unit

function execute_aarch64_instrs_float_convert_int_core (d, fltsize, fsize, intsize, n, op, part, rounding, is_unsigned, fpcr, merge) = {
    fltval : bits('fsize) = undefined;
    intval : bits('intsize) = undefined;
    match op {
      FPConvOp_CVT_FtoI => {
          let fltval : bits('fsize) = V_read(n, fsize);
          assert(constraint(('fsize in {16, 32, 64} & 'intsize in {16, 32, 64})));
          let intval : bits('intsize) = FPToFixed(fltval, 0, is_unsigned, fpcr, rounding, intsize);
          X_set(d, intsize) = intval
      },
      FPConvOp_CVT_ItoF => {
          let intval : bits('intsize) = X_read(n, intsize);
          fltval : bits('fsize) = if merge then V_read(d, fsize) else
            Zeros(fsize);
          assert(constraint(('fltsize in {16, 32, 64} & 'intsize in {16, 32, 64})));
          fltval = Elem_set(fltval, 0, fltsize, FixedToFP(intval, 0, is_unsigned, fpcr, rounding, fltsize));
          V_set(d, fsize) = fltval
      },
      FPConvOp_MOV_FtoI => {
          let fltval : bits('fsize) = Vpart_read(n, part, fsize);
          assert(constraint(('fsize >= 0 & 'intsize >= 'fsize)));
          let intval : bits('intsize) = ZeroExtend(fltval, intsize);
          X_set(d, intsize) = intval
      },
      FPConvOp_MOV_ItoF => {
          let intval : bits('intsize) = X_read(n, intsize);
          assert(constraint((0 <= 'fsize - 1 & 'fsize - 1 < 'intsize)));
          let fltval : bits('fsize) = intval[fsize - 1 .. 0];
          Vpart_set(d, part, fsize) = fltval
      },
      FPConvOp_CVT_FtoI_JS => {
          z : bits(1) = undefined;
          let fltval : bits('fsize) = V_read(n, fsize);
          assert(constraint('fsize == 64));
          assert(constraint('intsize == 32));
          (intval, z) = FPToFixedJS(fltval, fpcr, true, intsize);
          (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = (0b0 @ z) @ 0b00;
          X_set(d, intsize) = intval
      }
    }
}

val execute_aarch64_instrs_float_convert_int : forall 'd 'fltsize 'intsize ('is_unsigned : Bool) 'n 'part,
  ('part in {0, 1} & 0 <= 'n & 'n <= 31 & 'intsize in {32, 64} & 'fltsize in {16, 32, 64, 128} & 0 <= 'd & 'd <= 31).
  (int('d), int('fltsize), int('intsize), int('n), FPConvOp, int('part), FPRounding, bool('is_unsigned)) -> unit

function execute_aarch64_instrs_float_convert_int (d, fltsize, intsize, n, op, part, rounding, is_unsigned) = {
    if op == FPConvOp_CVT_FtoI_JS then {
        CheckFPAdvSIMDEnabled64()
    } else {
        CheckFPEnabled64()
    };
    let fpcr : FPCRType = FPCR_read();
    let merge : bool = IsMerging(fpcr);
    let 'fsize = if op == FPConvOp_CVT_ItoF & merge then 128 else fltsize;
    match fsize {
        16 => execute_aarch64_instrs_float_convert_int_core (d, fltsize, fsize, intsize, n, op, part, rounding, is_unsigned, fpcr, merge),
        32 => execute_aarch64_instrs_float_convert_int_core (d, fltsize, fsize, intsize, n, op, part, rounding, is_unsigned, fpcr, merge),
        64 => execute_aarch64_instrs_float_convert_int_core (d, fltsize, fsize, intsize, n, op, part, rounding, is_unsigned, fpcr, merge),
        128 => execute_aarch64_instrs_float_convert_int_core (d, fltsize, fsize, intsize, n, op, part, rounding, is_unsigned, fpcr, merge)
    }
}

val execute_aarch64_instrs_float_convert_fix_core : forall 'd 'fltsize 'fsize 'fracbits 'intsize ('is_unsigned : Bool) 'n,
  (0 <= 'n & 'n <= 31 & 'intsize in {32, 64} & 1 <= 'fracbits & 'fracbits <= 64 & 'fltsize in {16, 32, 64} & 'fsize in {16, 32, 64, 128} & 0 <= 'd & 'd <= 31).
  (int('d), int('fltsize), int('fsize), int('fracbits), int('intsize), int('n), FPConvOp, FPRounding, bool('is_unsigned), FPCRType, bool) -> unit

function execute_aarch64_instrs_float_convert_fix_core (d, fltsize, fsize, fracbits, intsize, n, op, rounding, is_unsigned, fpcr, merge) = {
    fltval : bits('fsize) = undefined;
    intval : bits('intsize) = undefined;
    match op {
      FPConvOp_CVT_FtoI => {
          let fltval : bits('fsize) = V_read(n, fsize);
          assert(constraint(('fsize in {16, 32, 64} & 'intsize in {16, 32, 64})));
          let intval : bits('intsize) = FPToFixed(fltval, fracbits, is_unsigned, fpcr, rounding, intsize);
          X_set(d, intsize) = intval
      },
      FPConvOp_CVT_ItoF => {
          let intval : bits('intsize) = X_read(n, intsize);
          fltval : bits('fsize) = if merge then V_read(d, fsize) else
            Zeros(fsize);
          fltval = Elem_set(fltval, 0, fltsize, FixedToFP(intval, fracbits, is_unsigned, fpcr, rounding, fltsize));
          V_set(d, fsize) = fltval
      },
      _ => ()
    }
}

val execute_aarch64_instrs_float_convert_fix : forall 'd 'fltsize 'fracbits 'intsize ('is_unsigned : Bool) 'n,
  (0 <= 'n & 'n <= 31 & 'intsize in {32, 64} & 1 <= 'fracbits & 'fracbits <= 64 & 'fltsize in {16, 32, 64} & 0 <= 'd & 'd <= 31).
  (int('d), int('fltsize), int('fracbits), int('intsize), int('n), FPConvOp, FPRounding, bool('is_unsigned)) -> unit

function execute_aarch64_instrs_float_convert_fix (d, fltsize, fracbits, intsize, n, op, rounding, is_unsigned) = {
    CheckFPEnabled64();
    let fpcr : FPCRType = FPCR_read();
    let merge : bool = IsMerging(fpcr);
    let 'fsize = if op == FPConvOp_CVT_ItoF & merge then 128 else fltsize;
    match fsize {
        16 => execute_aarch64_instrs_float_convert_fix_core(d, fltsize, fsize, fracbits, intsize, n, op, rounding, is_unsigned, fpcr, merge),
        32 => execute_aarch64_instrs_float_convert_fix_core(d, fltsize, fsize, fracbits, intsize, n, op, rounding, is_unsigned, fpcr, merge),
        64 => execute_aarch64_instrs_float_convert_fix_core(d, fltsize, fsize, fracbits, intsize, n, op, rounding, is_unsigned, fpcr, merge),
        128 => execute_aarch64_instrs_float_convert_fix_core(d, fltsize, fsize, fracbits, intsize, n, op, rounding, is_unsigned, fpcr, merge)
    }
}
