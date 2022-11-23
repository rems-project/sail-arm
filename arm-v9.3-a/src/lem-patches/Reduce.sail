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

val ReduceCombine : forall ('esize : Int), 'esize in {8, 16, 32, 64}.
  (ReduceOp, bits('esize), bits('esize), bool) -> bits('esize)

function ReduceCombine (op, lo, hi, altfp) = if 'esize == 8 then {
    assert(op == ReduceOp_ADD);
    lo + hi
  } else match op {
  ReduceOp_FMINNUM => {
      FPMinNum(lo, hi, FPCR_read())
  },
  ReduceOp_FMAXNUM => {
      FPMaxNum(lo, hi, FPCR_read())
  },
  ReduceOp_FMIN => {
      FPMin__1(lo, hi, FPCR_read(), altfp)
  },
  ReduceOp_FMAX => {
      FPMax__1(lo, hi, FPCR_read(), altfp)
  },
  ReduceOp_FADD => {
      FPAdd(lo, hi, FPCR_read())
  },
  ReduceOp_ADD => {
      lo + hi
  }
}

val Reduce16 : forall ('esize : Int), 'esize in {8, 16}.
  (ReduceOp, bits(16), int('esize), bool) -> bits('esize)

function Reduce16 (op, input, esize, altfp) = {
    if esize == 16 then input else {
        let hi = Slice(input, 8, 8);
        let lo = Slice(input, 0, 8);
        (ReduceCombine(op, lo, hi, altfp) : bits(8))
    }
}

val Reduce32 : forall ('esize : Int), 'esize in {8, 16, 32}.
  (ReduceOp, bits(32), int('esize), bool) -> bits('esize)

function Reduce32 (op, input, esize, altfp) = {
    if esize == 32 then input else {
        let hi = Reduce16(op, Slice(input, 16, 16), esize, altfp);
        let lo = Reduce16(op, Slice(input, 0, 16), esize, altfp);
        ReduceCombine(op, lo, hi, altfp)
    }
}

val Reduce64 : forall ('esize : Int), 'esize in {8, 16, 32, 64}.
  (ReduceOp, bits(64), int('esize), bool) -> bits('esize)

function Reduce64 (op, input, esize, altfp) = {
    if esize == 64 then input else {
        let hi = Reduce32(op, Slice(input, 32, 32), esize, altfp);
        let lo = Reduce32(op, Slice(input, 0, 32), esize, altfp);
        ReduceCombine(op, lo, hi, altfp)
    }
}

val Reduce128 : forall ('esize : Int), 'esize in {8, 16, 32, 64}.
  (ReduceOp, bits(128), int('esize), bool) -> bits('esize)

function Reduce128 (op, input, esize, altfp) = {
    let hi = Reduce64(op, Slice(input, 64, 64), esize, altfp);
    let lo = Reduce64(op, Slice(input, 0, 64), esize, altfp);
    ReduceCombine(op, lo, hi, altfp)
}

val Reduce256 : forall ('esize : Int), 'esize in {8, 16, 32, 64}.
  (ReduceOp, bits(256), int('esize), bool) -> bits('esize)

function Reduce256 (op, input, esize, altfp) = {
    let hi = Reduce128(op, Slice(input, 128, 128), esize, altfp);
    let lo = Reduce128(op, Slice(input, 0, 128), esize, altfp);
    ReduceCombine(op, lo, hi, altfp)
}

val Reduce512 : forall ('esize : Int), 'esize in {8, 16, 32, 64}.
  (ReduceOp, bits(512), int('esize), bool) -> bits('esize)

function Reduce512 (op, input, esize, altfp) = {
    let hi = Reduce256(op, Slice(input, 256, 256), esize, altfp);
    let lo = Reduce256(op, Slice(input, 0, 256), esize, altfp);
    ReduceCombine(op, lo, hi, altfp)
}

val Reduce1024 : forall ('esize : Int), 'esize in {8, 16, 32, 64}.
  (ReduceOp, bits(1024), int('esize), bool) -> bits('esize)

function Reduce1024 (op, input, esize, altfp) = {
    let hi = Reduce512(op, Slice(input, 512, 512), esize, altfp);
    let lo = Reduce512(op, Slice(input, 0, 512), esize, altfp);
    ReduceCombine(op, lo, hi, altfp)
}

val Reduce2048 : forall ('esize : Int), 'esize in {8, 16, 32, 64}.
  (ReduceOp, bits(2048), int('esize), bool) -> bits('esize)

function Reduce2048 (op, input, esize, altfp) = {
    let hi = Reduce1024(op, Slice(input, 1024, 1024), esize, altfp);
    let lo = Reduce1024(op, Slice(input, 0, 1024), esize, altfp);
    ReduceCombine(op, lo, hi, altfp)
}

val Reduce__1 : forall 'N 'esize,
  ('N in {16, 32, 64, 128, 256, 512, 1024, 2048} & 'esize in {8, 16, 32, 64} & 'N >= 'esize).
  (ReduceOp, bits('N), int('esize), bool) -> bits('esize) effect {escape, rreg, undef, wreg}

function Reduce__1 (op, input, esize, altfp) = {
    match 'N {
	16 => Reduce16(op, input, esize, altfp),
	32 => Reduce32(op, input, esize, altfp),
	64 => Reduce64(op, input, esize, altfp),
	128 => Reduce128(op, input, esize, altfp),
	256 => Reduce256(op, input, esize, altfp),
	512 => Reduce512(op, input, esize, altfp),
	1024 => Reduce1024(op, input, esize, altfp),
	2048 => Reduce2048(op, input, esize, altfp)
    }
}

/* Ordinary definition, but with stricter type */
val Reduce : forall 'N 'esize,
  ('N in {16, 32, 64, 128, 256, 512, 1024, 2048} & 'esize in {8, 16, 32, 64} & 'N >= 'esize).
  (ReduceOp, bits('N), int('esize)) -> bits('esize) effect {escape, rreg, undef, wreg}

function Reduce (op, input, esize) = {
    let altfp : bool = (HaveAltFP() & not_bool(UsingAArch32())) & FPCR[1 .. 1] == 0b1;
    return(Reduce__1(op, input, esize, altfp))
}


val ReducePredicatedP2Fixed : forall ('M 'N 'esize 'p2bits : Int), 'p2bits in {16, 32, 64, 128, 256, 512, 1024, 2048} & 'esize in {8, 16, 32, 64} & 'p2bits >= 'esize & 'p2bits >= 'N.
  (ReduceOp, bits('N), bits('M), bits('esize), int('p2bits)) -> bits('esize) effect {escape, rreg, undef, wreg}

val ReducePredicated : forall ('M 'N 'esize : Int), 'esize in {8, 16, 32, 64} & 'N >= 'esize.
  (ReduceOp, bits('N), bits('M), bits('esize)) -> bits('esize) effect {escape, rreg, undef, wreg}

function ReducePredicated (op, input, mask, identity) = {
    let 'p2bits = CeilPow2('N);
    assert(constraint('p2bits >= 'N));
    match p2bits {
    16 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    32 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    64 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    128 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    256 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    512 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    1024 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    2048 => ReducePredicatedP2Fixed(op, input, mask, identity, p2bits),
    }
}

function ReducePredicatedP2Fixed (op, input, mask, identity, p2bits) = {
    assert('N == 'M * 8);
    operand : bits('p2bits) = undefined;
    let 'elements = DIV(p2bits, 'esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if e * 'esize < 'N & ElemP_read(mask, e, 'esize) == 0b1 then {
            assert(constraint((0 <= 'loop_e * 'esize & 'loop_e * 'esize <= 'loop_e * 'esize + 'esize - 1 | not(('loop_e >= 0 & ('loop_e + 1) * 'esize <= 'N)) | not('N == 'M * 8))));
            operand = Elem_set(operand, e, 'esize, Elem_read(input, e, 'esize))
        } else {
            assert(constraint((0 <= 'loop_e * 'esize & 'loop_e * 'esize <= ('loop_e + 1) * 'esize - 1 | not(('loop_e >= 0 & ('loop_e + 1) * 'esize <= 'p2bits)) | not('N == 'M * 8))));
            operand = Elem_set(operand, e, 'esize, identity)
        }
    };
    return(Reduce(op, operand, 'esize))
}
