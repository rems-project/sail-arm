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

val __SetConfig : forall 'value_name. (string, int('value_name)) -> unit

val __Reset : forall ('cold : Bool). bool('cold) -> unit

val __EndCycle : unit -> unit

val __ListConfig : unit -> unit

val EndOfInstruction : unit -> unit

function EndOfInstruction () = {
    throw(Error_ExceptionTaken())
}

val EncodingSpecificOperations : unit -> unit

function EncodingSpecificOperations () = {
    return()
}

val IsZeroBit : forall 'N, 'N >= 0. bits('N) -> bits(1)

function IsZeroBit x = {
    return(if IsZero(x) then 0b1 else 0b0)
}

val LSL_C : forall 'N 'shift. (bits('N), int('shift)) -> (bits('N), bits(1))

function LSL_C (x, shift) = {
    let carry_out = if shift > 0 & shift <= 'N then x['N - shift] else bitzero;
    (sail_shiftleft(x, shift), [carry_out])
}

overload LSL = {sail_shiftleft}

val LSR_C : forall 'N 'shift. (bits('N), int('shift)) -> (bits('N), bits(1))

function LSR_C (x, shift) = {
    let carry_out = if shift > 0 & shift <= 'N then x[shift - 1] else bitzero;
    (sail_shiftright(x, shift), [carry_out])
}

overload LSR = {sail_shiftright}

val ASR_C : forall 'N 'shift, ('N >= 0 & 'shift >= 0).
  (bits('N), int('shift)) -> (bits('N), bits(1))

function ASR_C (x, shift) = {
    let carry_out = if shift == 0 | 'N == 0 then bitzero else
      if shift >= 'N then x['N - 1] else x['shift - 1];
    (sail_arith_shiftright(x, shift), [carry_out])
}

overload ASR = {sail_arith_shiftright}

val ROR_C : forall 'N 'shift, 'N > 0.
  (bits('N), int('shift)) -> (bits('N), bits(1))

function ROR_C (x, shift) = {
    assert(shift > 0);
    let 'm = MOD(shift, 'N);
    let result : bits('N) = LSR(x, m) | LSL(x, 'N - m);
    let carry_out : bits(1) = [result['N - 1]];
    return((result, carry_out))
}

val ROR : forall 'N 'shift, ('N > 0 & 'shift >= 0).
  (bits('N), int('shift)) -> bits('N)

function ROR (x, shift) = {
    if shift == 0 then x else
      let 'm = MOD(shift, 'N) in LSR(x, m) | LSL(x, 'N - m)
}

val Extend : forall 'M 'N ('is_unsigned : Bool),
  ('M >= 0 & 'N >= 0).
  (bits('M), int('N), bool('is_unsigned)) -> bits('N)

function Extend (x, N, is_unsigned) = {
    return(if is_unsigned then {
        assert(constraint(('M >= 0 & 'N >= 'M)));
        ZeroExtend(x, N)
    } else {
        assert(constraint(('M > 0 & 'N >= 'M)));
        SignExtend(x, N)
    })
}

val asl_Int : forall 'N ('is_unsigned : Bool), 'N >= 0.
  (bits('N), bool('is_unsigned)) -> int

function asl_Int (x, is_unsigned) = {
    let 'result = if is_unsigned then UInt(x) else {
        assert(constraint('N > 0));
        SInt(x)
    };
    return(result)
}

val LowestSetBit : forall 'N, 'N >= 0. bits('N) -> int

function LowestSetBit x = {
    foreach (i from 0 to ('N - 1) by 1 in inc) {
        if [x[i]] == 0b1 then {
            return(i)
        };
        ()
    };
    return('N)
}

val HighestSetBit : forall 'N, 'N >= 0. bits('N) -> int

function HighestSetBit x = {
    foreach (i from ('N - 1) to 0 by 1 in dec) {
        if [x[i]] == 0b1 then {
            return(i)
        };
        ()
    };
    return(negate(1))
}

val BitCount : forall 'N, 'N >= 0. bits('N) -> int

function BitCount x = {
    result : int = 0;
    foreach (i from 0 to ('N - 1) by 1 in inc) {
        if [x[i]] == 0b1 then {
            result = result + 1
        };
        ()
    };
    let 'result = result;
    return(result)
}

val CountLeadingZeroBits : forall 'N, 'N >= 0. bits('N) -> int

function CountLeadingZeroBits x = {
    return('N - (HighestSetBit(x) + 1))
}

val CountLeadingSignBits : forall 'N, 1 <= 'N - 1. bits('N) -> int

function CountLeadingSignBits x = {
    return(CountLeadingZeroBits(EOR(x['N - 1 .. 1], x['N - 2 .. 0])))
}

val Elem_read : forall 'N 'e 'size,
  'N >= 0 & 'size >= 0 & ('e * 'size <= 'e * 'size + 'size - 1 | not(('e >= 0 & ('e + 1) * 'size <= 'N))).
  (bits('N), int('e), int('size)) -> bits('size)

function Elem_read (vector_name, e, size) = {
    assert(e >= 0 & (e + 1) * size <= 'N);
    return(vector_name[e * size + size - 1 .. e * size])
}

val Elem_set : forall 'N 'e 'size,
  'N >= 0 & 'size >= 0 & ('e * 'size <= ('e + 1) * 'size - 1 | not(('e >= 0 & ('e + 1) * 'size <= 'N))).
  (bits('N), int('e), int('size), bits('size)) -> bits('N)

function Elem_set (vector_name__arg, e, size, value_name) = {
    vector_name : bits('N) = vector_name__arg;
    assert(e >= 0 & (e + 1) * size <= 'N);
    vector_name[(e + 1) * size - 1 .. e * size] = value_name;
    return(vector_name)
}
