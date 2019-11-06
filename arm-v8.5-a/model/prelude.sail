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

default Order dec

infixr 1 -->

type operator -->('p: Bool, 'q: Bool) -> Bool = not('p) | 'q

infix 1 <-->

type operator <-->('p: Bool, 'q: Bool) -> Bool = ('p --> 'q) & ('q --> 'p)

$include <smt.sail>
$include <flow.sail>
$include <arith.sail>
$include <trace.sail>

$ifdef FEATURE_BITVECTOR_TYPE
type bits ('n : Int) = bitvector('n, dec)
$else
type bits('n : Int) = vector('n, dec, bit)
$endif

val eq_bit = {ocaml: "(fun (x, y) -> x = y)", lem: "eq", interpreter: "eq_anything", c: "eq_bit"} : (bit, bit) -> bool

val eq_vec = {ocaml: "eq_list", interpreter: "eq_list", lem: "eq_vec", c: "eq_bits"} : forall 'n. (bits('n), bits('n)) -> bool

val eq_string = {ocaml: "eq_string", interpreter: "eq_string", lem: "eq", c: "eq_string"} : (string, string) -> bool

val eq_real = {ocaml: "eq_real", interpreter: "eq_real", lem: "eq", c: "eq_real"} : (real, real) -> bool

val eq_anything = {
  ocaml: "(fun (x, y) -> x = y)",
  interpreter: "eq_anything",
  lem: "eq",
  c: "eq_anything"
} : forall ('a : Type). ('a, 'a) -> bool

val bitvector_length = "length" : forall 'n. bits('n) -> atom('n)
val vector_length = {ocaml: "length", interpreter: "length", lem: "length_list", c: "length"} : forall 'n ('a : Type). vector('n, dec, 'a) -> atom('n)
val list_length = {ocaml: "length", interpreter: "length", lem: "length_list", c: "length"} : forall ('a : Type). list('a) -> int

overload length = {bitvector_length, vector_length, list_length}

overload operator == = {eq_unit, eq_bit, eq_vec, eq_string, eq_real, eq_anything}

val vector_subrange_A = {
  ocaml: "subrange",
  interpreter: "subrange",
  lem: "subrange_vec_dec",
  c: "vector_subrange"
} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

val vector_subrange_B = {
  ocaml: "subrange",
  interpreter: "subrange",
  lem: "subrange_vec_dec",
  c: "vector_subrange"
} : forall ('n : Int) ('m : Int) ('o : Int).
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

overload vector_subrange = {vector_subrange_A, vector_subrange_B}

val bitvector_access_A = {
  ocaml: "access",
  interpreter: "access",
  lem: "access_vec_dec",
  c: "vector_access"
} : forall ('n : Int) ('m : Int), 0 <= 'm < 'n. (bits('n), atom('m)) -> bit

val bitvector_access_B = {
  ocaml: "access",
  interpreter: "access",
  lem: "access_vec_dec",
  c: "vector_access"
} : forall ('n : Int). (bits('n), int) -> bit

val vector_access_A = {
  ocaml: "access",
  interpreter: "access",
  lem: "access_list_dec",
  c: "vector_access"
} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n. (vector('n, dec, 'a), atom('m)) -> 'a

val vector_access_B = {
  ocaml: "access",
  interpreter: "access",
  lem: "access_list_dec",
  c: "vector_access"
} : forall ('n : Int) ('a : Type). (vector('n, dec, 'a), int) -> 'a

overload vector_access = {bitvector_access_A, bitvector_access_B, vector_access_A, vector_access_B}

val bitvector_update_B = {ocaml: "update", interpreter: "update", lem: "update_vec_dec", c: "vector_update"} : forall 'n.
  (bits('n), int, bit) -> bits('n)

val vector_update_B = {ocaml: "update", interpreter: "update", lem: "update_list_dec", c: "vector_update"} : forall 'n ('a : Type).
  (vector('n, dec, 'a), int, 'a) -> vector('n, dec, 'a)

overload vector_update = {bitvector_update_B, vector_update_B}

val vector_update_subrange = {
  ocaml: "update_subrange",
  interpreter: "update_subrange",
  lem: "update_subrange_vec_dec",
  c: "vector_update_subrange"
} : forall 'n 'm 'o. (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

val vcons : forall ('n : Int) ('a : Type).
  ('a, vector('n, dec, 'a)) -> vector('n + 1, dec, 'a)

val bitvector_concat = {ocaml: "append", interpreter: "append", lem: "concat_vec", c: "append"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)

val vector_concat = {ocaml: "append", interpreter: "append", lem: "append_list"} : forall ('n : Int) ('m : Int) ('a : Type).
  (vector('n, dec, 'a), vector('m, dec, 'a)) -> vector('n + 'm, dec, 'a)

overload append = {bitvector_concat, vector_concat}

val not_vec = {
  ocaml: "not_vec",
  interpreter: "not_vec",
  lem: "not_vec",
  c: "not_bits"
} : forall 'n. bits('n) -> bits('n)

overload ~ = {not_bool, not_vec}

val neq_vec = {lem: "neq_vec", c: "neq_bits"} : forall 'n. (bits('n), bits('n)) -> bool

function neq_vec (x, y) = not_bool(eq_vec(x, y))

val neq_anything = {lem: "neq"} : forall ('a : Type). ('a, 'a) -> bool

function neq_anything (x, y) = not_bool(x == y)

overload operator != = {neq_vec, neq_anything}

val builtin_and_vec = {ocaml: "and_vec", interpreter: "and_vec", c: "and_bits"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val and_vec = {lem: "and_vec", c: "and_bits"} : forall 'n. (bits('n), bits('n)) -> bits('n)

function and_vec (xs, ys) = builtin_and_vec(xs, ys)

overload operator & = {and_vec}

val builtin_or_vec = {ocaml: "or_vec", interpreter: "or_vec", c: "or_bits"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val or_vec = {lem: "or_vec", c: "or_bits"}: forall 'n. (bits('n), bits('n)) -> bits('n)

function or_vec (xs, ys) = builtin_or_vec(xs, ys)

overload operator | = {or_vec}

val UInt = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_unsigned"
} : forall 'n. bits('n) -> {'m, 0 <= 'm <= 2 ^ 'n - 1. int('m)}

val SInt = {
  c: "sail_signed",
  _: "sint"
} : forall 'n. bits('n) -> {'m, (- (2 ^ ('n - 1)) <= 'm <= 2 ^ ('n - 1) - 1). int('m)}

val hex_slice = "hex_slice" : forall 'n 'm. (string, atom('n), atom('m)) -> bits('n - 'm) effect {escape}

val __SetSlice_bits = "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)

val __SetSlice_int = "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_SetSlice_int : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_GetSlice_int = "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val __GetSlice_int : forall 'n. (atom('n), int, int) -> bits('n)

function __GetSlice_int (n, m, o) = __raw_GetSlice_int(n, m, o)

val __raw_SetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int, bits('w)) -> bits('n)

val __raw_GetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int) -> bits('w)

val __ShiftLeft = "shiftl" : forall 'm. (bits('m), int) -> bits('m)

val __SignExtendSlice = {lem: "exts_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val __ZeroExtendSlice = {lem: "extz_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val DecStr = "dec_str" : int -> string

val print = "print" : string -> unit
val asl_prerr_string = "prerr" : string -> unit

val asl_prerr_int : int -> unit
function asl_prerr_int(n) = {
  asl_prerr_string(DecStr(n))
}

overload prerr = {asl_prerr_string, asl_prerr_int}

val putchar = {
  ocaml: "putchar",
  lem: "putchar",
  interpreter: "putchar",
  c: "sail_putchar"
} : int -> unit

val concat_str = {ocaml: "concat_str", interpreter: "concat_str", lem: "stringAppend", c: "concat_str"} : (string, string) -> string

val HexStr = "hex_str" : int -> string

val BoolStr : bool -> string

function BoolStr(b) = if b then "true" else "false"

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val xor_vec = {
  ocaml: "xor_vec",
  lem: "xor_vec",
  c: "xor_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

val int_power = {lem: "pow"} : (int, int) -> int

val real_power = {ocaml: "real_power", interpreter: "real_power", lem: "realPowInteger", c: "real_power"} : (real, int) -> real

overload operator ^ = {xor_vec, int_power, real_power}

val add_vec = {
  ocaml: "add_vec",
  lem: "add_vec",
  c: "add_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_vec_int = {
  ocaml: "add_vec_int",
  lem: "add_vec_int",
  c: "add_bits_int"
} : forall 'n. (bits('n), int) -> bits('n)

val add_real = {ocaml: "add_real", interpreter: "add_real", lem: "realAdd", c: "add_real"} : (real, real) -> real

overload operator + = {add_vec, add_vec_int, add_real}

val sub_vec = {c: "sub_bits", _: "sub_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val sub_vec_int = {
  ocaml: "sub_vec_int",
  lem: "sub_vec_int",
  c: "sub_bits_int"
} : forall 'n. (bits('n), int) -> bits('n)

val sub_real = {ocaml: "sub_real", interpreter: "sub_real", lem: "realMinus", c: "sub_real"} : (real, real) -> real

val negate_real = {ocaml: "negate_real", interpreter: "negate_real", lem: "realNegate", c: "neg_real"} : real -> real

overload operator - = {sub_vec, sub_vec_int, sub_real}

overload negate = {negate_real}

val mult_real = {ocaml: "mult_real", interpreter: "mult_real", lem: "realMult", c: "mult_real"} : (real, real) -> real

overload operator * = {mult_real}

val Sqrt = {ocaml: "sqrt_real", interpreter: "sqrt_real", lem: "realSqrt", c: "sqrt_real"} : real -> real

val gteq_real = {ocaml: "gteq_real", interpreter: "gteq_real", lem: "gteq", c: "gteq_real"} : (real, real) -> bool

overload operator >= = {gteq_real}

val lteq_real = {ocaml: "lteq_real", interpreter: "lteq_real", lem: "lteq", c: "lteq_real"} : (real, real) -> bool

overload operator <= = {lteq_real}

val gt_real = {ocaml: "gt_real", interpreter: "gt_real", lem: "gt", c: "gt_real"} : (real, real) -> bool

overload operator > = {gt_real}

val lt_real = {ocaml: "lt_real", interpreter: "lt_real", lem: "lt", c: "lt_real"} : (real, real) -> bool

overload operator < = {lt_real}

val RoundDown = {ocaml: "round_down", interpreter: "round_down", lem: "realFloor", c: "round_down"} : real -> int

val RoundUp = {ocaml: "round_up", interpreter: "round_up", lem: "realCeiling", c: "round_up"} : real -> int

val abs_real = {ocaml: "abs_real", interpreter: "abs_real", lem: "realAbs", c: "abs_real"} : real -> real

overload abs = {abs_int, abs_real}

val quotient_nat = {ocaml: "quotient", interpreter: "quotient", lem: "integerDiv", c: "tdiv_int"} : (nat, nat) -> nat

val quotient_real = {ocaml: "quotient_real", interpreter: "quotient_real", lem: "realDiv", c: "div_real"} : (real, real) -> real

val quotient = {ocaml: "quotient", interpreter: "quotient", lem: "integerDiv", c: "tdiv_int"} : (int, int) -> int

overload operator / = {ediv_int, quotient_nat, quotient, quotient_real}

val modulus = {ocaml: "modulus", interpreter: "modulus", lem: "hardware_mod", c: "tmod_int" } :
  forall 'n, 'n >= 0. (int, int('n)) -> {'m, 0 <= 'm < 'n. int('m)}

//val modulus = {ocaml: "modulus", lem: "hardware_mod", c: "tmod_int"} : (int, int) -> int

overload operator % = {emod_int, modulus}

val Real = {ocaml: "to_real", interpreter: "to_real", lem: "realFromInteger", c: "to_real"} : int -> real

val min_nat = {ocaml: "min_int", interpreter: "min_int", lem: "integerMin", c: "min_int"} : (nat, nat) -> nat

val min_int = {ocaml: "min_int", interpreter: "min_int", lem: "integerMin", c: "min_int"} : (int, int) -> int

val max_nat = {ocaml: "max_int", interpreter: "max_int", lem: "integerMax", c: "max_int"} : (nat, nat) -> nat

val max_int = {ocaml: "max_int", interpreter: "max_int", lem: "integerMax", c: "max_int"} : (int, int) -> int

overload min = {min_nat, min_int}

overload max = {max_nat, max_int}

val print_bits = "print_bits" : forall 'n. (string, bits('n)) -> unit

val prerr_bits = "prerr_bits" : forall 'n. (string, bits('n)) -> unit

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)

val eq_bits_int : forall 'n, 'n in {0, 1}. (bits(1), int('n)) -> bool

function eq_bits_int(bv, n) = {
  match bv {
    0b0 if n == 0 => true,
    0b1 if n == 1 => true,
    _ => false
  }
}

val sail_zeros = "zeros" : forall 'n. int('n) -> bits('n)

val eq_bits_zero : forall 'n, 'n >= 0. (bits('n), int(0)) -> bool

function eq_bits_zero(bv, _) = bv == sail_zeros(length(bv))

overload operator == = {eq_bits_int, eq_bits_zero}

/*
val ex_range : forall 'n 'm.
  range('n, 'm) -> {'o, 'n <= 'o & 'o <= 'm. atom('o)}

val coerce_int_nat : int -> nat effect {escape}

function coerce_int_nat 'x = {
  assert(constraint('x >= 0), "Cannot coerce int to nat");
  x
}
*/

val slice = "slice" : forall ('n : Int) ('m : Int), 'm >= 0 & 'n >= 0.
  (bits('m), int, atom('n)) -> bits('n)

val pow2_atom = "pow2" : forall 'n. atom('n) -> atom(2 ^ 'n)
val pow2_int = "pow2" : int -> int

overload pow2 = {pow2_atom, pow2_int}

val break : unit -> unit

function break () = ()

union exception = {
  Error_Undefined : unit,
  Error_See : string,
  Error_Implementation_Defined : string,
  Error_ReservedEncoding : unit,
  Error_ExceptionTaken : unit,
  Error_Unpredictable : unit,
  Error_SError : bool
}

val append_str = {ocaml: "concat_str", interpreter: "concat_str", lem: "stringAppend", c: "concat_str" } :
  (string, string) -> string

function append_int(str: string, n: int) -> string = {
  append_str(str, DecStr(n))
}

function append_bool(str: string, b: bool) -> string = {
  append_str(str, if b then "true" else "false")
}

infixl 4 ++

overload operator ++ = {append_int, append_bool, append_str}

function __tarmacEvent(str: string) -> unit = {
  ()
}

val zero_vector : forall 'n. (implicit('n), int(0)) -> bits('n)

function zero_vector(n, _) = sail_zeros(n)

val __SleepRequest = {ocaml: "sleep_request", lem: "sleep_request", smt: "sleep_request", interpreter: "sleep_request", c: "sleep_request"}: unit -> unit effect {rreg, undef}

val __WakeupRequest = {ocaml: "wakeup_request", lem: "wakeup_request", smt: "wakeup_request", interpreter: "wakeup_request", c: "wakeup_request"}: unit -> unit effect {rreg, undef}

val __Sleeping = {ocaml: "sleeping", lem: "sleeping", smt: "sleeping", interpreter: "sleeping", c: "sleeping"}: unit -> bool effect {rreg, undef}

val __GetVerbosity = {c: "sail_get_verbosity"}: unit -> bits(64) effect {rreg, undef}

val get_cycle_count = { c: "get_cycle_count" } : unit -> int effect {undef, wreg, rreg, rmem, wmem}

/* Used for creating long bitvector literals in the C backend. */
val "append_64" : forall 'n. (bits('n), bits(64)) -> bits('n + 64)

overload __size = {length}
