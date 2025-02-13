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

default Order dec

$include <smt.sail>
$include <flow.sail>
$include <arith.sail>
$include <trace.sail>
$include <vector_dec.sail>
$include <string.sail>
$include <real.sail>
$include <reverse_endianness.sail>
$include <option.sail>
$include <mono_rewrites.sail>
$include <concurrency_interface.sail>

/* These could be given refined types, if necessary */
val implies : (bool, bool) -> bool
function implies(p,q) = not_bool(p) | q
infixr 1 -->
overload operator --> = {implies}

val iff : (bool, bool) -> bool
function iff(p,q) = implies(p,q) & implies(q,p)
infix 1 <-->
overload operator <--> = {iff}

val eq_any = pure {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool

val eq_bits_int : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), int('m)) -> bool
function eq_bits_int (x, y) = (unsigned(x) == y)

overload operator == = {eq_any, eq_bits_int}

val neq_any = pure {lem: "neq", coq: "generic_neq"} : forall ('a : Type). ('a, 'a) -> bool
function neq_any(x, y) = not_bool(x == y)

overload operator != = {neq_any}

val in_range : forall 'n 'i 'j. (int('n), int('i), int('j)) -> bool(('i < 'j & 'i <= 'n <= 'j) | ('i >= 'j & 'j <= 'n <= 'i))
function in_range(n, i, j) = if i < j then (i <= n & n <= j) else (j <= n & n <= i)

val min_real : (real, real) -> real
function min_real(n, m) = (if n <= m then n else m)

overload Min = {min_int, min_real}

val max_real : (real, real) -> real
function max_real(n, m) = (if n <= m then m else n)

overload Max = {max_int, max_real}

overload Abs = {abs_int_atom, abs_int_plain, abs_real}

val ediv_nat = pure {
  ocaml: "quotient",
  interpreter: "quotient",
  lem: "integerDiv",
  c: "ediv_int",
  coq: "ZEuclid.div"
} : forall 'n 'm, 'n >= 0 & 'm > 0. (int('n), int('m)) -> int(div('n, 'm))

val emod_nat = pure {
  ocaml: "modulus",
  interpreter: "modulus",
  lem: "integerMod",
  c: "emod_int",
  coq: "ZEuclid.modulo"
} : forall 'n 'm, 'n >= 0 & 'm > 0. (int('n), int('m)) -> int(mod('n, 'm))

overload DIV = {ediv_nat, fdiv_int}
overload MOD = {emod_nat, fmod_int}
overload QUOT = {tdiv_int}
overload REM = {tmod_int}

overload operator ^ = {pow_real}

overload Real = {to_real}

val UInt0 = pure {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_unsigned",
  coq: "uint"
} : forall 'n. bits('n) -> {'m, 0 <= 'm < 2 ^ 'n. int('m)}

val UInt1 = pure { coq: "uint" } : forall 'n. (int('n), bits('n)) -> {'m, 0 <= 'm < 2 ^ 'n. int('m)}
function UInt1(n, x) = unsigned(x)

overload UInt = {UInt0, UInt1}

val SInt0 = pure {
  c: "sail_signed",
  _: "sint"
} : forall 'n, 'n > 0. bits('n) -> {'m, - (2 ^ ('n - 1)) <= 'm < 2 ^ ('n - 1). int('m)}

val SInt1 : forall 'n, 'n > 0. (int('n), bits('n)) -> {'m, - (2 ^ ('n - 1)) <= 'm < 2 ^ ('n - 1). int('m)}
function SInt1(n, x) = signed(x)

overload SInt = {SInt0, SInt1}

val Replicate__1 : forall 'n 'm, 'n >= 0 & 'm > 0 & mod('n, 'm) == 0. (implicit('n), bits('m)) -> bits('n)
function Replicate__1(n, x) = replicate_bits(x, ediv_int(n, 'm))

overload Replicate = {replicate_bits, Replicate__1}

val Ones : forall 'n, 'n >= 0. implicit('n) -> bits('n)
function Ones(n) = sail_ones(n)

val Zeros : forall 'n, 'n >= 0. implicit('n) -> bits('n)
function Zeros(n) = sail_zeros(n)

val IsZero : forall 'n, 'n >= 0. bits('n) -> bool
function IsZero(x) = (x == sail_zeros('n))

val IsOnes : forall 'n, 'n >= 0. bits('n) -> bool
function IsOnes(x) = (x == sail_ones('n))

val Bit : bits(1) -> bit
function Bit(b) = b[0]

val Bits : bit -> bits(1)
function Bits(b) = (if b == bitone then 0b1 else 0b0)

val integer_subrange : forall 'hi 'lo, 'lo <= 'hi. (int, int('hi), int('lo)) -> bits('hi - 'lo + 1)
function integer_subrange(i, hi, lo) = get_slice_int(hi - lo + 1, i, lo)

overload vector_subrange = {integer_subrange}

val integer_access : forall 'n. (int, int('n)) -> bit
function integer_access(i, n) = (integer_subrange(i, n, n))[0]

overload vector_access = {integer_access}

val integer_update_subrange : forall 'm 'o, 0 <= 'o <= 'm. (int, int('m), int('o), bits('m - 'o + 1)) -> int
function integer_update_subrange(i, hi, lo, x) = set_slice_int(hi - lo + 1, i, lo, x)

overload vector_update_subrange = {integer_update_subrange}

val array_access = pure {
  ocaml: "access",
  interpreter: "access",
  lem: "access_list_inc",
  coq: "vec_access_inc",
  c: "vector_access"
} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n. (vector('n, inc, 'a), int('m)) -> 'a

overload vector_access = {array_access}

val array_update = pure {
  ocaml: "update",
  interpreter: "update",
  lem: "update_list_inc",
  coq: "vec_update_inc",
  c: "vector_update"
} : forall 'n 'm ('a : Type), 0 <= 'm < 'n. (vector('n, inc, 'a), int('m), 'a) -> vector('n, inc, 'a)

overload vector_update = {array_update}

val sub_bits_int = pure {c:"sub_bits_int", _: "sub_vec_int"} : forall 'n, 'n > 0. (bits('n), int) -> bits('n)

overload operator - = {sub_bits, sub_bits_int}

overload AND = {and_vec}
overload OR = {or_vec}
overload EOR = {xor_vec}

val SignExtend0 = pure "sign_extend" : forall 'n 'm, 'n > 0 & 'm >= 'n.
  (bits('n), int('m)) -> bits('m)

val SignExtend1 : forall 'n 'm, 'n > 0 & 'm >= 'n.
  (implicit('m), bits('n)) -> bits('m)
function SignExtend1(m, x) = SignExtend0(x, m)

overload SignExtend = {SignExtend0, SignExtend1}

val ZeroExtend0 = pure "zero_extend" : forall 'n 'm, 'n >= 0 & 'm >= 'n.
  (bits('n), int('m)) -> bits('m)

val ZeroExtend1 : forall 'n 'm, 'n >= 0 & 'm >= 'n.
  (implicit('m), bits('n)) -> bits('m)
function ZeroExtend1(m, x) = ZeroExtend0(x, m)

overload ZeroExtend = {ZeroExtend0, ZeroExtend1}

val Slice_int : forall 'w, 'w >= 0. (int, int, int('w)) -> bits('w)
function Slice_int(i, l, n) = get_slice_int(n, i, l)

overload Slice = {slice, Slice_int}

overload SetSlice = {set_slice_bits}

overload RoundDown = {floor}

overload RoundUp = {ceil}

val Align_int = pure { lem: "align_int" } : (int, int) -> int
function Align_int(x, y) = (DIV(x, y) * y)

val Align_bits = pure { lem: "align_bits" } : forall 'n, 'n >= 0. (bits('n), int) -> bits('n)
function Align_bits(x, y) = Slice(Align_int(unsigned(x), y), 0, sizeof('n))

overload Align = {Align_bits, Align_int}

val RoundTowardsZero : real -> int
function RoundTowardsZero(r) = if r < to_real(0) then RoundUp(r) else RoundDown(r)

enum signal = LOW | HIGH

infix 7 >>
infix 7 <<

overload operator << = {sail_shiftleft, _shl1, _shl8, _shl32, _shl_int, _shl_int_general}
overload operator >> = {sail_shiftright, _shr32, _shr_int, _shr_int_general}

union exception = {
  Error_Undefined : unit,
  Error_See : string,
  Error_ImplementationDefined : string,
  Error_ReservedEncoding : unit,
  Error_ExceptionTaken : unit,
  Error_Unpredictable : unit,
  Error_ConstrainedUnpredictable : unit,
  Error_SError : bool
}

val IsUNDEFINED : exception -> bool
val IsUNPREDICTABLE : exception -> bool
val IsSEE : exception -> bool
val IsExceptionTaken : exception -> bool
val IsSError : exception -> bool

function IsUNDEFINED ex = match ex { Error_Undefined() => true, _ => false }
function IsUNPREDICTABLE ex = match ex { Error_Unpredictable() => true, _ => false }
function IsSEE ex = match ex { Error_See(_) => true, _ => false }
function IsExceptionTaken ex = match ex { Error_ExceptionTaken() => true, _ => false }
function IsSError ex = match ex { Error_SError(_) => true, _ => false }

val ThrowSError : bool -> unit
function ThrowSError(iesb_req) = throw(Error_SError(iesb_req))

val ReservedEncoding : unit -> unit
function ReservedEncoding() = throw(Error_ReservedEncoding())

val PatternMatchFailure : forall ('a : Type). string -> 'a
function PatternMatchFailure(location) = {
  assert(false, concat_str("Pattern match failure in ", location));
  exit()
}

val DecStr = pure "dec_str" : int -> string

val HexStr = pure "hex_str" : int -> string

val BoolStr : bool -> string
function BoolStr b = match b { true => "true", false => "false" }

function append_int(str: string, n: int) -> string = {
  concat_str(str, DecStr(n))
}

function append_bool(str: string, b: bool) -> string = {
  concat_str(str, if b then "true" else "false")
}

infixl 4 ++

overload operator ++ = {append_int, append_bool, concat_str}

val print_integer : int -> unit
function print_integer(i) = print_int("", i)

val print_newline : unit -> unit
function print_newline () = print_endline("")

overload println = {print_endline, print_newline}

val putchar = pure {
  ocaml: "putchar",
  lem: "putchar",
  interpreter: "putchar",
  c: "sail_putchar",
  coq: "putchar"
} : int -> unit

val __IMPDEF_boolean : string -> bool
val __IMPDEF_integer : string -> int

val __UNKNOWN_bits : forall 'n, 'n >= 0. int('n) -> bits('n)
function __UNKNOWN_bits(n) = undefined

function __UNKNOWN_integer() : unit -> int = undefined
function __UNKNOWN_boolean() : unit -> bool = undefined
function __UNKNOWN_real() : unit -> real = undefined
function __UNKNOWN_string() : unit -> string = undefined
function __UNKNOWN_bit() : unit -> bits(1) = undefined
function __UNKNOWN_signal() : unit -> signal = undefined

/* From A1.4 ("Supported data types") of ARM DDI 0487J.a:
   "An SVE scalable vector register has an IMPLEMENTATION DEFINED width that
   is a power of two, from a minimum of 128 bits up to a maximum of 2048 bits." */
type is_VL('vl : Int) -> Bool = ('vl in {128, 256, 512, 1024, 2048})
/* "An SVE predicate register has an IMPLEMENTATION DEFINED width that is a
   power of two, from a minimum of 16 bits up to a maximum of 256 bits." */
type is_PL('pl : Int) -> Bool = ('pl in {16, 32, 64, 128, 256})

type vector_length = {'vl, is_VL('vl). int('vl)}
type predicate_length = {'pl, is_PL('pl). int('pl)}

val PL_of_VL : forall 'vl, 'vl >= 0. int('vl) -> int(div('vl, 8))

function PL_of_VL(vl) = DIV(vl, 8)

val __SleepRequest = monadic {ocaml: "sleep_request", lem: "sleep_request", smt: "sleep_request", interpreter: "sleep_request", c: "sleep_request"}: unit -> unit

val __WakeupRequest = monadic {ocaml: "wakeup_request", lem: "wakeup_request", smt: "wakeup_request", interpreter: "wakeup_request", c: "wakeup_request"}: unit -> unit

/* C emulator support functions */

val __GetVerbosity = monadic {c: "sail_get_verbosity"} : unit -> bits(64)
function __GetVerbosity() = 0x0000_0000_0000_0000

val check_cycle_count = monadic { c: "cycle_count" } : unit -> unit
function check_cycle_count() = ()

val get_cycle_count = monadic { c: "get_cycle_count" } : unit -> int
function get_cycle_count() = 0
