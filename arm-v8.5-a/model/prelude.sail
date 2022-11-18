default Order dec

infixr 1 -->

type operator -->('p: Bool, 'q: Bool) -> Bool = not('p) | 'q

infix 1 <-->

type operator <-->('p: Bool, 'q: Bool) -> Bool = ('p --> 'q) & ('q --> 'p)

$define NO_SIGNED_UNSIGNED

$include <smt.sail>
$include <prelude.sail>
$include <string.sail>
$include <generic_equality.sail>
$include <real.sail>

val "one_if" : bool -> bits(1)

/* function one_if(b) = if b then 0b1 else 0b0 */

val "zero_if" : bool -> bits(1)

val min_nat = {ocaml: "min_int", interpreter: "min_int", lem: "integerMin", c: "min_int"} : (nat, nat) -> nat

val min_int = {ocaml: "min_int", interpreter: "min_int", lem: "integerMin", c: "min_int"} : (int, int) -> int

val max_nat = {ocaml: "max_int", interpreter: "max_int", lem: "integerMax", c: "max_int"} : (nat, nat) -> nat

val max_int = {ocaml: "max_int", interpreter: "max_int", lem: "integerMax", c: "max_int"} : (int, int) -> int

overload min = {min_nat, min_int}

overload max = {max_nat, max_int}

union exception = {
  Error_Undefined : unit,
  Error_See : string,
  Error_Implementation_Defined : string,
  Error_ReservedEncoding : unit,
  Error_ExceptionTaken : unit,
  Error_Unpredictable : unit,
  Error_SError : bool
}

function concat_str_bool(str: string, b: bool) -> string = {
    concat_str(str, if b then "true" else "false")
}

infixl 4 ++

overload operator ++ = {concat_str_bool, concat_str_dec, concat_str}

val UInt = pure {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_unsigned"
} : forall 'n. bits('n) -> {'m, 0 <= 'm <= 2 ^ 'n - 1. int('m)}

val SInt = pure {
  c: "sail_signed",
  _: "sint"
} : forall 'n. bits('n) -> {'m, (- (2 ^ ('n - 1)) <= 'm <= 2 ^ ('n - 1) - 1). int('m)}

val __SetSlice_bits = pure "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)

val __SetSlice_int = pure "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_SetSlice_int : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_GetSlice_int = pure "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val __GetSlice_int : forall 'n. (atom('n), int, int) -> bits('n)

function __GetSlice_int (n, m, o) = __raw_GetSlice_int(n, m, o)

val __raw_SetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int, bits('w)) -> bits('n)

val __raw_GetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int) -> bits('w)

val __ShiftLeft = pure "shiftl" : forall 'm. (bits('m), int) -> bits('m)

val __SignExtendSlice = pure {lem: "exts_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val __ZeroExtendSlice = pure {lem: "extz_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val __monomorphize = "monomorphize" : forall 'n, 'n >= 0. bits('n) -> bits('n)

val __mark_register = "mark_register" : forall ('a: Type). (register('a), string) -> unit
val __mark_register_pair = "mark_register_pair" : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit

val __ignore_write_to : forall ('a: Type). register('a) -> unit

function __ignore_write_to(reg) = __mark_register(reg, "ignore_write")

val DecStr = "dec_str" : int -> string

val HexStr = "hex_str" : int -> string

val BoolStr : bool -> string

function BoolStr(b) = if b then "true" else "false"

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val print = "print" : string -> unit
val asl_prerr_string = "prerr" : string -> unit

val asl_prerr_int : int -> unit
function asl_prerr_int(n) = {
  asl_prerr_string(dec_str(n))
}

overload prerr = {asl_prerr_string, asl_prerr_int}

val putchar = {
  ocaml: "putchar",
  lem: "putchar",
  interpreter: "putchar",
  c: "sail_putchar"
} : int -> unit

overload operator ^ = {xor_vec, int_power, pow_real}

overload ~ = {not_bool, not_vec}

val bitvector_access_weak = {
  ocaml: "access",
  interpreter: "access",
  lem: "access_vec_dec",
  c: "vector_access"
} : forall ('n : Int). (bits('n), int) -> bit

val vector_access_weak = {
  ocaml: "access",
  interpreter: "access",
  lem: "access_list_dec",
  c: "vector_access"
} : forall ('n : Int) ('a : Type). (vector('n, dec, 'a), int) -> 'a

overload vector_access = {vector_access_weak, bitvector_access_weak}

val bitvector_update_weak = {ocaml: "update", interpreter: "update", lem: "update_vec_dec", c: "vector_update"} : forall 'n.
  (bits('n), int, bit) -> bits('n)

val vector_update_weak = {ocaml: "update", interpreter: "update", lem: "update_list_dec", c: "vector_update"} : forall 'n ('a : Type).
  (vector('n, dec, 'a), int, 'a) -> vector('n, dec, 'a)

overload vector_update = {bitvector_update_weak, vector_update_weak}

val update_subrange_bits_weak = {
  ocaml: "update_subrange",
  interpreter: "update_subrange",
  lem: "update_subrange_vec_dec",
  c: "vector_update_subrange"
} : forall 'n 'm 'o. (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

overload vector_update_subrange = {update_subrange_bits_weak}

val quotient_nat = {ocaml: "quotient", interpreter: "quotient", lem: "integerDiv", c: "tdiv_int"} : (nat, nat) -> nat

val quotient_real = {ocaml: "quotient_real", interpreter: "quotient_real", lem: "realDiv", c: "div_real"} : (real, real) -> real

val quotient = {ocaml: "quotient", interpreter: "quotient", lem: "integerDiv", c: "tdiv_int"} : (int, int) -> int

overload operator / = {ediv_int, quotient_nat, quotient, quotient_real}

val modulus = {ocaml: "modulus", interpreter: "modulus", lem: "hardware_mod", c: "tmod_int" } :
  forall 'n, 'n >= 0. (int, int('n)) -> {'m, 0 <= 'm < 'n. int('m)}

overload operator % = {emod_int, modulus}

val "align_bits" : forall 'n 'm, 'n >= 0 & 'm >= 1. (bits('n), int('m)) -> bits('n)

val eq_bits_int : forall 'n, 'n in {0, 1}. (bits(1), int('n)) -> bool

function eq_bits_int(bv, n) = {
  match bv {
    0b0 if n == 0 => true,
    0b1 if n == 1 => true,
    _ => false
  }
}

val eq_bits_zero : forall 'n, 'n >= 0. (bits('n), int(0)) -> bool

function eq_bits_zero(bv, _) = bv == sail_zeros(length(bv))

overload operator == = {eq_bits_int, eq_bits_zero}

val sub_vec_int = {
  ocaml: "sub_vec_int",
  lem: "sub_vec_int",
  c: "sub_bits_int"
} : forall 'n. (bits('n), int) -> bits('n)

overload operator - = {sub_bits, sub_vec_int}

// ceil(m/n) = floor((m + n - 1) / n)
function cdiv_int(m: int, n: int) -> int =
  ((m + n) - 1) / n

val pow2_atom = "pow2" : forall 'n. int('n) -> int(2 ^ 'n)
val pow2_int = "pow2" : int -> int

overload pow2 = {pow2_atom, pow2_int}

overload RoundDown = {floor}
overload RoundUp = {ceil}
overload Real = {to_real}
overload Sqrt = {sqrt}
overload abs = {abs_int, abs_real}

val negate_real = {ocaml: "negate_real", interpreter: "negate_real", lem: "realNegate", c: "neg_real"} : real -> real

overload negate = {negate_real}

function __tarmacEvent(str: string) -> unit = {
  ()
}

val __SleepRequest : unit -> unit effect {rreg, undef}

function __SleepRequest() = ()

val __WakeupRequest : unit -> unit effect {rreg, undef}

function __WakeupRequest() = ()

val __Sleeping : unit -> bool effect {rreg, undef}

function __Sleeping() = {
  false
}
