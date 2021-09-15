val sail_sign_extend = "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), int('m)) -> bits('m)

val SignExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0.
  (bits('M), int('N)) -> bits('N) effect {escape}

function SignExtend__0 (x, N) = {
    assert(N >= 'M);
    sail_sign_extend (x, N)
}
