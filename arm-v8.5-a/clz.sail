val count_leading_zeros = "count_leading_zeros" : forall 'N , 'N >= 1. bits('N) -> {'n, 0 <= 'n <= 'N . atom('n)}
val CountLeadingZeroBits : forall ('N : Int), 'N >= 0. bits('N) -> int

function CountLeadingZeroBits x = {
    if 'N == 0 then 0 else count_leading_zeros(x)
}
