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

val decode : bits(32) -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

scattered function decode
function clause decode (0b10011011001 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    U : bits(1) = [op_code[23]];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_widening_3264_decode(Rd, Rn, Ra, o0, Rm, U, op54, sf)
}

function clause decode (_ : bits(1) @ 0b1001011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_shiftedreg_decode(Rd, Rn, imm6, Rm, shift, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b010100111 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_preidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111100000 @ _ : bits(7) @ 0b01 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    h : bits(1) = [op_code[5]];
    g : bits(1) = [op_code[6]];
    f : bits(1) = [op_code[7]];
    e : bits(1) = [op_code[8]];
    d : bits(1) = [op_code[9]];
    o2 : bits(1) = [op_code[11]];
    cmode : bits(4) = op_code[15 .. 12];
    c : bits(1) = [op_code[16]];
    b : bits(1) = [op_code[17]];
    a : bits(1) = [op_code[18]];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_logical_decode(Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111100000 @ _ : bits(3) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    h : bits(1) = [op_code[5]];
    g : bits(1) = [op_code[6]];
    f : bits(1) = [op_code[7]];
    e : bits(1) = [op_code[8]];
    d : bits(1) = [op_code[9]];
    o2 : bits(1) = [op_code[11]];
    cmode : bits(4) = op_code[15 .. 12];
    c : bits(1) = [op_code[16]];
    b : bits(1) = [op_code[17]];
    a : bits(1) = [op_code[18]];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_fp16_movi_decode(Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q)
}

function clause decode (0b0110100100 @ _ : bits(22) as op_code) = {
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xt2 : bits(5) = op_code[14 .. 10];
    simm7 : bits(7) = op_code[21 .. 15];
    integer_tags_mcsettaganddatapair_decode(Xt, Xn, Xt2, simm7)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autib_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b0111111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mul_fp16_sisd_decode(Rd, Rn, H, opcode, Rm, M, L, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110011 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_truncating_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b01001000110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode (0b11010101000000110010001000011111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b11010101000000110011 @ _ : bits(4) @ 0b11011111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode (0b01111110110 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(5) @ 0b1110 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b011000 @ _ : bits(16) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    scale : bits(6) = op_code[15 .. 10];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_fix_decode(Rd, Rn, scale, opcode, rmode, typ, S, sf)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001111001100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_addsub_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (_ : bits(1) @ 0b0111010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode (0b10111000100 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_wrapping_pair_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b10011010110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_tags_mcinserttagmask_decode(Xd, Xn, Xm)
}

function clause decode (0b11010101000000110010000001011111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0110100101 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_offset_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b00001000110 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0101111010110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16maxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_integer_dup_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (_ : bits(1) @ 0b0010001 @ _ : bits(24) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_float_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101011000001110 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (_ : bits(2) @ 0b10110100 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b010111111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mul_fp_sisd_decode(Rd, Rn, H, opcode, Rm, M, L, sz, U)
}

function clause decode (0b00111000000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b01001000000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b00011111 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_addsub_decode(Rd, Rn, Ra, o0, Rm, o1, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_int_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b1001000110 @ _ : bits(22) as op_code) = {
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    uimm4 : bits(4) = op_code[13 .. 10];
    op3 : bits(2) = op_code[15 .. 14];
    uimm6 : bits(6) = op_code[21 .. 16];
    integer_tags_mcaddtag_decode(Xd, Xn, uimm4, op3, uimm6)
}

function clause decode (_ : bits(1) @ 0b1001011001 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm3 : bits(3) = op_code[12 .. 10];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opt : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_extendedreg_decode(Rd, Rn, imm3, option_name, Rm, opt, S, op, sf)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_int_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(5) @ 0b0000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_swp_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (_ : bits(1) @ 0b0111010010 @ _ : bits(9) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
    nzcv : bits(4) = op_code[3 .. 0];
    o3 : bits(1) = [op_code[4]];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_compare_immediate_decode(nzcv, o3, Rn, o2, cond, imm5, S, op, sf)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (0b10111000100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b01111000000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111010110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16max_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode (_ : bits(1) @ 0b0001011001 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm3 : bits(3) = op_code[12 .. 10];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opt : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_extendedreg_decode(Rd, Rn, imm3, option_name, Rm, opt, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111100000 @ _ : bits(6) @ 0b101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    h : bits(1) = [op_code[5]];
    g : bits(1) = [op_code[6]];
    f : bits(1) = [op_code[7]];
    e : bits(1) = [op_code[8]];
    d : bits(1) = [op_code[9]];
    o2 : bits(1) = [op_code[11]];
    cmode : bits(4) = op_code[15 .. 12];
    c : bits(1) = [op_code[16]];
    b : bits(1) = [op_code[17]];
    a : bits(1) = [op_code[18]];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_logical_decode(Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_2008_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011011000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    op31 : bits(3) = op_code[23 .. 21];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_uniform_addsub_decode(Rd, Rn, Ra, o0, Rm, op31, op54, sf)
}

function clause decode (0b00001000100 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0101111000110000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16add_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b0111111011111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100000110000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode (0b01111111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    S : bits(1) = [op_code[13]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_high_sisd_decode(Rd, Rn, H, S, Rm, M, L, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100001110000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b110 @ _ : bits(2) @ 0b1 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rot : bits(2) = op_code[12 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_complex_decode(Rd, Rn, rot, Rm, size, U, Q)
}

function clause decode (0b11010101000000110010000000011111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111000110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16maxnm_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode (0b0101111001111001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size_1_ : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, size_1_, U)
}

function clause decode (0b00011001001 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairpre_decode(Rt, Xn, imm9)
}

function clause decode (0b00001000000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b00011001101 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairandzerodatapost_decode(Rt, Xn, imm9)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_extract_sqxtun_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110000101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode(Rd, Rn, S, Rm, size, U, Q)
}

function clause decode (0b01011110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1hash_majority_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_addsub_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    P : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha256hash_decode(Rd, Rn, P, Rm, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode(Rd, Rn, o1, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmax_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b000010001 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_cas_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b11010101000000110011 @ _ : bits(4) @ 0b01011111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_monitors_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_int_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b01 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
    nzcv : bits(4) = op_code[3 .. 0];
    op : bits(1) = [op_code[4]];
    Rn : bits(5) = op_code[9 .. 5];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_compare_cond_decode(nzcv, op, Rn, cond, Rm, typ, S, M)
}

function clause decode (_ : bits(1) @ 0b1101011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_shiftedreg_decode(Rd, Rn, imm6, Rm, shift, S, op, sf)
}

function clause decode (0b0101111011111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size_1_ : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_recip_fp16_sisd_decode(Rd, Rn, opcode, size_1_, U)
}

function clause decode (0b110101010001 @ _ : bits(20) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    o0 : bits(1) = [op_code[19]];
    L : bits(1) = [op_code[21]];
    system_register_system_decode(Rt, op2, CRm, CRn, op1, o0, L)
}

function clause decode (0b01111111 @ _ : bits(8) @ 0b1111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    S : bits(1) = [op_code[13]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_high_sisd_decode(Rd, Rn, H, S, Rm, M, L, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_fp_simd_decode(Rd, Rn, H, opcode, Rm, M, L, sz, U, Q)
}

function clause decode (_ : bits(1) @ 0b1111010010 @ _ : bits(9) @ 0b00 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
    nzcv : bits(4) = op_code[3 .. 0];
    o3 : bits(1) = [op_code[4]];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_compare_register_decode(nzcv, o3, Rn, o2, cond, Rm, S, op, sf)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (_ : bits(1) @ 0b0011010100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_select_decode(Rd, Rn, o2, cond, Rm, S, op, sf)
}

function clause decode (0b10011000 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_general_decode(Rt, imm19, V, opc)
}

function clause decode (_ : bits(1) @ 0b1011010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp_simd_decode(Rd, Rn, ac, Rm, sz, E, U, Q)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b10 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_offset_normal_memory_single_simdfp_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b11010101000000110011 @ _ : bits(4) @ 0b10111111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode (0b0100111000101000011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_mix_decode(Rd, Rn, D, size)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autdb_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_int_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000001 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    sz : bits(1) = [op_code[30]];
    memory_exclusive_pair_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, sz)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4_0_ : bits(1) = [op_code[11]];
    imm4_1_ : bits(1) = [op_code[12]];
    imm4_3_2_ : bits(2) = op_code[14 .. 13];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_integer_move_unsigned_decode(Rd, Rn, imm4_0_, imm4_1_, imm4_3_2_, imm5, op, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_fused_decode(Rd, Rn, opcode, Rm, sz, op, U, Q)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha256sched1_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_rsqrtsfp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b1101011 @ _ : bits(1) @ 0b0001111100001 @ _ : bits(11) as op_code) = {
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(5) @ 0b0100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b1101010100000 @ _ : bits(3) @ 0b0100 @ _ : bits(7) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_register_cpsr_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_xtn_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (_ : bits(1) @ 0b1111010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp_simd_decode(Rd, Rn, ac, Rm, sz, E, U, Q)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b11100101 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    imm16 : bits(16) = op_code[20 .. 5];
    hw : bits(2) = op_code[22 .. 21];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_insext_insert_movewide_decode(Rd, imm16, hw, opc, sf)
}

function clause decode (0b0101111100 @ _ : bits(6) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_fp16_sisd_decode(Rd, Rn, H, o2, Rm, M, L, size, U)
}

function clause decode (0b00111000010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b010111111 @ _ : bits(7) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_fp_sisd_decode(Rd, Rn, H, o2, Rm, M, L, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b0110100 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    op : bits(1) = [op_code[24]];
    sf : bits(1) = [op_code[31]];
    branch_conditional_compare_decode(Rt, imm19, op, sf)
}

function clause decode (0b10011011101 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    U : bits(1) = [op_code[23]];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_widening_3264_decode(Rd, Rn, Ra, o0, Rm, U, op54, sf)
}

function clause decode (0b10111000101 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000011 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b01011110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b01 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_register_memory_single_simdfp_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110101000000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_add_saturating_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110111 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_fp16_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (_ : bits(1) @ 0b1110001 @ _ : bits(24) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode (_ : bits(1) @ 0b010100010 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_postidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0100111000101000010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_round_decode(Rd, Rn, D, size)
}

function clause decode (0b0101111011111000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_recpsfp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b0101111011111001111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_frecpxfp16_decode(Rd, Rn, opcode, a, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000000110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rev_decode(Rd, Rn, o0, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_product_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_fused_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_lessthan_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0101111000101000000010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha2op_sha1hash_decode(Rd, Rn, opcode, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtest_int_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100000000000100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (_ : bits(1) @ 0b01100100 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000000010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rev_decode(Rd, Rn, o0, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b000110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_unzip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode (_ : bits(1) @ 0b010100000 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_noalloc_memory_pair_general_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (_ : bits(2) @ 0b10110101 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b011001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftsat_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b000010 @ _ : bits(16) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    scale : bits(6) = op_code[15 .. 10];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_fix_decode(Rd, Rn, scale, opcode, rmode, typ, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110100100000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_cpydup_simd_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode (0b000101 @ _ : bits(26) as op_code) = {
    imm26 : bits(26) = op_code[25 .. 0];
    op : bits(1) = [op_code[31]];
    branch_unconditional_immediate_decode(imm26, op)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_2008_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b011001 @ _ : bits(16) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    scale : bits(6) = op_code[15 .. 10];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_fix_decode(Rd, Rn, scale, opcode, rmode, typ, S, sf)
}

function clause decode (0b00001000110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b101001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftlong_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode (_ : bits(2) @ 0b10110110 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_extended_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b11010101000000110010000010111111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_saturating_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b101101011000000000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[10]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_cnt_decode(Rd, Rn, op, opcode2, S, sf)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    P : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha256hash_decode(Rd, Rn, P, Rm, size)
}

function clause decode (0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b10011011001 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    U : bits(1) = [op_code[23]];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_widening_3264_decode(Rd, Rn, Ra, o0, Rm, U, op54, sf)
}

function clause decode (_ : bits(1) @ 0b0110111 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm14 : bits(14) = op_code[18 .. 5];
    b40 : bits(5) = op_code[23 .. 19];
    op : bits(1) = [op_code[24]];
    b5 : bits(1) = [op_code[31]];
    branch_conditional_test_decode(Rt, imm14, b40, op, b5)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_transpose_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0111100101 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_nonuniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111000111010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_lessthan_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000011 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    sz : bits(1) = [op_code[30]];
    memory_exclusive_pair_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, sz)
}

function clause decode (0b10111000100 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001111001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b0001010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_zip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b0100 @ _ : bits(12) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    sz : bits(2) = op_code[11 .. 10];
    C : bits(1) = [op_code[12]];
    opcode2_5_3_ : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_crc_decode(Rd, Rn, sz, C, opcode2_5_3_, Rm, S, op, sf)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_float_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftsat_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b011000 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_general_decode(Rt, imm19, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101010000001110 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000001 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    sz : bits(1) = [op_code[30]];
    memory_exclusive_pair_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, sz)
}

function clause decode (0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_left_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (_ : bits(1) @ 0b0110001 @ _ : bits(24) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (0b00001000010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_recip_float_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_int_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111001111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b101001000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111001100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b11010101000000110011 @ _ : bits(4) @ 0b10011111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_nosat_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp16_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b010001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightinsert_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autda_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (0b1 @ _ : bits(1) @ 0b11100100 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101101 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (_ : bits(1) @ 0b1101010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b10011001100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_fp_simd_decode(Rd, Rn, H, o2, Rm, M, L, sz, U, Q)
}

function clause decode (0b0111111011111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_sqrtest_fp16_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode (_ : bits(1) @ 0b0101010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000101 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_orderedrcpc_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0110100110 @ _ : bits(22) as op_code) = {
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xt2 : bits(5) = op_code[14 .. 10];
    simm7 : bits(7) = op_code[21 .. 15];
    integer_tags_mcsettaganddatapairpre_decode(Xt, Xn, Xt2, simm7)
}

function clause decode (0b00001000010 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b01111000010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100011000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_extract_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp_simd_decode(Rd, Rn, ac, Rm, sz, E, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_divfp16_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b00011001100 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagandzerodatapre_decode(Rt, Xn, imm9)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_nonuniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (0b00011111 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_addsub_decode(Rd, Rn, Ra, o0, Rm, o1, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111000100000010110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_not_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_tieaway_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b11010110101111110000001111100000 as op_code) = {
    op4 : bits(5) = op_code[4 .. 0];
    Rt : bits(5) = op_code[9 .. 5];
    op3 : bits(6) = op_code[15 .. 10];
    op2 : bits(5) = op_code[20 .. 16];
    opc : bits(4) = op_code[24 .. 21];
    branch_unconditional_dret_decode(op4, Rt, op3, op2, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[23]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower_decode(Rd, Rn, Rm, sz, S, Q)
}

function clause decode (_ : bits(1) @ 0b0011011000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    op31 : bits(3) = op_code[23 .. 21];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_uniform_addsub_decode(Rd, Rn, Ra, o0, Rm, op31, op54, sf)
}

function clause decode (0b00011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b00011001010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcgettag_decode(Xt, Xn, imm9)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100010000001000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (0b01011111 @ _ : bits(8) @ 0b0111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_double_sisd_decode(Rd, Rn, H, o2, Rm, M, L, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b111 @ _ : bits(1) @ 0b01 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rot : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp_complex_decode(Rd, Rn, rot, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(2) @ 0b011100 @ _ : bits(1) @ 0b100001111 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_frint_32_64_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_div_decode(Rd, Rn, opcode, Rm, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0010000 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    sz : bits(1) = [op_code[30]];
    memory_atomicops_cas_pair_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, sz)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111000110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16max_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b00001000100 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op2 : bits(2) = op_code[11 .. 10];
    opcode2_5_2_ : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_shift_variable_decode(Rd, Rn, op2, opcode2_5_2_, Rm, S, op, sf)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b101001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftlong_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_widen_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (_ : bits(2) @ 0b011100 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_simdfp_decode(Rt, imm19, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_fp16_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_disparate_mul_double_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmax_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp16_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100100010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b1010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_long_decode(Rd, Rn, H, opcode, Rm, M, L, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b110001000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_int_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b01011001110 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b1101011000111111000000 @ _ : bits(5) @ 0b00000 as op_code) = {
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[23]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper_decode(Rd, Rn, Rm, sz, S, Q)
}

function clause decode (_ : bits(1) @ 0b0011010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode (_ : bits(1) @ 0b00100111 @ _ : bits(1) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    o0 : bits(1) = [op_code[21]];
    N : bits(1) = [op_code[22]];
    op21 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_insext_extract_immediate_decode(Rd, Rn, imms, Rm, o0, N, op21, sf)
}

function clause decode (0b0011100100 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (_ : bits(1) @ 0b010100011 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_postidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b01111000001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b11010100101 @ _ : bits(16) @ 0b00001 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_exception_decode(LL, op2, imm16, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftinsert_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode (0b1101000110 @ _ : bits(22) as op_code) = {
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    uimm4 : bits(4) = op_code[13 .. 10];
    op3 : bits(2) = op_code[15 .. 14];
    uimm6 : bits(6) = op_code[21 .. 16];
    integer_tags_mcsubtag_decode(Xd, Xn, uimm4, op3, uimm6)
}

function clause decode (_ : bits(1) @ 0b010100100 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_offset_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100001010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_logical_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111001111001100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (0b0110100111 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_preidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b11010101000000000100 @ _ : bits(4) @ 0b00111111 as op_code) = {
    CRm : bits(4) = op_code[11 .. 8];
    integer_flags_xaflag_decode(CRm)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b01011111 @ _ : bits(8) @ 0b0011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_double_sisd_decode(Rd, Rn, H, o2, Rm, M, L, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101101 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b01111110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode (0b10011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_rounding_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (_ : bits(2) @ 0b111101 @ _ : bits(1) @ 0b0 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_zip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0100111000101000010110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_round_decode(Rd, Rn, D, size)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_int_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110001 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b01111000000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode (0b0101111001111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_long_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp_simd_decode(Rd, Rn, ac, Rm, sz, E, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b0101011001 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm3 : bits(3) = op_code[12 .. 10];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opt : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_extendedreg_decode(Rd, Rn, imm3, option_name, Rm, opt, S, op, sf)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0111111001111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (_ : bits(1) @ 0b1010001 @ _ : bits(24) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode (0b1 @ _ : bits(2) @ 0b10000 @ _ : bits(24) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    immhi : bits(19) = op_code[23 .. 5];
    immlo : bits(2) = op_code[30 .. 29];
    op : bits(1) = [op_code[31]];
    integer_arithmetic_address_pcrel_decode(Rd, immhi, immlo, op)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100100110000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101011000001100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b10011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111001111001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (0b00001000000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100000000000000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_recps_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(8) @ 0b10000000 @ _ : bits(5) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    imm5 : bits(5) = op_code[9 .. 5];
    imm8 : bits(8) = op_code[20 .. 13];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_move_fp_imm_decode(Rd, imm5, imm8, typ, S, M)
}

function clause decode (0b0101111001111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_int_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(5) @ 0b0000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101100 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1000 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_int_decode(Rd, Rn, H, opcode, Rm, M, L, size, U, Q)
}

function clause decode (0b11001110100 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    vector_crypto_sha3_xar_decode(Rd, Rn, imm6, Rm)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b011110011 @ _ : bits(23) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (_ : bits(1) @ 0b00100110 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_bitfield_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    S : bits(1) = [op_code[13]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_high_simd_decode(Rd, Rn, H, S, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode(Rd, Rn, S, Rm, size, U, Q)
}

function clause decode (0b01111000010 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_div_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101010000001100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1100 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    op : bits(1) = [op_code[12]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_high_simd_decode(Rd, Rn, H, op, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b01111110010 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_fused_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110101100000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b00111000000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_product_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (_ : bits(1) @ 0b0011010100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_select_decode(Rd, Rn, o2, cond, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftsat_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b101000000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b00011001101 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairandzerodata_decode(Rt, Xn, imm9)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0000 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_int_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b1101101011000000000010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[11 .. 10];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rev_decode(Rd, Rn, opc, opcode2, S, sf)
}

function clause decode (0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (_ : bits(2) @ 0b10110010 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b010100110 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_preidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmaxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100010000000100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (0b01011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b11010101000000110010000010011111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[10]];
    opcode2_5_1_ : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_div_decode(Rd, Rn, o1, opcode2_5_1_, Rm, S, op, sf)
}

function clause decode (0b00111000011 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101100 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b0111111001111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_int_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_rsqrts_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtest_float_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (_ : bits(1) @ 0b1011010100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_select_decode(Rd, Rn, o2, cond, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b0 @ _ : bits(1) @ 0b000 as op_code) = {
    opc : bits(2) = op_code[4 .. 3];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[15 .. 14];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_compare_uncond_decode(opc, Rn, op, Rm, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_transpose_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode (_ : bits(1) @ 0b0110110 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm14 : bits(14) = op_code[18 .. 5];
    b40 : bits(5) = op_code[23 .. 19];
    op : bits(1) = [op_code[24]];
    b5 : bits(1) = [op_code[31]];
    branch_conditional_test_decode(Rt, imm14, b40, op, b5)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_fp_simd_decode(Rd, Rn, H, o2, Rm, M, L, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110100000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1sched0_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (0b0101111100 @ _ : bits(6) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_fp16_sisd_decode(Rd, Rn, H, o2, Rm, M, L, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b010110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_unzip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111001111001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(5) @ 0b1110 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b10011011110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    U : bits(1) = [op_code[23]];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_widening_64128hi_decode(Rd, Rn, Ra, o0, Rm, U, op54, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111100 @ _ : bits(6) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_fp16_simd_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op2 : bits(2) = op_code[11 .. 10];
    opcode2_5_2_ : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_shift_variable_decode(Rd, Rn, op2, opcode2_5_2_, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110101 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_double_simd_decode(Rd, Rn, H, opcode, Rm, M, L, size, U, Q)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b1101010100000010001001 @ _ : bits(10) as op_code) = {
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    integer_tags_mcgettagarray_decode(Xt, Xn)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_narrow_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_recip_int_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    op : bits(1) = [op_code[12]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_high_simd_decode(Rd, Rn, H, op, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_extended_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b111000000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (_ : bits(1) @ 0b10100101 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    imm16 : bits(16) = op_code[20 .. 5];
    hw : bits(2) = op_code[22 .. 21];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_insext_insert_movewide_decode(Rd, imm16, hw, opc, sf)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_int_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrt_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_2008_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(5) @ 0b1100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100110010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_float_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b01010100 @ _ : bits(19) @ 0b0 @ _ : bits(4) as op_code) = {
    cond : bits(4) = op_code[3 .. 0];
    o0 : bits(1) = [op_code[4]];
    imm19 : bits(19) = op_code[23 .. 5];
    o1 : bits(1) = [op_code[24]];
    branch_conditional_cond_decode(cond, o0, imm19, o1)
}

function clause decode (0b0101111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mul_fp16_sisd_decode(Rd, Rn, H, opcode, Rm, M, L, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b011001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftsat_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b11 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_register_memory_single_simdfp_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(5) @ 0b1000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b01001110000 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_integer_insert_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmax_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (_ : bits(2) @ 0b10110001 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b001110001 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b0 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    S : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower_decode(Rd, Rn, H, S, Rm, M, L, sz, Q)
}

function clause decode (0b00011111 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_addsub_decode(Rd, Rn, Ra, o0, Rm, o1, typ, S, M)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b00 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_1985_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (0b10111000100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b01111000000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_product_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (0b1101010100000011001000 @ _ : bits(1) @ 0b100 @ _ : bits(1) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_pacia_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b110000000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b1 @ _ : bits(1) @ 0b000 as op_code) = {
    opc : bits(2) = op_code[4 .. 3];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[15 .. 14];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_compare_uncond_decode(opc, Rn, op, Rm, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b1101011001011111000000 @ _ : bits(5) @ 0b00000 as op_code) = {
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b10001 @ _ : bits(2) @ 0b10000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_convert_fp_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000010 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_clsz_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b00011001001 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairpost_decode(Rt, Xn, imm9)
}

function clause decode (0b00111000000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacib_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b10 @ _ : bits(1) @ 0b11 @ _ : bits(1) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b1 @ _ : bits(1) @ 0b11100101 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_fp_simd_decode(Rd, Rn, H, opcode, Rm, M, L, sz, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000100 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_long_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b11011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_fp16_simd_decode(Rd, Rn, H, opcode, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b00111000010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b0 @ _ : bits(2) @ 0b000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    len : bits(2) = op_code[14 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    op2 : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_table_decode(Rd, Rn, op, len, Rm, op2, Q)
}

function clause decode (_ : bits(1) @ 0b00100101 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    imm16 : bits(16) = op_code[20 .. 5];
    hw : bits(2) = op_code[22 .. 21];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_insext_insert_movewide_decode(Rd, imm16, hw, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode (0b11010100101 @ _ : bits(16) @ 0b00010 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_exception_decode(LL, op2, imm16, opc)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode(Rd, Rn, o1, Rm, size, U)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_sqxtun_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b00111000101 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_orderedrcpc_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_nonuniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001100000010110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rbit_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1hash_choose_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtest_fp16_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (0b11010100000 @ _ : bits(16) @ 0b00010 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_runtime_hvc_decode(LL, op2, imm16, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_fused_decode(Rd, Rn, opcode, Rm, sz, op, U, Q)
}

function clause decode (0b00011001000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettag_decode(Rt, Xn, imm9)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b10011010110 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_arithmetic_pointer_mcsubtracttaggedaddress_decode(Xd, Xn, Xm)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    rot : bits(2) = op_code[14 .. 13];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_complex_decode(Rd, Rn, H, rot, Rm, M, L, size, U, Q)
}

function clause decode (0b0101111011111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_dmacc_simd_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011111 @ _ : bits(7) @ 0b1 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    S : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_mul_norounding_i_upper_decode(Rd, Rn, H, S, Rm, M, L, sz, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_swp_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110001 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b00 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_offset_normal_memory_single_simdfp_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b01111000010 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110000001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_addlong_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111001111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtfp16_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_int_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_recip_fp16_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (_ : bits(1) @ 0b10100100 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode (0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode (_ : bits(2) @ 0b10110011 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b00011001100 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagandzerodata_decode(Rt, Xn, imm9)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmax_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_product_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111011111001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b11010101000000110010 @ _ : bits(7) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110101000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b010010001 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_cas_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b100101 @ _ : bits(26) as op_code) = {
    imm26 : bits(26) = op_code[25 .. 0];
    op : bits(1) = [op_code[31]];
    branch_unconditional_immediate_decode(imm26, op)
}

function clause decode (0b01111000010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_xtn_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacia_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1hash_parity_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode (0b0101111000101000001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha2op_sha256sched0_decode(Rd, Rn, opcode, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b1111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    S : bits(1) = [op_code[13]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_high_simd_decode(Rd, Rn, H, S, Rm, M, L, size, U, Q)
}

function clause decode (0b1101010100000010001000 @ _ : bits(10) as op_code) = {
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    integer_tags_mcsettagarray_decode(Xt, Xn)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b100000101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_lessthan_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100010000000000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_float_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode (0b11010101000000000100 @ _ : bits(4) @ 0b01011111 as op_code) = {
    CRm : bits(4) = op_code[11 .. 8];
    integer_flags_axflag_decode(CRm)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_accum_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100010000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (_ : bits(1) @ 0b00100100 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_1985_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (_ : bits(1) @ 0b1111010010 @ _ : bits(9) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
    nzcv : bits(4) = op_code[3 .. 0];
    o3 : bits(1) = [op_code[4]];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_compare_immediate_decode(nzcv, o3, Rn, o2, cond, imm5, S, op, sf)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100000111010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_lessthan_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000100 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b111001000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b11010101000000110010001000111111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b1101010100101 @ _ : bits(19) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_sysops_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b00011001100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_product_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_saturating_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_double_simd_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b111000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_poly_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100111010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110000000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (0b11111000 @ _ : bits(2) @ 0b1 @ _ : bits(10) @ 0b1 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    W : bits(1) = [op_code[11]];
    imm9 : bits(9) = op_code[20 .. 12];
    S : bits(1) = [op_code[22]];
    M : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_pac_decode(Rt, Rn, W, imm9, S, M, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (0b1101010100001 @ _ : bits(19) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_sysops_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b1101011000011111000000 @ _ : bits(5) @ 0b00000 as op_code) = {
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b01011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (0b0101111011111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (_ : bits(1) @ 0b101101011000000000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rbit_decode(Rd, Rn, opcode2, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_product_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_1985_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b1101011 @ _ : bits(1) @ 0b0011111100001 @ _ : bits(11) as op_code) = {
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftinsert_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b011111111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mul_fp_sisd_decode(Rd, Rn, H, opcode, Rm, M, L, sz, U)
}

function clause decode (0b01011110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_recpsfp16_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b1101010100000011001000 @ _ : bits(1) @ 0b101 @ _ : bits(1) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_pacib_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_long_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b11010100010 @ _ : bits(16) @ 0b00000 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_halt_decode(LL, op2, imm16, opc)
}

function clause decode (0b11010101000000110010000000111111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (_ : bits(1) @ 0b11100100 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_nonuniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b10 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_preidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_recps_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b11011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (_ : bits(1) @ 0b1101010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b01 @ _ : bits(5) @ 0b1 @ _ : bits(4) as op_code) = {
    nzcv : bits(4) = op_code[3 .. 0];
    op : bits(1) = [op_code[4]];
    Rn : bits(5) = op_code[9 .. 5];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_compare_cond_decode(nzcv, op, Rn, cond, Rm, typ, S, M)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_left_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100001111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_frecpx_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b0011100101 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0100 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_int_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b0111111001111001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size_1_ : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, size_1_, U)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000011 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    sz : bits(1) = [op_code[30]];
    memory_exclusive_pair_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, sz)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110100100000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode (0b11010101000000000100000000011111 as op_code) = {
    CRm : bits(4) = op_code[11 .. 8];
    integer_flags_cfinv_decode(CRm)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b110000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpadd_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b00111000010 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b10011010110 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_tags_mcinsertrandomtag_decode(Xd, Xn, Xm)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111001111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_int_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (_ : bits(1) @ 0b0001011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_shiftedreg_decode(Rd, Rn, imm6, Rm, shift, S, op, sf)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode (_ : bits(1) @ 0b1011010100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_select_decode(Rd, Rn, o2, cond, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111010110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16maxnm_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode (0b10011010110 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacga_dp_2src_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(2) @ 0b0111100000 @ _ : bits(3) @ 0b111101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    h : bits(1) = [op_code[5]];
    g : bits(1) = [op_code[6]];
    f : bits(1) = [op_code[7]];
    e : bits(1) = [op_code[8]];
    d : bits(1) = [op_code[9]];
    o2 : bits(1) = [op_code[11]];
    cmode : bits(4) = op_code[15 .. 12];
    c : bits(1) = [op_code[16]];
    b : bits(1) = [op_code[17]];
    a : bits(1) = [op_code[18]];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_logical_decode(Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q)
}

function clause decode (0b00011001001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpair_decode(Rt, Xn, imm9)
}

function clause decode (_ : bits(1) @ 0b01100110 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_bitfield_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b0101 @ _ : bits(12) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    sz : bits(2) = op_code[11 .. 10];
    C : bits(1) = [op_code[12]];
    opcode2_5_3_ : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_crc_decode(Rd, Rn, sz, C, opcode2_5_3_, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111100000 @ _ : bits(7) @ 0b01 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    h : bits(1) = [op_code[5]];
    g : bits(1) = [op_code[6]];
    f : bits(1) = [op_code[7]];
    e : bits(1) = [op_code[8]];
    d : bits(1) = [op_code[9]];
    o2 : bits(1) = [op_code[11]];
    cmode : bits(4) = op_code[15 .. 12];
    c : bits(1) = [op_code[16]];
    b : bits(1) = [op_code[17]];
    a : bits(1) = [op_code[18]];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_logical_decode(Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b1101010100000011001000 @ _ : bits(1) @ 0b110 @ _ : bits(1) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_autia_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_int_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_tieaway_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0111111011111000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode (0b0111111011111000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode (_ : bits(1) @ 0b0111010000 @ _ : bits(6) @ 0b00001 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
    mask : bits(4) = op_code[3 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[20 .. 15];
    sf : bits(1) = [op_code[31]];
    integer_flags_rmif_decode(mask, Rn, imm6, sf)
}

function clause decode (0b11010100000 @ _ : bits(16) @ 0b00001 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_runtime_svc_decode(LL, op2, imm16, opc)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_add_saturating_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b11001110100 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    vector_crypto_sha3_xar_decode(Rd, Rn, imm6, Rm)
}

function clause decode (0b0 @ _ : bits(2) @ 0b10000 @ _ : bits(24) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    immhi : bits(19) = op_code[23 .. 5];
    immlo : bits(2) = op_code[30 .. 29];
    op : bits(1) = [op_code[31]];
    integer_arithmetic_address_pcrel_decode(Rd, immhi, immlo, op)
}

function clause decode (0b110101101001111100001 @ _ : bits(1) @ 0b1111111111 as op_code) = {
    op4 : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    branch_unconditional_eret_decode(op4, Rn, M, A, op2)
}

function clause decode (0b01001000000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b01111000101 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_orderedrcpc_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (_ : bits(1) @ 0b010100001 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_noalloc_memory_pair_general_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100101110000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_add_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0101111011111000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b00111000001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_int_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b01111110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_fp16_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode (0b0100111000101000011110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_mix_decode(Rd, Rn, D, size)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_swp_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (_ : bits(1) @ 0b0111010010 @ _ : bits(9) @ 0b00 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) = {
    nzcv : bits(4) = op_code[3 .. 0];
    o3 : bits(1) = [op_code[4]];
    Rn : bits(5) = op_code[9 .. 5];
    o2 : bits(1) = [op_code[10]];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_conditional_compare_register_decode(nzcv, o3, Rn, o2, cond, Rm, S, op, sf)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_long_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110011 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode (0b11010110100111110000001111100000 as op_code) = {
    op4 : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    branch_unconditional_eret_decode(op4, Rn, M, A, op2)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_accum_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100111110000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110000101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b10011011101 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    U : bits(1) = [op_code[23]];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_widening_3264_decode(Rd, Rn, Ra, o0, Rm, U, op54, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110100000000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100101000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmaxnm_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b10 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_double_simd_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode_0_ : bits(1) = [op_code[12]];
    opcode_1_ : bits(1) = [op_code[13]];
    opcode_2_ : bits(1) = [op_code[14]];
    opcode_3_ : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_product_decode(Rd, Rn, opcode_0_, opcode_1_, opcode_2_, opcode_3_, Rm, size, U, Q)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (0b0101111000110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16max_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100000010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode (0b01011001100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (_ : bits(1) @ 0b0111010000000000 @ _ : bits(1) @ 0b0010 @ _ : bits(5) @ 0b01101 as op_code) = {
    mask : bits(4) = op_code[3 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(4) = op_code[13 .. 10];
    sz : bits(1) = [op_code[14]];
    imm6 : bits(6) = op_code[20 .. 15];
    sf : bits(1) = [op_code[31]];
    integer_flags_setf_decode(mask, Rn, opcode2, sz, imm6, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4_0_ : bits(1) = [op_code[11]];
    imm4_1_ : bits(1) = [op_code[12]];
    imm4_3_2_ : bits(2) = op_code[14 .. 13];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_integer_move_signed_decode(Rd, Rn, imm4_0_, imm4_1_, imm4_3_2_, imm5, op, Q)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100000000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b11010100001 @ _ : bits(16) @ 0b00000 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_breakpoint_decode(LL, op2, imm16, opc)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b010001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightinsert_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode (0b11111000100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100001000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_logical_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacda_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_recip_float_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b110001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_reduce_add_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b01111000000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_1985_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode(Rd, Rn, S, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(5) @ 0b1100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b00011001000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpost_decode(Rt, Xn, imm9)
}

function clause decode (_ : bits(1) @ 0b10110101100000000001 @ _ : bits(11) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[11 .. 10];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rev_decode(Rd, Rn, opc, opcode2, S, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode (0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (_ : bits(1) @ 0b10100110 @ _ : bits(23) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_bitfield_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode (0b01101110000 @ _ : bits(5) @ 0b0 @ _ : bits(4) @ 0b1 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_insert_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode (0b110101100101111100001 @ _ : bits(1) @ 0b1111111111 as op_code) = {
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(5) @ 0b0100 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b01111110110 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b00011111 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_addsub_decode(Rd, Rn, Ra, o0, Rm, o1, typ, S, M)
}

function clause decode (0b0111100100 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode (0b0101111000110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16maxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b110110101100000101000 @ _ : bits(1) @ 0b11111 @ _ : bits(5) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[10]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_strip_dp_1src_decode(Rd, Rn, D, opcode2, S, sf)
}

function clause decode (_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b00 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_preidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_int_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_int_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacdb_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (0b00011001100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagandzerodatapost_decode(Rt, Xn, imm9)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100000000001000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b1001010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000110 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b0 @ _ : bits(2) @ 0b100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    len : bits(2) = op_code[14 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    op2 : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_table_decode(Rd, Rn, op, len, Rm, op2, Q)
}

function clause decode (0b10111010110 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags_decode(Xd, Xn, Xm)
}

function clause decode (0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_extract_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000010010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_clsz_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_int_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode (0b11010101000000110010000001111111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b110101010011 @ _ : bits(20) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    o0 : bits(1) = [op_code[19]];
    L : bits(1) = [op_code[21]];
    system_register_system_decode(Rt, op2, CRm, CRn, op1, o0, L)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode (_ : bits(1) @ 0b101101011000000000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[11 .. 10];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rev_decode(Rd, Rn, opc, opcode2, S, sf)
}

function clause decode (0b011111100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001111001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_double_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (0b0111111011111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode (0b0001111001111110000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b11010100101 @ _ : bits(16) @ 0b00011 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_exception_decode(LL, op2, imm16, opc)
}

function clause decode (0b01011110110 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_rsqrtsfp16_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode (_ : bits(1) @ 0b101101011000000000100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[10]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_cnt_decode(Rd, Rn, op, opcode2, S, sf)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b1101010100000011001000 @ _ : bits(1) @ 0b111 @ _ : bits(1) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_autib_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b0111111001111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110111 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b01001000110 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b00111000010 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b00111000000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_fp16_simd_decode(Rd, Rn, H, opcode, Rm, M, L, size, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b10100 @ _ : bits(2) @ 0b10000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    float_arithmetic_round_frint_32_64_decode(Rd, Rn, op, typ)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b0010001 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_cas_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b1 @ _ : bits(1) @ 0b001000110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (_ : bits(1) @ 0b0101011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_shiftedreg_decode(Rd, Rn, imm6, Rm, shift, S, op, sf)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op2 : bits(2) = op_code[11 .. 10];
    opcode2_5_2_ : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_shift_variable_decode(Rd, Rn, op2, opcode2_5_2_, Rm, S, op, sf)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b000011 @ _ : bits(16) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    scale : bits(6) = op_code[15 .. 10];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_fix_decode(Rd, Rn, scale, opcode, rmode, typ, S, sf)
}

function clause decode (0b11010101000000110011 @ _ : bits(4) @ 0b11111111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmaxnm_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode (0b01001000010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b01011111 @ _ : bits(8) @ 0b1100 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    op : bits(1) = [op_code[12]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mul_high_sisd_decode(Rd, Rn, H, op, Rm, M, L, size, U)
}

function clause decode (0b01111000011 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp_simd_decode(Rd, Rn, ac, Rm, sz, E, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b01011110000 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    vector_transfer_vector_cpydup_sisd_decode(Rd, Rn, imm4, imm5, op)
}

function clause decode (0b01001000100 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (_ : bits(1) @ 0b0001010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode(Rd, Rn, S, Rm, size, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0101111000101000000110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha2op_sha1sched1_decode(Rd, Rn, opcode, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111001111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b100101010000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode (0b00011001101 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairandzerodatapre_decode(Rt, Xn, imm9)
}

function clause decode (0b0101111010110000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16max_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110101 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(5) @ 0b1000 @ _ : bits(12) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode (_ : bits(1) @ 0b0101010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_fp_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode (0b001110011 @ _ : bits(23) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (_ : bits(1) @ 0b1101011001 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm3 : bits(3) = op_code[12 .. 10];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opt : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_extendedreg_decode(Rd, Rn, imm3, option_name, Rm, opt, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_dmacc_simd_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode_0_ : bits(1) = [op_code[12]];
    opcode_1_ : bits(1) = [op_code[13]];
    opcode_2_ : bits(1) = [op_code[14]];
    opcode_3_ : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_product_decode(Rd, Rn, opcode_0_, opcode_1_, opcode_2_, opcode_3_, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_rounding_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp_2008_decode(Rd, Rn, opcode, Rm, sz, o1, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000000010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rev_decode(Rd, Rn, o0, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_right_simd_decode(Rd, Rn, o0, o1, immb, immh, U, Q)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftsat_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b11011000 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_general_decode(Rt, imm19, V, opc)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmaxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_fp_extended_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode (_ : bits(1) @ 0b0110101 @ _ : bits(24) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    op : bits(1) = [op_code[24]];
    sf : bits(1) = [op_code[31]];
    branch_conditional_compare_decode(Rt, imm19, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001100010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (_ : bits(2) @ 0b10110111 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b00011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b11010101000000110010000011111111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_strip_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_shift_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode (0b011111110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110000 @ _ : bits(5) @ 0b0 @ _ : bits(4) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    op2 : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_extract_decode(Rd, Rn, imm4, Rm, op2, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mul_long_decode(Rd, Rn, H, opcode, Rm, M, L, size, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode (0b01001000010 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_exclusive_single_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (0b11010100000 @ _ : bits(16) @ 0b00011 as op_code) = {
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_runtime_smc_decode(LL, op2, imm16, opc)
}

function clause decode (0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0101111011111000111010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_lessthan_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode (0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b11111000101 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110101100000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_nowb_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00110001000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode (0b010111101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111100000 @ _ : bits(6) @ 0b101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    h : bits(1) = [op_code[5]];
    g : bits(1) = [op_code[6]];
    f : bits(1) = [op_code[7]];
    e : bits(1) = [op_code[8]];
    d : bits(1) = [op_code[9]];
    o2 : bits(1) = [op_code[11]];
    cmode : bits(4) = op_code[15 .. 12];
    c : bits(1) = [op_code[16]];
    b : bits(1) = [op_code[17]];
    a : bits(1) = [op_code[18]];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_logical_decode(Rd, h, g, f, e, d, o2, cmode, c, b, a, op, Q)
}

function clause decode (0b01011111 @ _ : bits(8) @ 0b1011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mul_double_sisd_decode(Rd, Rn, H, opcode, Rm, M, L, size, U)
}

function clause decode (0b01001000100 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    size : bits(2) = op_code[31 .. 30];
    memory_ordered_decode(Rt, Rn, Rt2, o0, Rs, o1, L, o2, size)
}

function clause decode (_ : bits(1) @ 0b1001010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_truncating_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode (0b1111100110 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_unsigned__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b011111101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_sqrtest_float_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode (_ : bits(2) @ 0b111101 @ _ : bits(1) @ 0b1 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (_ : bits(2) @ 0b10110000 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111100 @ _ : bits(6) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_element_mulacc_fp16_simd_decode(Rd, Rn, H, o2, Rm, M, L, size, U, Q)
}

function clause decode (_ : bits(1) @ 0b010100101 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_offset_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b000010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[10]];
    opcode2_5_1_ : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_div_decode(Rd, Rn, o1, opcode2_5_1_, Rm, S, op, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_shift_simd_decode(Rd, Rn, S, R, Rm, size, U, Q)
}

function clause decode (0b00011001000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpre_decode(Rt, Xn, imm9)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000010110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cnt_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b010111110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftsat_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode (0b010111111 @ _ : bits(7) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    o2 : bits(1) = [op_code[14]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mulacc_fp_sisd_decode(Rd, Rn, H, o2, Rm, M, L, sz, U)
}

function clause decode (0b011110001 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[12]];
    option_name : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_register_memory_single_general_register__decode(Rt, Rn, S, option_name, Rm, opc, V, size)
}

function clause decode (0b10011011010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Ra : bits(5) = op_code[14 .. 10];
    o0 : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    U : bits(1) = [op_code[23]];
    op54 : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_mul_widening_64128hi_decode(Rd, Rn, Ra, o0, Rm, U, op54, sf)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000111110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_float_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b00011001110 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_float_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode (0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(5) @ 0b11111 as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_st_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b00111011111001101010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    S : bits(1) = [op_code[12]];
    opcode : bits(3) = op_code[15 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[21]];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_single_postinc_memory_vector_single_nowb__decode(Rt, Rn, size, S, opcode, Rm, R, L, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000111010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_lessthan_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode (0b0110100011 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_postidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode (0b0 @ _ : bits(1) @ 0b10111001111001110110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_int_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode (0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_rsqrts_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode (0b1011100110 @ _ : bits(22) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode (0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode (0b0101111001111001101110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode (0b010111100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode (0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110000001110 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_addlong_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode (0b0110100010 @ _ : bits(22) as op_code) = {
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xt2 : bits(5) = op_code[14 .. 10];
    simm7 : bits(7) = op_code[21 .. 15];
    integer_tags_mcsettaganddatapairpost_decode(Xt, Xn, Xt2, simm7)
}

function clause decode (0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_move_fp_select_decode(Rd, Rn, cond, Rm, typ, S, M)
}

function clause decode (_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op2 : bits(2) = op_code[11 .. 10];
    opcode2_5_2_ : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_shift_variable_decode(Rd, Rn, op2, opcode2_5_2_, Rm, S, op, sf)
}

function clause decode (0b01011111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    H : bits(1) = [op_code[11]];
    op : bits(1) = [op_code[12]];
    Rm : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[20]];
    L : bits(1) = [op_code[21]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_element_mul_high_sisd_decode(Rd, Rn, H, op, Rm, M, L, size, U)
}

function clause decode (_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100100000000 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode (0b110110101100000100 @ _ : bits(1) @ 0b100 @ _ : bits(10) as op_code) = {
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autia_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode (0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) = {
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(3) = op_code[14 .. 12];
    o3 : bits(1) = [op_code[15]];
    Rs : bits(5) = op_code[20 .. 16];
    R : bits(1) = [op_code[22]];
    A : bits(1) = [op_code[23]];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_atomicops_ld_decode(Rt, Rn, opc, o3, Rs, R, A, V, size)
}
end decode
