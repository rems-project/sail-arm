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

register SEE : int

val decode32 : bits(32) -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

val decode64 : bits(32) -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

function clause decode32 ((_ : bits(4) @ 0b0001111 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 0) = {
    SEE = 0;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    MVN_r_A1_A_decode(cond, S, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 1) = {
    SEE = 1;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDREXB_T1_A_decode(Rn, Rt)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 2) = {
    SEE = 2;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T3A3_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 3) = {
    SEE = 3;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VEOR_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 4) = {
    SEE = 4;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHL_i_T1A1_A_decode(D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100010 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 5) = {
    SEE = 5;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QADD16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111110100 @ _ : bits(7) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 6) = {
    SEE = 6;
    typ : bits(2) = op_code[22 .. 21];
    S : bits(1) = [op_code[20]];
    Rm : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rs : bits(4) = op_code[3 .. 0];
    MOV_rr_T2_A_decode(typ, S, Rm, Rd, Rs)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b100 @ _ : bits(1) @ 0b01 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 7) = {
    SEE = 7;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRSHRN_T1A1_A_decode(U, D, imm6, Vd, op, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 8) = {
    SEE = 8;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMULH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0100 @ _ : bits(1) @ 0b110 @ _ : bits(20) as op_code) if SEE < 9) = {
    SEE = 9;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    STRBT_A1pre_A_decode(cond, U, Rn, Rt, imm12)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 10) = {
    SEE = 10;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1SU0_A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110001011 @ _ : bits(20) as op_code) if SEE < 11) = {
    SEE = 11;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRH_i_T2_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((0b111110101010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 12) = {
    SEE = 12;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SASX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b11110011111 @ _ : bits(5) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(6) @ 0b1 @ _ : bits(5) as op_code) if SEE < 13) = {
    SEE = 13;
    R : bits(1) = [op_code[20]];
    M1 : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    MRS_br_T1_AS_decode(R, M1, Rd, M)
}

function clause decode32 ((_ : bits(16) @ 0b0100000000 @ _ : bits(6) as op_code) if SEE < 14) = {
    SEE = 14;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    AND_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((_ : bits(16) @ 0b11001 @ _ : bits(11) as op_code) if SEE < 15) = {
    SEE = 15;
    Rn : bits(3) = op_code[10 .. 8];
    register_list : bits(8) = op_code[7 .. 0];
    LDM_T1_A_decode(Rn, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b0110101 @ _ : bits(15) @ 0b01 @ _ : bits(4) as op_code) if SEE < 16) = {
    SEE = 16;
    cond : bits(4) = op_code[31 .. 28];
    sat_imm : bits(5) = op_code[20 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    sh : bits(1) = [op_code[6]];
    Rn : bits(4) = op_code[3 .. 0];
    SSAT_A1_A_decode(cond, sat_imm, Rd, imm5, sh, Rn)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 17) = {
    SEE = 17;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    len : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VTBL_T1A1_A_decode(D, Vn, Vd, len, N, op, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 18) = {
    SEE = 18;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABA_T2A2_A_decode(U, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b11000 @ _ : bits(11) as op_code) if SEE < 19) = {
    SEE = 19;
    Rn : bits(3) = op_code[10 .. 8];
    register_list : bits(8) = op_code[7 .. 0];
    STM_T1_A_decode(Rn, register_list)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(20) as op_code) if SEE < 20) = {
    SEE = 20;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00010 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 21) = {
    SEE = 21;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VUZP_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111111100 @ _ : bits(11) @ 0b10 @ _ : bits(3) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 22) = {
    SEE = 22;
    D : bits(1) = [op_code[22]];
    cc : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSEL_A1_A_decode(D, cc, Vn, Vd, size, N, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b10 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 23) = {
    SEE = 23;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VBIC_i_T1A1_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((_ : bits(16) @ 0b01000101 @ _ : bits(8) as op_code) if SEE < 24) = {
    SEE = 24;
    N : bits(1) = [op_code[7]];
    Rm : bits(4) = op_code[6 .. 3];
    Rn : bits(3) = op_code[2 .. 0];
    CMP_r_T2_A_decode(N, Rm, Rn)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 25) = {
    SEE = 25;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    op : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAX_i_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, op, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b10111111 @ _ : bits(8) as op_code) if SEE < 26) = {
    SEE = 26;
    firstcond : bits(4) = op_code[7 .. 4];
    mask : bits(4) = op_code[3 .. 0];
    IT_T1_A_decode(firstcond, mask)
}

function clause decode32 ((_ : bits(4) @ 0b0001101 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 27) = {
    SEE = 27;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    MOV_r_A1_A_decode(cond, S, Rd, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b001100100000 @ _ : bits(8) @ 0b00000101 as op_code) if SEE < 28) = {
    SEE = 28;
    cond : bits(4) = op_code[31 .. 28];
    SEVL_A1_A_decode(cond)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 29) = {
    SEE = 29;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGE_r_A2_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b01101 @ _ : bits(1) @ 0b11010 @ _ : bits(15) as op_code) if SEE < 30) = {
    SEE = 30;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    SUB_SP_i_T2_A_decode(i, S, imm3, Rd, imm8)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 31) = {
    SEE = 31;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QDADD_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0010100 @ _ : bits(1) @ 0b1101 @ _ : bits(16) as op_code) if SEE < 32) = {
    SEE = 32;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    ADD_SP_i_A1_A_decode(cond, S, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b0111111 @ _ : bits(14) @ 0b101 @ _ : bits(4) as op_code) if SEE < 33) = {
    SEE = 33;
    cond : bits(4) = op_code[31 .. 28];
    widthm1 : bits(5) = op_code[20 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    lsb : bits(5) = op_code[11 .. 7];
    Rn : bits(4) = op_code[3 .. 0];
    UBFX_A1_A_decode(cond, widthm1, Rd, lsb, Rn)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 34) = {
    SEE = 34;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256H2_A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1110 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 35) = {
    SEE = 35;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VACGE_A1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0100000010 @ _ : bits(6) as op_code) if SEE < 36) = {
    SEE = 36;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    LSL_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((_ : bits(16) @ 0b0100001011 @ _ : bits(6) as op_code) if SEE < 37) = {
    SEE = 37;
    Rm : bits(3) = op_code[5 .. 3];
    Rn : bits(3) = op_code[2 .. 0];
    CMN_r_T1_A_decode(Rm, Rn)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b01000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 38) = {
    SEE = 38;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADD_i_T3_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b1110000 @ _ : bits(9) @ 0b1001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 39) = {
    SEE = 39;
    cond : bits(4) = op_code[31 .. 28];
    op : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    VMOV_h_A1_A_decode(cond, op, Vn, Rt, N)
}

function clause decode32 ((_ : bits(4) @ 0b11100 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 40) = {
    SEE = 40;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VNMLA_A1_A_decode(cond, D, Vn, Vd, size, N, op, M, Vm)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 41) = {
    SEE = 41;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[3 .. 0];
    STREXB_T1_A_decode(Rn, Rt, Rd)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b100 @ _ : bits(9) as op_code) if SEE < 42) = {
    SEE = 42;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 43) = {
    SEE = 43;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T4A4_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 44) = {
    SEE = 44;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSLI_T1A1_A_decode(D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001111 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 45) = {
    SEE = 45;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESIMC_T1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001111 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 46) = {
    SEE = 46;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256SU0_T1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(20) as op_code) if SEE < 47) = {
    SEE = 47;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110001010 @ _ : bits(20) as op_code) if SEE < 48) = {
    SEE = 48;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    STRH_i_T2_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b001100100000 @ _ : bits(8) @ 0b00000011 as op_code) if SEE < 49) = {
    SEE = 49;
    cond : bits(4) = op_code[31 .. 28];
    WFI_A1_A_decode(cond)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 50) = {
    SEE = 50;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1C_A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0100000001 @ _ : bits(6) as op_code) if SEE < 51) = {
    SEE = 51;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    EOR_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((_ : bits(4) @ 0b01100111 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 52) = {
    SEE = 52;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UHADD8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b10110110011 @ _ : bits(1) @ 0b0 @ _ : bits(3) as op_code) if SEE < 53) = {
    SEE = 53;
    im : bits(1) = [op_code[4]];
    A : bits(1) = [op_code[2]];
    I : bits(1) = [op_code[1]];
    F : bits(1) = [op_code[0]];
    CPS_T1pre_AS_decode(im, A, I, F)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 54) = {
    SEE = 54;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    REVSH_T2_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b111001 @ _ : bits(4) @ 0b101111 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 55) = {
    SEE = 55;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VJCVT_T1_A_decode(D, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b1011 @ _ : bits(24) as op_code) if SEE < 56) = {
    SEE = 56;
    cond : bits(4) = op_code[31 .. 28];
    imm24 : bits(24) = op_code[23 .. 0];
    BL_i_A1_A_decode(cond, imm24)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b0 @ _ : bits(1) @ 0b11 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 57) = {
    SEE = 57;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[10]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMLAL_T2A2_A_decode(D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 58) = {
    SEE = 58;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABD_f_T1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111011110 @ _ : bits(11) @ 0b1111 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 59) = {
    SEE = 59;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAX_f_T1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1110 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 60) = {
    SEE = 60;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VACGE_T1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b01001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 61) = {
    SEE = 61;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTX_asimd_A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b000 @ _ : bits(4) @ 0b0 @ _ : bits(4) as op_code) if SEE < 62) = {
    SEE = 62;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[8 .. 7];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VREV16_T1A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b001 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 63) = {
    SEE = 63;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUBL_T1A1_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b1001 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 64) = {
    SEE = 64;
    op : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_i_T1A1_A_decode(op, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 65) = {
    SEE = 65;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    STRH_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(20) as op_code) if SEE < 66) = {
    SEE = 66;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010011 @ _ : bits(12) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 67) = {
    SEE = 67;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    TEQ_rr_A1_A_decode(cond, Rn, Rs, typ, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0010 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 68) = {
    SEE = 68;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSUB_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1111 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 69) = {
    SEE = 69;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPMAX_f_A1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(11) @ 0b11 @ _ : bits(1) @ 0b1 @ _ : bits(12) as op_code) if SEE < 70) = {
    SEE = 70;
    S : bits(1) = [op_code[26]];
    imm10 : bits(10) = op_code[25 .. 16];
    J1 : bits(1) = [op_code[13]];
    J2 : bits(1) = [op_code[11]];
    imm11 : bits(11) = op_code[10 .. 0];
    BL_i_T1_A_decode(S, imm10, J1, J2, imm11)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b110111 @ _ : bits(4) @ 0b10 @ _ : bits(2) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 71) = {
    SEE = 71;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTX_vfp_T1_A_decode(D, Vd, size, M, Vm)
}

function clause decode32 ((0b111110101110 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 72) = {
    SEE = 72;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SHSAX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111010000101 @ _ : bits(20) as op_code) if SEE < 73) = {
    SEE = 73;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    LDREX_T1_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 74) = {
    SEE = 74;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    op : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAX_i_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, op, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 75) = {
    SEE = 75;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGE_r_T2_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100111101 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(12) as op_code) if SEE < 76) = {
    SEE = 76;
    imm8 : bits(8) = op_code[7 .. 0];
    ERET_T1_A_decode(imm8)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 77) = {
    SEE = 77;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T3A3_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 78) = {
    SEE = 78;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSHL_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b111 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 79) = {
    SEE = 79;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRSHT_A1pre_A_decode(cond, U, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 80) = {
    SEE = 80;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VEOR_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00011101 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 81) = {
    SEE = 81;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAEXB_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b1111 @ _ : bits(24) as op_code) if SEE < 82) = {
    SEE = 82;
    cond : bits(4) = op_code[31 .. 28];
    imm24 : bits(24) = op_code[23 .. 0];
    SVC_A1_A_decode(cond, imm24)
}

function clause decode32 ((_ : bits(4) @ 0b01100001 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 83) = {
    SEE = 83;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SSAX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b10101 @ _ : bits(11) as op_code) if SEE < 84) = {
    SEE = 84;
    Rd : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADD_SP_i_T1_A_decode(Rd, imm8)
}

function clause decode32 ((0b111110000100 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 85) = {
    SEE = 85;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    STRT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 86) = {
    SEE = 86;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VORN_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110000000 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 87) = {
    SEE = 87;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    STRBT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 88) = {
    SEE = 88;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSQRTS_A1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111101111000111110000000000000 @ _ : bits(2) as op_code) if SEE < 89) = {
    SEE = 89;
    opt : bits(2) = op_code[1 .. 0];
    DCPS_T1_A_decode(opt)
}

function clause decode32 ((_ : bits(4) @ 0b0001101 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 90) = {
    SEE = 90;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    MOV_rr_A1_A_decode(cond, S, Rd, Rs, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01101111 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 91) = {
    SEE = 91;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    REVSH_A1_A_decode(cond, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010001 @ _ : bits(12) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 92) = {
    SEE = 92;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    TST_rr_A1_A_decode(cond, Rn, Rs, typ, Rm)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 93) = {
    SEE = 93;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGT_r_A2_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111011100 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 94) = {
    SEE = 94;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VNMLA_T1_A_decode(D, Vn, Vd, size, N, op, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 95) = {
    SEE = 95;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABA_T2A2_A_decode(U, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01111 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 96) = {
    SEE = 96;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQNEG_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111110001000 @ _ : bits(20) as op_code) if SEE < 97) = {
    SEE = 97;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    STRB_i_T2_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b01110000 @ _ : bits(12) @ 0b01 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 98) = {
    SEE = 98;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMLSD_A1_A_decode(cond, Rd, Ra, Rm, M, Rn)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 99) = {
    SEE = 99;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLE_i_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(11) @ 0b1100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 100) = {
    SEE = 100;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFMA_A1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00011111 @ _ : bits(10) @ 0b001001 @ _ : bits(4) as op_code) if SEE < 101) = {
    SEE = 101;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAH_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b00011100 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 102) = {
    SEE = 102;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STLEXB_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 103) = {
    SEE = 103;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UHADD8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b11101010010 @ _ : bits(21) as op_code) if SEE < 104) = {
    SEE = 104;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    ORR_r_T2_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 105) = {
    SEE = 105;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    len : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VTBL_T1A1_A_decode(D, Vn, Vd, len, N, op, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000110 @ _ : bits(13) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 106) = {
    SEE = 106;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    SMULL_A1_A_decode(cond, S, RdHi, RdLo, Rm, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b010 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b11111 @ _ : bits(16) as op_code) if SEE < 107) = {
    SEE = 107;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDR_l_A1_A_decode(cond, P, U, W, Rt, imm12)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(20) as op_code) if SEE < 108) = {
    SEE = 108;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b1110 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 109) = {
    SEE = 109;
    Q : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLAH_A2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0100001111 @ _ : bits(6) as op_code) if SEE < 110) = {
    SEE = 110;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    MVN_r_T1_A_decode(Rm, Rd)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b10 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 111) = {
    SEE = 111;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VBIC_i_T1A1_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b111110100011 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 112) = {
    SEE = 112;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    UXTAB16_T1_A_decode(Rn, Rd, rotate, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b100100 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 113) = {
    SEE = 113;
    i : bits(1) = [op_code[26]];
    imm4 : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    MOV_i_T3pre_A_decode(i, imm4, imm3, Rd, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b01101110 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 114) = {
    SEE = 114;
    cond : bits(4) = op_code[31 .. 28];
    sat_imm : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rn : bits(4) = op_code[3 .. 0];
    USAT16_A1_A_decode(cond, sat_imm, Rd, Rn)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 115) = {
    SEE = 115;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1C_T1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b1011111101010000 as op_code) if SEE < 116) = {
    SEE = 116;
    SEVL_T1_A_decode()
}

function clause decode32 ((_ : bits(4) @ 0b00010 @ _ : bits(2) @ 0b0 @ _ : bits(12) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 117) = {
    SEE = 117;
    cond : bits(4) = op_code[31 .. 28];
    sz : bits(2) = op_code[22 .. 21];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    C : bits(1) = [op_code[9]];
    Rm : bits(4) = op_code[3 .. 0];
    CRC32_A1_A_decode(cond, sz, Rn, Rd, C, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00110001 @ _ : bits(20) as op_code) if SEE < 118) = {
    SEE = 118;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    TST_i_A1_A_decode(cond, Rn, imm12)
}

function clause decode32 ((0b11111110 @ _ : bits(12) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 119) = {
    SEE = 119;
    S : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    rot : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCMLA_idx_A1_A_decode(S, D, rot, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100011 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 120) = {
    SEE = 120;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SHADD16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 121) = {
    SEE = 121;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QADD16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b111100 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 122) = {
    SEE = 122;
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    widthm1 : bits(5) = op_code[4 .. 0];
    UBFX_T1_A_decode(Rn, imm3, Rd, imm2, widthm1)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 123) = {
    SEE = 123;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((0b111110101101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 124) = {
    SEE = 124;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UQSUB16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0010 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 125) = {
    SEE = 125;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSUB_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 126) = {
    SEE = 126;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VZIP_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1111 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 127) = {
    SEE = 127;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPMAX_f_T1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b11110101 @ _ : bits(2) @ 0b0111111111 @ _ : bits(12) as op_code) if SEE < 128) = {
    SEE = 128;
    U : bits(1) = [op_code[23]];
    R : bits(1) = [op_code[22]];
    imm12 : bits(12) = op_code[11 .. 0];
    PLD_l_A1_A_decode(U, R, imm12)
}

function clause decode32 ((0b111110111000 @ _ : bits(12) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 129) = {
    SEE = 129;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SMULL_T1_A_decode(Rn, RdLo, RdHi, Rm)
}

function clause decode32 ((0b111001111111 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 130) = {
    SEE = 130;
    imm12 : bits(12) = op_code[19 .. 8];
    imm4 : bits(4) = op_code[3 .. 0];
    UDF_A1_A_decode(imm12, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b00010100 @ _ : bits(12) @ 0b1 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 131) = {
    SEE = 131;
    cond : bits(4) = op_code[31 .. 28];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[6]];
    N : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMLALBB_A1_A_decode(cond, RdHi, RdLo, Rm, M, N, Rn)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 132) = {
    SEE = 132;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLE_i_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111110000101 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 133) = {
    SEE = 133;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    LDR_i_T4_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b111010 @ _ : bits(4) @ 0b0000 @ _ : bits(4) @ 0b00 @ _ : bits(6) as op_code) if SEE < 134) = {
    SEE = 134;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    sat_imm : bits(4) = op_code[3 .. 0];
    USAT16_T1_A_decode(Rn, Rd, sat_imm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 135) = {
    SEE = 135;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSHL_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00010011 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 136) = {
    SEE = 136;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    TEQ_r_A1_A_decode(cond, Rn, imm5, typ, Rm)
}

function clause decode32 ((0b111101010111 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 137) = {
    SEE = 137;
    SB_A1_A_decode()
}

function clause decode32 ((0b11101010001 @ _ : bits(21) as op_code) if SEE < 138) = {
    SEE = 138;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    BIC_r_T2_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b1001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 139) = {
    SEE = 139;
    op : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_i_T1A1_A_decode(op, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00110000 @ _ : bits(20) as op_code) if SEE < 140) = {
    SEE = 140;
    cond : bits(4) = op_code[31 .. 28];
    imm4 : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    MOV_i_A2pre_A_decode(cond, imm4, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b010 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 141) = {
    SEE = 141;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    STR_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b00011000 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 142) = {
    SEE = 142;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STREX_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b001 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 143) = {
    SEE = 143;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUBL_T1A1_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b011010111111 @ _ : bits(8) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 144) = {
    SEE = 144;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    SXTH_A1_A_decode(cond, Rd, rotate, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b1001 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 145) = {
    SEE = 145;
    op : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_i_T1A1_A_decode(op, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001000 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 146) = {
    SEE = 146;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMOVN_T1A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111101111111 @ _ : bits(4) @ 0b1000 @ _ : bits(12) as op_code) if SEE < 147) = {
    SEE = 147;
    imm4 : bits(4) = op_code[19 .. 16];
    SMC_T1_AS_decode(imm4)
}

function clause decode32 ((0b11111010001011111111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 148) = {
    SEE = 148;
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SXTB16_T1_A_decode(Rd, rotate, Rm)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0001111 @ _ : bits(4) as op_code) if SEE < 149) = {
    SEE = 149;
    option_name : bits(4) = op_code[3 .. 0];
    DBG_T1_A_decode(option_name)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b100 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 150) = {
    SEE = 150;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLT_i_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 151) = {
    SEE = 151;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGT_r_T2_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000000 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 152) = {
    SEE = 152;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    AND_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00011000 @ _ : bits(10) @ 0b001001 @ _ : bits(4) as op_code) if SEE < 153) = {
    SEE = 153;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[3 .. 0];
    STL_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b11111010110 @ _ : bits(5) @ 0b1111 @ _ : bits(4) @ 0b10 @ _ : bits(6) as op_code) if SEE < 154) = {
    SEE = 154;
    C : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    sz : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    CRC32_T1_A_decode(C, Rn, Rd, sz, Rm)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b100001 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 155) = {
    SEE = 155;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSHRN_T1A1_A_decode(D, imm6, Vd, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b000001 @ _ : bits(4) @ 0b0 @ _ : bits(3) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 156) = {
    SEE = 156;
    i : bits(1) = [op_code[26]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    TST_i_T1_A_decode(i, Rn, imm3, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b0000000 @ _ : bits(13) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 157) = {
    SEE = 157;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[19 .. 16];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    MUL_A1_A_decode(cond, S, Rd, Rm, Rn)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 158) = {
    SEE = 158;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    op : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VPMAX_i_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, op, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b001100100000 @ _ : bits(8) @ 0b00000010 as op_code) if SEE < 159) = {
    SEE = 159;
    cond : bits(4) = op_code[31 .. 28];
    WFE_A1_A_decode(cond)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0 @ _ : bits(1) @ 0b10 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 160) = {
    SEE = 160;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[10]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_s_T2A2_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00010010 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 161) = {
    SEE = 161;
    cond : bits(4) = op_code[31 .. 28];
    Rm : bits(4) = op_code[3 .. 0];
    BLX_r_A1_A_decode(cond, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1011110 @ _ : bits(9) as op_code) if SEE < 162) = {
    SEE = 162;
    P : bits(1) = [op_code[8]];
    register_list : bits(8) = op_code[7 .. 0];
    POP_T1_A_decode(P, register_list)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b1100 @ _ : bits(4) as op_code) if SEE < 163) = {
    SEE = 163;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAEXB_T1_A_decode(Rn, Rt)
}

function clause decode32 ((0b111110101110 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 164) = {
    SEE = 164;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SSAX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00011001 @ _ : bits(10) @ 0b001001 @ _ : bits(4) as op_code) if SEE < 165) = {
    SEE = 165;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDA_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((_ : bits(16) @ 0b0101010 @ _ : bits(9) as op_code) if SEE < 166) = {
    SEE = 166;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    STRB_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 167) = {
    SEE = 167;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 168) = {
    SEE = 168;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VORN_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b1111100010 @ _ : bits(1) @ 0b1 @ _ : bits(4) @ 0b1111 @ _ : bits(12) as op_code) if SEE < 169) = {
    SEE = 169;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    PLD_i_T1_A_decode(W, Rn, imm12)
}

function clause decode32 ((_ : bits(16) @ 0b01001 @ _ : bits(11) as op_code) if SEE < 170) = {
    SEE = 170;
    Rt : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    LDR_l_T1_A_decode(Rt, imm8)
}

function clause decode32 ((0b11101011011 @ _ : bits(21) as op_code) if SEE < 171) = {
    SEE = 171;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SBC_r_T2_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01101000 @ _ : bits(14) @ 0b01 @ _ : bits(4) as op_code) if SEE < 172) = {
    SEE = 172;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    tb : bits(1) = [op_code[6]];
    Rm : bits(4) = op_code[3 .. 0];
    PKH_A1_A_decode(cond, Rn, Rd, imm5, tb, Rm)
}

function clause decode32 ((0b11111010010111111111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 173) = {
    SEE = 173;
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    UXTB_T2_A_decode(Rd, rotate, Rm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b1110 @ _ : bits(6) @ 0b10 @ _ : bits(2) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 174) = {
    SEE = 174;
    D : bits(1) = [op_code[22]];
    RM : bits(2) = op_code[17 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTA_vfp_A1_A_decode(D, RM, Vd, size, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 175) = {
    SEE = 175;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VAND_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 176) = {
    SEE = 176;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_f_T1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b100110 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 177) = {
    SEE = 177;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    LDMIB_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 178) = {
    SEE = 178;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SHADD16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010110 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 179) = {
    SEE = 179;
    cond : bits(4) = op_code[31 .. 28];
    imm4 : bits(4) = op_code[3 .. 0];
    SMC_A1_AS_decode(cond, imm4)
}

function clause decode32 ((0b111110101010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1000 @ _ : bits(4) as op_code) if SEE < 180) = {
    SEE = 180;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SEL_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010010 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 181) = {
    SEE = 181;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QSUB_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b11111 @ _ : bits(8) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 182) = {
    SEE = 182;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRSH_l_A1_A_decode(cond, P, U, W, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111110111101 @ _ : bits(12) @ 0b110 @ _ : bits(5) as op_code) if SEE < 183) = {
    SEE = 183;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMLSLD_T1_A_decode(Rn, RdLo, RdHi, M, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b1110 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 184) = {
    SEE = 184;
    Q : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLAH_T2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b011 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 185) = {
    SEE = 185;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_hs_T1A1_A_decode(D, size, Vd, op, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b11011111 @ _ : bits(8) as op_code) if SEE < 186) = {
    SEE = 186;
    imm8 : bits(8) = op_code[7 .. 0];
    SVC_T1_A_decode(imm8)
}

function clause decode32 ((_ : bits(4) @ 0b01100111 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 187) = {
    SEE = 187;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UHSUB8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0101110 @ _ : bits(9) as op_code) if SEE < 188) = {
    SEE = 188;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDRB_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((0b111110110100 @ _ : bits(12) @ 0b000 @ _ : bits(5) as op_code) if SEE < 189) = {
    SEE = 189;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMLSD_T1_A_decode(Rn, Ra, Rd, M, Rm)
}

function clause decode32 ((0b11110011111 @ _ : bits(5) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(6) @ 0b0 @ _ : bits(5) as op_code) if SEE < 190) = {
    SEE = 190;
    R : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[11 .. 8];
    MRS_T1_AS_decode(R, Rd)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b110 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 191) = {
    SEE = 191;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMVN_i_T3A3_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((_ : bits(16) @ 0b0100001101 @ _ : bits(6) as op_code) if SEE < 192) = {
    SEE = 192;
    Rn : bits(3) = op_code[5 .. 3];
    Rdm : bits(3) = op_code[2 .. 0];
    MUL_T1_A_decode(Rn, Rdm)
}

function clause decode32 ((0b111100111011 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(4) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 193) = {
    SEE = 193;
    option_name : bits(4) = op_code[3 .. 0];
    DSB_T1_A_decode(option_name)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b00000000100 as op_code) if SEE < 194) = {
    SEE = 194;
    SEV_T2_A_decode()
}

function clause decode32 ((_ : bits(4) @ 0b0001110 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 195) = {
    SEE = 195;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    BIC_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 196) = {
    SEE = 196;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b1110000 @ _ : bits(9) @ 0b1010 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 197) = {
    SEE = 197;
    cond : bits(4) = op_code[31 .. 28];
    op : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    VMOV_s_A1_A_decode(cond, op, Vn, Rt, N)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 198) = {
    SEE = 198;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 199) = {
    SEE = 199;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    STRD_r_A1_A_decode(cond, P, U, W, Rn, Rt, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0111110 @ _ : bits(14) @ 0b001 @ _ : bits(4) as op_code) if SEE < 200) = {
    SEE = 200;
    cond : bits(4) = op_code[31 .. 28];
    msb : bits(5) = op_code[20 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    lsb : bits(5) = op_code[11 .. 7];
    Rn : bits(4) = op_code[3 .. 0];
    BFI_A1_A_decode(cond, msb, Rd, lsb, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b001010001111 @ _ : bits(16) as op_code) if SEE < 201) = {
    SEE = 201;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    ADR_A1_A_decode(cond, Rd, imm12)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b011 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 202) = {
    SEE = 202;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_hs_T1A1_A_decode(D, size, Vd, op, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b11111 @ _ : bits(8) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 203) = {
    SEE = 203;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRSB_l_A1_A_decode(cond, P, U, W, Rt, imm4H, imm4L)
}

function clause decode32 ((_ : bits(4) @ 0b100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 204) = {
    SEE = 204;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    STM_u_A1_AS_decode(cond, P, U, Rn, register_list)
}

function clause decode32 ((0b111110101100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 205) = {
    SEE = 205;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UHSUB8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000011 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 206) = {
    SEE = 206;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    RSB_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((0b111110011001 @ _ : bits(20) as op_code) if SEE < 207) = {
    SEE = 207;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRSB_i_T1_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1000 @ _ : bits(8) as op_code) if SEE < 208) = {
    SEE = 208;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b11111001 @ _ : bits(1) @ 0b0111111 @ _ : bits(16) as op_code) if SEE < 209) = {
    SEE = 209;
    U : bits(1) = [op_code[23]];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRSH_l_T1_A_decode(U, Rt, imm12)
}

function clause decode32 ((_ : bits(16) @ 0b0001100 @ _ : bits(9) as op_code) if SEE < 210) = {
    SEE = 210;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    ADD_r_T1_A_decode(Rm, Rn, Rd)
}

function clause decode32 ((0b11101010110 @ _ : bits(21) as op_code) if SEE < 211) = {
    SEE = 211;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    tb : bits(1) = [op_code[5]];
    T : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    PKH_T1_A_decode(S, Rn, imm3, Rd, imm2, tb, T, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100011 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 212) = {
    SEE = 212;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SHADD8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1011111100100000 as op_code) if SEE < 213) = {
    SEE = 213;
    WFE_T1_A_decode()
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0 @ _ : bits(1) @ 0b10 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 214) = {
    SEE = 214;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[10]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_s_T2A2_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00011100 @ _ : bits(10) @ 0b001001 @ _ : bits(4) as op_code) if SEE < 215) = {
    SEE = 215;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[3 .. 0];
    STLB_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0100 @ _ : bits(8) as op_code) if SEE < 216) = {
    SEE = 216;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1011001000 @ _ : bits(6) as op_code) if SEE < 217) = {
    SEE = 217;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    SXTH_T1_A_decode(Rm, Rd)
}

function clause decode32 ((0b111110111100 @ _ : bits(12) @ 0b10 @ _ : bits(6) as op_code) if SEE < 218) = {
    SEE = 218;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    N : bits(1) = [op_code[5]];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMLALBB_T1_A_decode(Rn, RdLo, RdHi, N, M, Rm)
}

function clause decode32 ((0b111110111011 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 219) = {
    SEE = 219;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UDIV_T1_A_decode(Rn, Ra, Rd, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b1010 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 220) = {
    SEE = 220;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_s_T2A2_A_decode(U, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 221) = {
    SEE = 221;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T3A3pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b10 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 222) = {
    SEE = 222;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VORR_i_T1A1_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b11111000 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b111111111 @ _ : bits(12) as op_code) if SEE < 223) = {
    SEE = 223;
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    imm12 : bits(12) = op_code[11 .. 0];
    PLD_l_T1_A_decode(U, W, imm12)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 224) = {
    SEE = 224;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSHL_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b1001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 225) = {
    SEE = 225;
    op : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_i_T1A1_A_decode(op, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b11011110 @ _ : bits(8) as op_code) if SEE < 226) = {
    SEE = 226;
    imm8 : bits(8) = op_code[7 .. 0];
    UDF_T1_A_decode(imm8)
}

function clause decode32 ((_ : bits(16) @ 0b01100 @ _ : bits(11) as op_code) if SEE < 227) = {
    SEE = 227;
    imm5 : bits(5) = op_code[10 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    STR_i_T1_A_decode(imm5, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 228) = {
    SEE = 228;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    LDRD_r_A1_A_decode(cond, P, U, W, Rn, Rt, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01101011 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 229) = {
    SEE = 229;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    REV_A1_A_decode(cond, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b00001 @ _ : bits(11) as op_code) if SEE < 230) = {
    SEE = 230;
    imm5 : bits(5) = op_code[10 .. 6];
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    LSR_i_T1_A_decode(imm5, Rm, Rd)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b00011 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 231) = {
    SEE = 231;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ORN_i_T1_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 232) = {
    SEE = 232;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCEQ_r_T2_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b1110 @ _ : bits(6) @ 0b10 @ _ : bits(2) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 233) = {
    SEE = 233;
    D : bits(1) = [op_code[22]];
    RM : bits(2) = op_code[17 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTA_vfp_T1_A_decode(D, RM, Vd, size, M, Vm)
}

function clause decode32 ((0b11101011000 @ _ : bits(1) @ 0b1101 @ _ : bits(16) as op_code) if SEE < 234) = {
    SEE = 234;
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    ADD_SP_r_T3_A_decode(S, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b111 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 235) = {
    SEE = 235;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[18]];
    U : bits(1) = [op_code[16]];
    Vd : bits(4) = op_code[15 .. 12];
    sf : bits(2) = op_code[9 .. 8];
    sx : bits(1) = [op_code[7]];
    i : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VCVT_xv_A1_A_decode(cond, D, op, U, Vd, sf, sx, i, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b010 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 236) = {
    SEE = 236;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    STRHT_A2pre_A_decode(cond, U, Rn, Rt, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 237) = {
    SEE = 237;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADDL_T1A1_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111110110110 @ _ : bits(12) @ 0b000 @ _ : bits(5) as op_code) if SEE < 238) = {
    SEE = 238;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    R : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMMLS_T1_A_decode(Rn, Ra, Rd, R, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b100 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 239) = {
    SEE = 239;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLT_i_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b11 @ _ : bits(2) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 240) = {
    SEE = 240;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[9 .. 8];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_xs_T1_A_decode(U, D, imm6, Vd, op, Q, M, Vm)
}

function clause decode32 ((0b1111000100000001 @ _ : bits(8) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 241) = {
    SEE = 241;
    E : bits(1) = [op_code[9]];
    SETEND_A1_A_decode(E)
}

function clause decode32 ((_ : bits(4) @ 0b0000011 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 242) = {
    SEE = 242;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    RSB_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b111 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 243) = {
    SEE = 243;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRHT_A1pre_A_decode(cond, U, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 244) = {
    SEE = 244;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0010010 @ _ : bits(21) as op_code) if SEE < 245) = {
    SEE = 245;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    SUB_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b0000001 @ _ : bits(13) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 246) = {
    SEE = 246;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    MLA_A1_A_decode(cond, S, Rd, Ra, Rm, Rn)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0111 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 247) = {
    SEE = 247;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABD_i_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b11110011100 @ _ : bits(5) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(6) @ 0b0 @ _ : bits(5) as op_code) if SEE < 248) = {
    SEE = 248;
    R : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    mask : bits(4) = op_code[11 .. 8];
    MSR_r_T1_AS_decode(R, Rn, mask)
}

function clause decode32 ((0b111010101001 @ _ : bits(8) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 249) = {
    SEE = 249;
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    TEQ_r_T1_A_decode(Rn, imm3, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010 @ _ : bits(1) @ 0b10 @ _ : bits(10) @ 0b0 @ _ : bits(1) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 250) = {
    SEE = 250;
    cond : bits(4) = op_code[31 .. 28];
    R : bits(1) = [op_code[22]];
    mask : bits(4) = op_code[19 .. 16];
    Rn : bits(4) = op_code[3 .. 0];
    MSR_r_A1_AS_decode(cond, R, mask, Rn)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b111 @ _ : bits(7) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 251) = {
    SEE = 251;
    D : bits(1) = [op_code[22]];
    opc2 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_iv_T1_A_decode(D, opc2, Vd, size, op, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b010001111 @ _ : bits(7) as op_code) if SEE < 252) = {
    SEE = 252;
    Rm : bits(4) = op_code[6 .. 3];
    BLX_r_T1_A_decode(Rm)
}

function clause decode32 ((0b11111001 @ _ : bits(1) @ 0b00111111111 @ _ : bits(12) as op_code) if SEE < 253) = {
    SEE = 253;
    U : bits(1) = [op_code[23]];
    imm12 : bits(12) = op_code[11 .. 0];
    PLI_i_T3_A_decode(U, imm12)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b1010 @ _ : bits(4) as op_code) if SEE < 254) = {
    SEE = 254;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    STL_T1_A_decode(Rn, Rt)
}

function clause decode32 ((0b111100101 @ _ : bits(1) @ 0b11 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 255) = {
    SEE = 255;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    imm4 : bits(4) = op_code[11 .. 8];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VEXT_T1A1_A_decode(D, Vn, Vd, imm4, N, Q, M, Vm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1001 @ _ : bits(8) as op_code) if SEE < 256) = {
    SEE = 256;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01111000 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 257) = {
    SEE = 257;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    USADA8_A1_A_decode(cond, Rd, Ra, Rm, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b01101000 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 258) = {
    SEE = 258;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    SXTAB16_A1_A_decode(cond, Rn, Rd, rotate, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 259) = {
    SEE = 259;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b10100 @ _ : bits(11) as op_code) if SEE < 260) = {
    SEE = 260;
    Rd : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADR_T1_A_decode(Rd, imm8)
}

function clause decode32 ((0b111111111 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 261) = {
    SEE = 261;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSLI_T1A1_A_decode(D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b11111001 @ _ : bits(1) @ 0b0011111 @ _ : bits(16) as op_code) if SEE < 262) = {
    SEE = 262;
    U : bits(1) = [op_code[23]];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRSB_l_T1_A_decode(U, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b00011111 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 263) = {
    SEE = 263;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDREXH_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1000 @ _ : bits(8) as op_code) if SEE < 264) = {
    SEE = 264;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000111 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 265) = {
    SEE = 265;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    RSC_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100110 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 266) = {
    SEE = 266;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UQSAX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b10 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 267) = {
    SEE = 267;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[9]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMLAL_T1A1pre_A_decode(D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b110110 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 268) = {
    SEE = 268;
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    msb : bits(5) = op_code[4 .. 0];
    BFI_T1_A_decode(Rn, imm3, Rd, imm2, msb)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 269) = {
    SEE = 269;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256H2_T1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 270) = {
    SEE = 270;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1SU0_T1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 271) = {
    SEE = 271;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0101 @ _ : bits(8) as op_code) if SEE < 272) = {
    SEE = 272;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 273) = {
    SEE = 273;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b1010 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 274) = {
    SEE = 274;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_s_T2A2_A_decode(U, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1001 @ _ : bits(8) as op_code) if SEE < 275) = {
    SEE = 275;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01101010 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 276) = {
    SEE = 276;
    cond : bits(4) = op_code[31 .. 28];
    sat_imm : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rn : bits(4) = op_code[3 .. 0];
    SSAT16_A1_A_decode(cond, sat_imm, Rd, Rn)
}

function clause decode32 ((0b111110001001 @ _ : bits(20) as op_code) if SEE < 277) = {
    SEE = 277;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRB_i_T2_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b1100 @ _ : bits(1) @ 0b0 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 278) = {
    SEE = 278;
    sh : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    sat_imm : bits(5) = op_code[4 .. 0];
    SSAT_T1_A_decode(sh, Rn, imm3, Rd, imm2, sat_imm)
}

function clause decode32 ((0b11101110000 @ _ : bits(9) @ 0b1001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 279) = {
    SEE = 279;
    op : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    VMOV_h_T1_A_decode(op, Vn, Rt, N)
}

function clause decode32 ((_ : bits(16) @ 0b1011101000 @ _ : bits(6) as op_code) if SEE < 280) = {
    SEE = 280;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    REV_T1_A_decode(Rm, Rd)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 281) = {
    SEE = 281;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHL_i_T1A1_A_decode(D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b100110 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 282) = {
    SEE = 282;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    STMIB_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b01100110 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 283) = {
    SEE = 283;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UQADD16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b110000 @ _ : bits(4) @ 0b101001 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 284) = {
    SEE = 284;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMOVX_A1_A_decode(D, Vd, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 285) = {
    SEE = 285;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLS_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00010010 @ _ : bits(12) @ 0b1 @ _ : bits(1) @ 0b00 @ _ : bits(4) as op_code) if SEE < 286) = {
    SEE = 286;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[6]];
    Rn : bits(4) = op_code[3 .. 0];
    SMLAWB_A1_A_decode(cond, Rd, Ra, Rm, M, Rn)
}

function clause decode32 ((0b11101011110 @ _ : bits(21) as op_code) if SEE < 287) = {
    SEE = 287;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    RSB_r_T1_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1011111100110000 as op_code) if SEE < 288) = {
    SEE = 288;
    WFI_T1_A_decode()
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 289) = {
    SEE = 289;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VTRN_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111011111 @ _ : bits(1) @ 0b11 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 290) = {
    SEE = 290;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    imm4 : bits(4) = op_code[11 .. 8];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VEXT_T1A1_A_decode(D, Vn, Vd, imm4, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b1011 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b1 @ _ : bits(8) as op_code) if SEE < 291) = {
    SEE = 291;
    op : bits(1) = [op_code[11]];
    i : bits(1) = [op_code[9]];
    imm5 : bits(5) = op_code[7 .. 3];
    Rn : bits(3) = op_code[2 .. 0];
    CBNZ_T1_A_decode(op, i, imm5, Rn)
}

function clause decode32 ((_ : bits(16) @ 0b01000110 @ _ : bits(8) as op_code) if SEE < 292) = {
    SEE = 292;
    D : bits(1) = [op_code[7]];
    Rm : bits(4) = op_code[6 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    MOV_r_T1_A_decode(D, Rm, Rd)
}

function clause decode32 ((_ : bits(4) @ 0b00010110 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 293) = {
    SEE = 293;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    CLZ_A1_A_decode(cond, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b11100 @ _ : bits(11) as op_code) if SEE < 294) = {
    SEE = 294;
    imm11 : bits(11) = op_code[10 .. 0];
    B_T2_A_decode(imm11)
}

function clause decode32 ((_ : bits(4) @ 0b00010101 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 295) = {
    SEE = 295;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    CMP_r_A1_A_decode(cond, Rn, imm5, typ, Rm)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 296) = {
    SEE = 296;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SHADD8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 297) = {
    SEE = 297;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0111 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 298) = {
    SEE = 298;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABD_i_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b1000 @ _ : bits(4) as op_code) if SEE < 299) = {
    SEE = 299;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    STLB_T1_A_decode(Rn, Rt)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0100 @ _ : bits(8) as op_code) if SEE < 300) = {
    SEE = 300;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111111100 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 301) = {
    SEE = 301;
    op1 : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    op2 : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    U : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VDOT_s_A1_A_decode(op1, D, op2, Vn, Vd, N, Q, M, U, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0010010 @ _ : bits(1) @ 0b1101 @ _ : bits(16) as op_code) if SEE < 302) = {
    SEE = 302;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    SUB_SP_i_A1_A_decode(cond, S, Rd, imm12)
}

function clause decode32 ((0b111111100 @ _ : bits(11) @ 0b10 @ _ : bits(3) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 303) = {
    SEE = 303;
    D : bits(1) = [op_code[22]];
    cc : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSEL_T1_A_decode(D, cc, Vn, Vd, size, N, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 304) = {
    SEE = 304;
    Q : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[10]];
    F : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_s_A1_A_decode(Q, D, size, Vn, Vd, op, F, N, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 305) = {
    SEE = 305;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T3A3pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((0b111110001101 @ _ : bits(20) as op_code) if SEE < 306) = {
    SEE = 306;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDR_i_T3_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((0b1111100 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b1 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 307) = {
    SEE = 307;
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    RFE_A1_AS_decode(P, U, W, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b00011110 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 308) = {
    SEE = 308;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STREXH_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b01111000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 309) = {
    SEE = 309;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    USAD8_A1_A_decode(cond, Rd, Rm, Rn)
}

function clause decode32 ((0b111110000100 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 310) = {
    SEE = 310;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    STR_i_T4_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((0b111110110111 @ _ : bits(12) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 311) = {
    SEE = 311;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    USADA8_T1_A_decode(Rn, Ra, Rd, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1011 @ _ : bits(8) as op_code) if SEE < 312) = {
    SEE = 312;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b00000000001 as op_code) if SEE < 313) = {
    SEE = 313;
    YIELD_T2_A_decode()
}

function clause decode32 ((0b111110100010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 314) = {
    SEE = 314;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SXTAB16_T1_A_decode(Rn, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 315) = {
    SEE = 315;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRH_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b111 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 316) = {
    SEE = 316;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[18]];
    U : bits(1) = [op_code[16]];
    Vd : bits(4) = op_code[15 .. 12];
    sf : bits(2) = op_code[9 .. 8];
    sx : bits(1) = [op_code[7]];
    i : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VCVT_xv_T1_A_decode(D, op, U, Vd, sf, sx, i, imm4)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0001 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 317) = {
    SEE = 317;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRHADD_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b110 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 318) = {
    SEE = 318;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMVN_i_T3A3_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b01100101 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 319) = {
    SEE = 319;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    USUB16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 320) = {
    SEE = 320;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCEQ_r_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b001100100000 @ _ : bits(8) @ 0b00000100 as op_code) if SEE < 321) = {
    SEE = 321;
    cond : bits(4) = op_code[31 .. 28];
    SEV_A1_A_decode(cond)
}

function clause decode32 ((0b111110000011 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 322) = {
    SEE = 322;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRHT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b11101110000 @ _ : bits(9) @ 0b1010 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 323) = {
    SEE = 323;
    op : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    VMOV_s_T1_A_decode(op, Vn, Rt, N)
}

function clause decode32 ((_ : bits(16) @ 0b0001111 @ _ : bits(9) as op_code) if SEE < 324) = {
    SEE = 324;
    imm3 : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    SUB_i_T1_A_decode(imm3, Rn, Rd)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0100 @ _ : bits(8) as op_code) if SEE < 325) = {
    SEE = 325;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111110010011 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 326) = {
    SEE = 326;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRSHT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b11111110 @ _ : bits(12) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 327) = {
    SEE = 327;
    S : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    rot : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCMLA_idx_T1_A_decode(S, D, rot, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b00110 @ _ : bits(11) as op_code) if SEE < 328) = {
    SEE = 328;
    Rdn : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADD_i_T2_A_decode(Rdn, imm8)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 329) = {
    SEE = 329;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(20) as op_code) if SEE < 330) = {
    SEE = 330;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110101101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 331) = {
    SEE = 331;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    USUB16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b10 @ _ : bits(3) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 332) = {
    SEE = 332;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VDIV_A1_A_decode(cond, D, Vn, Vd, size, N, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b101100001 @ _ : bits(7) as op_code) if SEE < 333) = {
    SEE = 333;
    imm7 : bits(7) = op_code[6 .. 0];
    SUB_SP_i_T1_A_decode(imm7)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 334) = {
    SEE = 334;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b101010 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 335) = {
    SEE = 335;
    i : bits(1) = [op_code[26]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    SUB_i_T4_A_decode(i, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 336) = {
    SEE = 336;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UQADD16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 337) = {
    SEE = 337;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUB_f_A1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b010 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 338) = {
    SEE = 338;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    STRB_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm12)
}

function clause decode32 ((0b111110110011 @ _ : bits(12) @ 0b000 @ _ : bits(5) as op_code) if SEE < 339) = {
    SEE = 339;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMLAWB_T1_A_decode(Rn, Ra, Rd, M, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b11111 @ _ : bits(8) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 340) = {
    SEE = 340;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRH_l_A1_A_decode(cond, P, U, W, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b1011 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 341) = {
    SEE = 341;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULL_T2A2_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100011 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 342) = {
    SEE = 342;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SHSUB8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010010 @ _ : bits(12) @ 0b1 @ _ : bits(1) @ 0b10 @ _ : bits(4) as op_code) if SEE < 343) = {
    SEE = 343;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[6]];
    Rn : bits(4) = op_code[3 .. 0];
    SMULWB_A1_A_decode(cond, Rd, Rm, M, Rn)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 344) = {
    SEE = 344;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGE_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b10000011010 @ _ : bits(15) as op_code) if SEE < 345) = {
    SEE = 345;
    i : bits(1) = [op_code[26]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADD_SP_i_T4_A_decode(i, imm3, Rd, imm8)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 346) = {
    SEE = 346;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLS_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 347) = {
    SEE = 347;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSQRTS_T1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b110000 @ _ : bits(4) @ 0b101001 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 348) = {
    SEE = 348;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMOVX_T1_A_decode(D, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0010101 @ _ : bits(21) as op_code) if SEE < 349) = {
    SEE = 349;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    ADC_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((0b111011110 @ _ : bits(11) @ 0b1100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 350) = {
    SEE = 350;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFMA_T1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0110 @ _ : bits(1) @ 0b011 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 351) = {
    SEE = 351;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    LDRT_A2pre_A_decode(cond, U, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b101 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 352) = {
    SEE = 352;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMLAL_T1A1pre_A_decode(D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1001 @ _ : bits(8) as op_code) if SEE < 353) = {
    SEE = 353;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b110010 @ _ : bits(4) @ 0b0000 @ _ : bits(4) @ 0b00 @ _ : bits(6) as op_code) if SEE < 354) = {
    SEE = 354;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    sat_imm : bits(4) = op_code[3 .. 0];
    SSAT16_T1_A_decode(Rn, Rd, sat_imm)
}

function clause decode32 ((_ : bits(16) @ 0b1011101011 @ _ : bits(6) as op_code) if SEE < 355) = {
    SEE = 355;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    REVSH_T1_A_decode(Rm, Rd)
}

function clause decode32 ((_ : bits(16) @ 0b10000 @ _ : bits(11) as op_code) if SEE < 356) = {
    SEE = 356;
    imm5 : bits(5) = op_code[10 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    STRH_i_T1_A_decode(imm5, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b01100111 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 357) = {
    SEE = 357;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UHSUB16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b1100 @ _ : bits(4) as op_code) if SEE < 358) = {
    SEE = 358;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[3 .. 0];
    STLEXB_T1_A_decode(Rn, Rt, Rd)
}

function clause decode32 ((_ : bits(16) @ 0b1011010 @ _ : bits(9) as op_code) if SEE < 359) = {
    SEE = 359;
    M : bits(1) = [op_code[8]];
    register_list : bits(8) = op_code[7 .. 0];
    PUSH_T1_A_decode(M, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b010 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 360) = {
    SEE = 360;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRB_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm12)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1011 @ _ : bits(8) as op_code) if SEE < 361) = {
    SEE = 361;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0100001010 @ _ : bits(6) as op_code) if SEE < 362) = {
    SEE = 362;
    Rm : bits(3) = op_code[5 .. 3];
    Rn : bits(3) = op_code[2 .. 0];
    CMP_r_T1_A_decode(Rm, Rn)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b100 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 363) = {
    SEE = 363;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSHRN_T1A1_A_decode(U, D, imm6, Vd, op, M, Vm)
}

function clause decode32 ((0b11110110 @ _ : bits(1) @ 0b101 @ _ : bits(4) @ 0b1111 @ _ : bits(7) @ 0b0 @ _ : bits(4) as op_code) if SEE < 364) = {
    SEE = 364;
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    PLI_r_A1_A_decode(U, Rn, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010010 @ _ : bits(12) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 365) = {
    SEE = 365;
    cond : bits(4) = op_code[31 .. 28];
    Rm : bits(4) = op_code[3 .. 0];
    BXJ_A1_A_decode(cond, Rm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 366) = {
    SEE = 366;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b01001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 367) = {
    SEE = 367;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTX_asimd_T1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 368) = {
    SEE = 368;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABA_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 369) = {
    SEE = 369;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAH_T1_A_decode(Rn, Rt)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 370) = {
    SEE = 370;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMVN_i_T2A2_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b111110110111 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 371) = {
    SEE = 371;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    USAD8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111110000101 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 372) = {
    SEE = 372;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    LDR_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((0b111110101011 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1000 @ _ : bits(4) as op_code) if SEE < 373) = {
    SEE = 373;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    CLZ_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010010 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 374) = {
    SEE = 374;
    cond : bits(4) = op_code[31 .. 28];
    imm12 : bits(12) = op_code[19 .. 8];
    imm4 : bits(4) = op_code[3 .. 0];
    BKPT_A1_A_decode(cond, imm12, imm4)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01111 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 375) = {
    SEE = 375;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQNEG_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 376) = {
    SEE = 376;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQADD_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b1010 @ _ : bits(24) as op_code) if SEE < 377) = {
    SEE = 377;
    cond : bits(4) = op_code[31 .. 28];
    imm24 : bits(24) = op_code[23 .. 0];
    B_A1_A_decode(cond, imm24)
}

function clause decode32 ((_ : bits(4) @ 0b0001100 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 378) = {
    SEE = 378;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    ORR_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100110 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 379) = {
    SEE = 379;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UQASX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b10001 @ _ : bits(11) as op_code) if SEE < 380) = {
    SEE = 380;
    imm5 : bits(5) = op_code[10 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDRH_i_T1_A_decode(imm5, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b00010 @ _ : bits(1) @ 0b10 @ _ : bits(10) @ 0b1 @ _ : bits(1) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 381) = {
    SEE = 381;
    cond : bits(4) = op_code[31 .. 28];
    R : bits(1) = [op_code[22]];
    M1 : bits(4) = op_code[19 .. 16];
    M : bits(1) = [op_code[8]];
    Rn : bits(4) = op_code[3 .. 0];
    MSR_br_A1_AS_decode(cond, R, M1, M, Rn)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 382) = {
    SEE = 382;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T3A3_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111111000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 383) = {
    SEE = 383;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    U : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VDOT_A1_A_decode(D, Vn, Vd, N, Q, M, U, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001100 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 384) = {
    SEE = 384;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESE_A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 385) = {
    SEE = 385;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    op : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VPMAX_i_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, op, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b011 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b1 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 386) = {
    SEE = 386;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    LDR_r_A1_A_decode(cond, P, U, W, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b10111110 @ _ : bits(8) as op_code) if SEE < 387) = {
    SEE = 387;
    imm8 : bits(8) = op_code[7 .. 0];
    BKPT_T1_A_decode(imm8)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 388) = {
    SEE = 388;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUB_f_T1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111010100001 @ _ : bits(8) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 389) = {
    SEE = 389;
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    TST_r_T2_A_decode(Rn, imm3, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0110 @ _ : bits(1) @ 0b111 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 390) = {
    SEE = 390;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    LDRBT_A2pre_A_decode(cond, U, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0100001100 @ _ : bits(6) as op_code) if SEE < 391) = {
    SEE = 391;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    ORR_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b100 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 392) = {
    SEE = 392;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSHRN_T1A1_A_decode(U, D, imm6, Vd, op, M, Vm)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1010 @ _ : bits(4) as op_code) if SEE < 393) = {
    SEE = 393;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QSUB_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00011111 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 394) = {
    SEE = 394;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAEXH_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b111110101100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 395) = {
    SEE = 395;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SHSUB8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01110000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b01 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 396) = {
    SEE = 396;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMUSD_A1_A_decode(cond, Rd, Rm, M, Rn)
}

function clause decode32 ((0b111100111 @ _ : bits(11) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 397) = {
    SEE = 397;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSUBHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b01110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 398) = {
    SEE = 398;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    RSB_i_T2_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 399) = {
    SEE = 399;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1M_A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110101010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 400) = {
    SEE = 400;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UQASX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b1010 @ _ : bits(4) as op_code) if SEE < 401) = {
    SEE = 401;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDA_T1_A_decode(Rn, Rt)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 402) = {
    SEE = 402;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGE_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(4) @ 0b1 @ _ : bits(15) as op_code) if SEE < 403) = {
    SEE = 403;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(15) = op_code[14 .. 0];
    LDM_e_A1_AS_decode(cond, P, U, W, Rn, register_list)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b100001 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 404) = {
    SEE = 404;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSHRN_T1A1_A_decode(D, imm6, Vd, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 405) = {
    SEE = 405;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSRA_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0010001 @ _ : bits(21) as op_code) if SEE < 406) = {
    SEE = 406;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    EOR_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 407) = {
    SEE = 407;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(15) = op_code[14 .. 0];
    LDM_u_A1_AS_decode(cond, P, U, Rn, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b00110111 @ _ : bits(20) as op_code) if SEE < 408) = {
    SEE = 408;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    CMN_i_A1_A_decode(cond, Rn, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b01100010 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 409) = {
    SEE = 409;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QASX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0010100 @ _ : bits(21) as op_code) if SEE < 410) = {
    SEE = 410;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    ADD_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b01101110 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 411) = {
    SEE = 411;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    UXTAB_A1_A_decode(cond, Rn, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b011011101111 @ _ : bits(8) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 412) = {
    SEE = 412;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    UXTB_A1_A_decode(cond, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b110001 @ _ : bits(4) @ 0b10 @ _ : bits(2) @ 0b11 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 413) = {
    SEE = 413;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSQRT_A1_A_decode(cond, D, Vd, size, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00011000 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 414) = {
    SEE = 414;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STLEX_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b00011010 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 415) = {
    SEE = 415;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STREXD_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((0b111110110011 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b000 @ _ : bits(5) as op_code) if SEE < 416) = {
    SEE = 416;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMULWB_T1_A_decode(Rn, Rd, M, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b001 @ _ : bits(4) @ 0b1 @ _ : bits(4) @ 0b1111 @ _ : bits(12) as op_code) if SEE < 417) = {
    SEE = 417;
    cond : bits(4) = op_code[31 .. 28];
    opcode : bits(4) = op_code[24 .. 21];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    SUBS_PC_A1pre_AS_decode(cond, opcode, Rn, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b0000111 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 418) = {
    SEE = 418;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    RSC_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 419) = {
    SEE = 419;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    REV16_T2_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0011 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 420) = {
    SEE = 420;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGT_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01010 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 421) = {
    SEE = 421;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCNT_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 422) = {
    SEE = 422;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUB_i_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 423) = {
    SEE = 423;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABA_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b01110 @ _ : bits(11) as op_code) if SEE < 424) = {
    SEE = 424;
    imm5 : bits(5) = op_code[10 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    STRB_i_T1_A_decode(imm5, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b01110001 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 425) = {
    SEE = 425;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    SDIV_A1_A_decode(cond, Rd, Ra, Rm, Rn)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 426) = {
    SEE = 426;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLAH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 427) = {
    SEE = 427;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSWP_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b10 @ _ : bits(3) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 428) = {
    SEE = 428;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VDIV_T1_A_decode(D, Vn, Vd, size, N, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0010 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 429) = {
    SEE = 429;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSHR_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b00010 @ _ : bits(1) @ 0b11110 @ _ : bits(15) as op_code) if SEE < 430) = {
    SEE = 430;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    MOV_i_T2pre_A_decode(i, S, imm3, Rd, imm8)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 431) = {
    SEE = 431;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMVN_r_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01101010 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 432) = {
    SEE = 432;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    SXTAB_A1_A_decode(cond, Rn, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100101 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 433) = {
    SEE = 433;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UADD8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111010000100 @ _ : bits(20) as op_code) if SEE < 434) = {
    SEE = 434;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    STREX_T1_A_decode(Rn, Rt, Rd, imm8)
}

function clause decode32 ((0b111100111100 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(12) as op_code) if SEE < 435) = {
    SEE = 435;
    Rm : bits(4) = op_code[19 .. 16];
    BXJ_T1_A_decode(Rm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 436) = {
    SEE = 436;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b01010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 437) = {
    SEE = 437;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADC_i_T1_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b00011011 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 438) = {
    SEE = 438;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDREXD_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b100100 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 439) = {
    SEE = 439;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    LDMDB_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 440) = {
    SEE = 440;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLZ_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111110101101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 441) = {
    SEE = 441;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UHSUB16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 442) = {
    SEE = 442;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VAND_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000110 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 443) = {
    SEE = 443;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    SBC_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 444) = {
    SEE = 444;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110010011 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 445) = {
    SEE = 445;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    LDRSH_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b1011 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 446) = {
    SEE = 446;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULL_T2A2_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111100111011 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(4) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 447) = {
    SEE = 447;
    SB_T1_A_decode()
}

function clause decode32 ((_ : bits(4) @ 0b0010000 @ _ : bits(21) as op_code) if SEE < 448) = {
    SEE = 448;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    AND_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 449) = {
    SEE = 449;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110010001 @ _ : bits(4) @ 0b1111000000 @ _ : bits(6) as op_code) if SEE < 450) = {
    SEE = 450;
    Rn : bits(4) = op_code[19 .. 16];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    PLI_r_T1_A_decode(Rn, imm2, Rm)
}

function clause decode32 ((0b1111110 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 451) = {
    SEE = 451;
    rot : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCADD_A1_A_decode(rot, D, S, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0100001110 @ _ : bits(6) as op_code) if SEE < 452) = {
    SEE = 452;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    BIC_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((_ : bits(4) @ 0b0011101 @ _ : bits(21) as op_code) if SEE < 453) = {
    SEE = 453;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    MOV_i_A1pre_A_decode(cond, S, Rd, imm12)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b0110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 454) = {
    SEE = 454;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADAL_T1A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100110 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 455) = {
    SEE = 455;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UQADD8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 456) = {
    SEE = 456;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rt2 : bits(4) = op_code[11 .. 8];
    LDREXD_T1_A_decode(Rn, Rt, Rt2)
}

function clause decode32 ((0b111110110100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b000 @ _ : bits(5) as op_code) if SEE < 457) = {
    SEE = 457;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMUSD_T1_A_decode(Rn, Rd, M, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b110 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 458) = {
    SEE = 458;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABS_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0100000110 @ _ : bits(6) as op_code) if SEE < 459) = {
    SEE = 459;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    SBC_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 460) = {
    SEE = 460;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1M_T1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 461) = {
    SEE = 461;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSHL_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b00000 @ _ : bits(11) as op_code) if SEE < 462) = {
    SEE = 462;
    imm5 : bits(5) = op_code[10 .. 6];
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    LSL_i_T1_A_decode(imm5, Rm, Rd)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 463) = {
    SEE = 463;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSRA_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b11 @ _ : bits(4) @ 0b010 @ _ : bits(1) @ 0b0 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 464) = {
    SEE = 464;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[8]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRECPE_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 465) = {
    SEE = 465;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUBHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b010001 @ _ : bits(4) @ 0b0 @ _ : bits(3) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 466) = {
    SEE = 466;
    i : bits(1) = [op_code[26]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    CMN_i_T1_A_decode(i, Rn, imm3, imm8)
}

function clause decode32 ((0b111110010001 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 467) = {
    SEE = 467;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    LDRSB_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((0b1110100100 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 468) = {
    SEE = 468;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    P : bits(1) = [op_code[15]];
    M : bits(1) = [op_code[14]];
    register_list : bits(14) = op_code[13 .. 0];
    LDMDB_T1_A_decode(W, Rn, P, M, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b00010000 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 469) = {
    SEE = 469;
    cond : bits(4) = op_code[31 .. 28];
    imm12 : bits(12) = op_code[19 .. 8];
    imm4 : bits(4) = op_code[3 .. 0];
    HLT_A1_A_decode(cond, imm12, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b01100001 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 470) = {
    SEE = 470;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SSUB16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b1110100000 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 471) = {
    SEE = 471;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    RFE_T1_AS_decode(W, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b01101111 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 472) = {
    SEE = 472;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    RBIT_A1_A_decode(cond, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0011111 @ _ : bits(21) as op_code) if SEE < 473) = {
    SEE = 473;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    MVN_i_A1_A_decode(cond, S, Rd, imm12)
}

function clause decode32 ((0b111101010111 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 474) = {
    SEE = 474;
    option_name : bits(4) = op_code[3 .. 0];
    DMB_A1_A_decode(option_name)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b00100 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 475) = {
    SEE = 475;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    EOR_i_T1_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b00010100 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 476) = {
    SEE = 476;
    cond : bits(4) = op_code[31 .. 28];
    imm12 : bits(12) = op_code[19 .. 8];
    imm4 : bits(4) = op_code[3 .. 0];
    HVC_A1_A_decode(cond, imm12, imm4)
}

function clause decode32 ((0b111110110000 @ _ : bits(12) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 477) = {
    SEE = 477;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    MLA_T1_A_decode(Rn, Ra, Rd, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001110 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 478) = {
    SEE = 478;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESMC_A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 479) = {
    SEE = 479;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAXNM_T2A2pre_A_decode(D, Vn, Vd, size, N, op, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0100000111 @ _ : bits(6) as op_code) if SEE < 480) = {
    SEE = 480;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    ROR_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((_ : bits(4) @ 0b00110100 @ _ : bits(20) as op_code) if SEE < 481) = {
    SEE = 481;
    cond : bits(4) = op_code[31 .. 28];
    imm4 : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    MOVT_A1_A_decode(cond, imm4, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b0001111 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 482) = {
    SEE = 482;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    MVN_rr_A1_A_decode(cond, S, Rd, Rs, typ, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 483) = {
    SEE = 483;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMVN_r_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0011 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 484) = {
    SEE = 484;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGT_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b011 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 485) = {
    SEE = 485;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    LDRSBT_A2pre_A_decode(cond, U, Rn, Rt, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0111101 @ _ : bits(14) @ 0b101 @ _ : bits(4) as op_code) if SEE < 486) = {
    SEE = 486;
    cond : bits(4) = op_code[31 .. 28];
    widthm1 : bits(5) = op_code[20 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    lsb : bits(5) = op_code[11 .. 7];
    Rn : bits(4) = op_code[3 .. 0];
    SBFX_A1_A_decode(cond, widthm1, Rd, lsb, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b01110100 @ _ : bits(12) @ 0b00 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 487) = {
    SEE = 487;
    cond : bits(4) = op_code[31 .. 28];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMLALD_A1_A_decode(cond, RdHi, RdLo, Rm, M, Rn)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 488) = {
    SEE = 488;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCLZ_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111110100101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 489) = {
    SEE = 489;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    UXTAB_T1_A_decode(Rn, Rd, rotate, Rm)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b1110 @ _ : bits(4) as op_code) if SEE < 490) = {
    SEE = 490;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[3 .. 0];
    STLEX_T1_A_decode(Rn, Rt, Rd)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 491) = {
    SEE = 491;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rt2 : bits(4) = op_code[11 .. 8];
    Rd : bits(4) = op_code[3 .. 0];
    STREXD_T1_A_decode(Rn, Rt, Rt2, Rd)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(4) @ 0b1 @ _ : bits(4) @ 0b1111 @ _ : bits(7) @ 0b0 @ _ : bits(4) as op_code) if SEE < 492) = {
    SEE = 492;
    cond : bits(4) = op_code[31 .. 28];
    opcode : bits(4) = op_code[24 .. 21];
    Rn : bits(4) = op_code[19 .. 16];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    SUBS_PC_A2pre_AS_decode(cond, opcode, Rn, imm5, typ, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b1101 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 493) = {
    SEE = 493;
    Q : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMULH_T2A2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b1 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 494) = {
    SEE = 494;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    LDRSH_r_A1_A_decode(cond, P, U, W, Rn, Rt, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b00000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 495) = {
    SEE = 495;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    AND_i_T1_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b1100 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 496) = {
    SEE = 496;
    Q : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULH_T2A2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b101101100101 @ _ : bits(4) as op_code) if SEE < 497) = {
    SEE = 497;
    E : bits(1) = [op_code[3]];
    SETEND_T1_A_decode(E)
}

function clause decode32 ((0b111110101010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 498) = {
    SEE = 498;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QASX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111100010001 @ _ : bits(12) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 499) = {
    SEE = 499;
    imm1 : bits(1) = [op_code[9]];
    SETPAN_A1_A_decode(imm1)
}

function clause decode32 ((0b1111110 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 500) = {
    SEE = 500;
    rot : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCADD_T1_A_decode(rot, D, S, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00110 @ _ : bits(1) @ 0b10 @ _ : bits(20) as op_code) if SEE < 501) = {
    SEE = 501;
    cond : bits(4) = op_code[31 .. 28];
    R : bits(1) = [op_code[22]];
    mask : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    MSR_i_A1_AS_decode(cond, R, mask, imm12)
}

function clause decode32 ((0b111111000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 502) = {
    SEE = 502;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    U : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VDOT_T1_A_decode(D, Vn, Vd, N, Q, M, U, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b0010 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 503) = {
    SEE = 503;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[7 .. 6];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQMOVN_T1A1_A_decode(D, size, Vd, op, M, Vm)
}

function clause decode32 ((0b111110000100 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 504) = {
    SEE = 504;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    STR_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 505) = {
    SEE = 505;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLAH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b1011001011 @ _ : bits(6) as op_code) if SEE < 506) = {
    SEE = 506;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    UXTB_T1_A_decode(Rm, Rd)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b110001 @ _ : bits(4) @ 0b10 @ _ : bits(2) @ 0b11 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 507) = {
    SEE = 507;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSQRT_T1_A_decode(D, Vd, size, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001100 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 508) = {
    SEE = 508;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESE_T1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b011011 @ _ : bits(4) @ 0b0 @ _ : bits(3) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 509) = {
    SEE = 509;
    i : bits(1) = [op_code[26]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    CMP_i_T2_A_decode(i, Rn, imm3, imm8)
}

function clause decode32 ((_ : bits(16) @ 0b0101100 @ _ : bits(9) as op_code) if SEE < 510) = {
    SEE = 510;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDR_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 511) = {
    SEE = 511;
    Q : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_s_A1_A_decode(Q, D, size, Vn, Vd, F, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000101 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 512) = {
    SEE = 512;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    ADC_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000111 @ _ : bits(13) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 513) = {
    SEE = 513;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    SMLAL_A1_A_decode(cond, S, RdHi, RdLo, Rm, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b110 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 514) = {
    SEE = 514;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    STRHT_A1pre_A_decode(cond, U, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((_ : bits(4) @ 0b01100001 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 515) = {
    SEE = 515;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SSUB8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b10110110000 @ _ : bits(5) as op_code) if SEE < 516) = {
    SEE = 516;
    imm1 : bits(1) = [op_code[3]];
    SETPAN_T1_A_decode(imm1)
}

function clause decode32 ((_ : bits(4) @ 0b00011110 @ _ : bits(10) @ 0b001001 @ _ : bits(4) as op_code) if SEE < 517) = {
    SEE = 517;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[3 .. 0];
    STLH_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b111100100 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 518) = {
    SEE = 518;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VTST_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b01 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 519) = {
    SEE = 519;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(3) = op_code[9 .. 7];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTA_asimd_A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 520) = {
    SEE = 520;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VTRN_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 521) = {
    SEE = 521;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDREXH_T1_A_decode(Rn, Rt)
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 522) = {
    SEE = 522;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCEQ_r_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b00100 @ _ : bits(11) as op_code) if SEE < 523) = {
    SEE = 523;
    Rd : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    MOV_i_T1pre_A_decode(Rd, imm8)
}

function clause decode32 ((0b111110010001 @ _ : bits(4) @ 0b11111100 @ _ : bits(8) as op_code) if SEE < 524) = {
    SEE = 524;
    Rn : bits(4) = op_code[19 .. 16];
    imm8 : bits(8) = op_code[7 .. 0];
    PLI_i_T2_A_decode(Rn, imm8)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b0110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 525) = {
    SEE = 525;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADAL_T1A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0001 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 526) = {
    SEE = 526;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRHADD_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00110101 @ _ : bits(20) as op_code) if SEE < 527) = {
    SEE = 527;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    CMP_i_A1_A_decode(cond, Rn, imm12)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b101100 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 528) = {
    SEE = 528;
    i : bits(1) = [op_code[26]];
    imm4 : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    MOVT_T1_A_decode(i, imm4, imm3, Rd, imm8)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b00000000000 as op_code) if SEE < 529) = {
    SEE = 529;
    NOP_T2_A_decode()
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 530) = {
    SEE = 530;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010110 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 531) = {
    SEE = 531;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QDSUB_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 532) = {
    SEE = 532;
    Q : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[10]];
    F : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_s_T1_A_decode(Q, D, size, Vn, Vd, op, F, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00011011 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 533) = {
    SEE = 533;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAEXD_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b0000010 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 534) = {
    SEE = 534;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    SUB_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010101 @ _ : bits(12) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 535) = {
    SEE = 535;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    CMP_rr_A1_A_decode(cond, Rn, Rs, typ, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0100000100 @ _ : bits(6) as op_code) if SEE < 536) = {
    SEE = 536;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    ASR_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b10 @ _ : bits(3) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 537) = {
    SEE = 537;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    imm4H : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    VMOV_i_A2_A_decode(cond, D, imm4H, Vd, size, imm4L)
}

function clause decode32 ((_ : bits(4) @ 0b100100 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 538) = {
    SEE = 538;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    STMDB_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b0110 @ _ : bits(1) @ 0b010 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 539) = {
    SEE = 539;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    STRT_A2pre_A_decode(cond, U, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 540) = {
    SEE = 540;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUBHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100010 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 541) = {
    SEE = 541;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QSAX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010000 @ _ : bits(12) @ 0b1 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 542) = {
    SEE = 542;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[6]];
    N : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMLABB_A1_A_decode(cond, Rd, Ra, Rm, M, N, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b001100100000 @ _ : bits(8) @ 0b00000001 as op_code) if SEE < 543) = {
    SEE = 543;
    cond : bits(4) = op_code[31 .. 28];
    YIELD_A1_A_decode(cond)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0000 @ _ : bits(8) as op_code) if SEE < 544) = {
    SEE = 544;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b1110100110 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 545) = {
    SEE = 545;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    RFE_T2_AS_decode(W, Rn)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b1100 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 546) = {
    SEE = 546;
    Q : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULH_T2A2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 547) = {
    SEE = 547;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADD_f_A1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1010 @ _ : bits(4) as op_code) if SEE < 548) = {
    SEE = 548;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    RBIT_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b110 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 549) = {
    SEE = 549;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABS_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b010001001 @ _ : bits(4) @ 0b101 as op_code) if SEE < 550) = {
    SEE = 550;
    Rm : bits(4) = op_code[6 .. 3];
    ADD_SP_r_T2_A_decode(Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0101111 @ _ : bits(9) as op_code) if SEE < 551) = {
    SEE = 551;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDRSH_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((0b11111100 @ _ : bits(2) @ 0b10 @ _ : bits(8) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 552) = {
    SEE = 552;
    S : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFMAL_A1_A_decode(S, D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001100 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 553) = {
    SEE = 553;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHLL_T2A2_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b1011111101000000 as op_code) if SEE < 554) = {
    SEE = 554;
    SEV_T1_A_decode()
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b110100 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 555) = {
    SEE = 555;
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    widthm1 : bits(5) = op_code[4 .. 0];
    SBFX_T1_A_decode(Rn, imm3, Rd, imm2, widthm1)
}

function clause decode32 ((0b111100111 @ _ : bits(11) @ 0b0100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 556) = {
    SEE = 556;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSRI_T1A1_A_decode(D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0101 @ _ : bits(8) as op_code) if SEE < 557) = {
    SEE = 557;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001110 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 558) = {
    SEE = 558;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESMC_T1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b11110011100 @ _ : bits(5) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(6) @ 0b1 @ _ : bits(5) as op_code) if SEE < 559) = {
    SEE = 559;
    R : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    M1 : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    MSR_br_T1_AS_decode(R, Rn, M1, M)
}

function clause decode32 ((_ : bits(4) @ 0b01100101 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 560) = {
    SEE = 560;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UASX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 561) = {
    SEE = 561;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VORR_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110101110 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 562) = {
    SEE = 562;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UQSAX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111111100 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 563) = {
    SEE = 563;
    op1 : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    op2 : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    U : bits(1) = [op_code[4]];
    Vm : bits(4) = op_code[3 .. 0];
    VDOT_s_T1_A_decode(op1, D, op2, Vn, Vd, N, Q, M, U, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000101 @ _ : bits(13) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 564) = {
    SEE = 564;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    UMLAL_A1_A_decode(cond, S, RdHi, RdLo, Rm, Rn)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b11 @ _ : bits(4) @ 0b010 @ _ : bits(1) @ 0b0 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 565) = {
    SEE = 565;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[8]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRECPE_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100101 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 566) = {
    SEE = 566;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    USUB8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b11000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 567) = {
    SEE = 567;
    D : bits(1) = [op_code[22]];
    imm4 : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VDUP_s_T1A1_A_decode(D, imm4, Vd, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b00011 @ _ : bits(1) @ 0b11110 @ _ : bits(15) as op_code) if SEE < 568) = {
    SEE = 568;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    MVN_i_T1_A_decode(i, S, imm3, Rd, imm8)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 569) = {
    SEE = 569;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[3 .. 0];
    STREXH_T1_A_decode(Rn, Rt, Rd)
}

function clause decode32 ((0b11101011101 @ _ : bits(21) as op_code) if SEE < 570) = {
    SEE = 570;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SUB_r_T2_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b110000 @ _ : bits(4) @ 0b101011 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 571) = {
    SEE = 571;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VINS_A1_A_decode(D, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00000110 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 572) = {
    SEE = 572;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    MLS_A1_A_decode(cond, Rd, Ra, Rm, Rn)
}

function clause decode32 ((0b111110101010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 573) = {
    SEE = 573;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UASX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b11101011000 @ _ : bits(21) as op_code) if SEE < 574) = {
    SEE = 574;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    ADD_r_T3_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 575) = {
    SEE = 575;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VTST_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0001 @ _ : bits(8) as op_code) if SEE < 576) = {
    SEE = 576;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0110111 @ _ : bits(15) @ 0b01 @ _ : bits(4) as op_code) if SEE < 577) = {
    SEE = 577;
    cond : bits(4) = op_code[31 .. 28];
    sat_imm : bits(5) = op_code[20 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    sh : bits(1) = [op_code[6]];
    Rn : bits(4) = op_code[3 .. 0];
    USAT_A1_A_decode(cond, sat_imm, Rd, imm5, sh, Rn)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001101 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 578) = {
    SEE = 578;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESD_A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100010 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 579) = {
    SEE = 579;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QADD8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 580) = {
    SEE = 580;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFNMA_A1_A_decode(cond, D, Vn, Vd, size, N, op, M, Vm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 581) = {
    SEE = 581;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111110000011 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 582) = {
    SEE = 582;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    LDRH_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0100 @ _ : bits(8) as op_code) if SEE < 583) = {
    SEE = 583;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 584) = {
    SEE = 584;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rt2 : bits(4) = op_code[11 .. 8];
    LDAEXD_T1_A_decode(Rn, Rt, Rt2)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b11100 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 585) = {
    SEE = 585;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T5A5pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 586) = {
    SEE = 586;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGE_i_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111110001100 @ _ : bits(20) as op_code) if SEE < 587) = {
    SEE = 587;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    STR_i_T3_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b0001100 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 588) = {
    SEE = 588;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    ORR_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((0b111110101110 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 589) = {
    SEE = 589;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QSAX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111110101100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 590) = {
    SEE = 590;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    USUB8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00110011 @ _ : bits(20) as op_code) if SEE < 591) = {
    SEE = 591;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    TEQ_i_A1_A_decode(cond, Rn, imm12)
}

function clause decode32 ((_ : bits(16) @ 0b10011 @ _ : bits(11) as op_code) if SEE < 592) = {
    SEE = 592;
    Rt : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    LDR_i_T2_A_decode(Rt, imm8)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b110000 @ _ : bits(4) @ 0b101011 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 593) = {
    SEE = 593;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VINS_T1_A_decode(D, Vd, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b1111 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 594) = {
    SEE = 594;
    Q : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLSH_A2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b000 @ _ : bits(5) as op_code) if SEE < 595) = {
    SEE = 595;
    Rn : bits(4) = op_code[19 .. 16];
    H : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    TBB_T1_A_decode(Rn, H, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1011111100010000 as op_code) if SEE < 596) = {
    SEE = 596;
    YIELD_T1_A_decode()
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0000 @ _ : bits(8) as op_code) if SEE < 597) = {
    SEE = 597;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b001100100000 @ _ : bits(8) @ 0b00000000 as op_code) if SEE < 598) = {
    SEE = 598;
    cond : bits(4) = op_code[31 .. 28];
    NOP_A1_A_decode(cond)
}

function clause decode32 ((0b111110000010 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 599) = {
    SEE = 599;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    STRHT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b0000100 @ _ : bits(1) @ 0b1101 @ _ : bits(11) @ 0b0 @ _ : bits(4) as op_code) if SEE < 600) = {
    SEE = 600;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    ADD_SP_r_A1_A_decode(cond, S, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 601) = {
    SEE = 601;
    Q : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_s_T1_A_decode(Q, D, size, Vn, Vd, F, N, M, Vm)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b10 @ _ : bits(3) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 602) = {
    SEE = 602;
    D : bits(1) = [op_code[22]];
    imm4H : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    VMOV_i_T2_A_decode(D, imm4H, Vd, size, imm4L)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 603) = {
    SEE = 603;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQADD_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b1101 @ _ : bits(2) @ 0b00 @ _ : bits(8) @ 0b10 @ _ : bits(10) as op_code) if SEE < 604) = {
    SEE = 604;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    VSTR_A1_A_decode(cond, U, D, Rn, Vd, size, imm8)
}

function clause decode32 ((0b111110111110 @ _ : bits(12) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 605) = {
    SEE = 605;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UMLAL_T1_A_decode(Rn, RdLo, RdHi, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01110000 @ _ : bits(12) @ 0b00 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 606) = {
    SEE = 606;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMLAD_A1_A_decode(cond, Rd, Ra, Rm, M, Rn)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 607) = {
    SEE = 607;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b11110100 @ _ : bits(1) @ 0b101 @ _ : bits(4) @ 0b1111 @ _ : bits(12) as op_code) if SEE < 608) = {
    SEE = 608;
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    PLI_i_A1_A_decode(U, Rn, imm12)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b11000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 609) = {
    SEE = 609;
    D : bits(1) = [op_code[22]];
    imm4 : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VDUP_s_T1A1_A_decode(D, imm4, Vd, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001100 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 610) = {
    SEE = 610;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHLL_T2A2_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 611) = {
    SEE = 611;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHL_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111100 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 612) = {
    SEE = 612;
    D : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFMAL_i_A1_A_decode(D, S, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b010 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b11111 @ _ : bits(16) as op_code) if SEE < 613) = {
    SEE = 613;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRB_l_A1_A_decode(cond, P, U, W, Rt, imm12)
}

function clause decode32 ((0b111100111101 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(12) as op_code) if SEE < 614) = {
    SEE = 614;
    imm8 : bits(8) = op_code[7 .. 0];
    SUBS_PC_T1pre_AS_decode(imm8)
}

function clause decode32 ((_ : bits(4) @ 0b01100110 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 615) = {
    SEE = 615;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UQSUB8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1011 @ _ : bits(8) as op_code) if SEE < 616) = {
    SEE = 616;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0101 @ _ : bits(8) as op_code) if SEE < 617) = {
    SEE = 617;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 618) = {
    SEE = 618;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VBIC_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110000010 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 619) = {
    SEE = 619;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    STRH_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((0b11111010010011111111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 620) = {
    SEE = 620;
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SXTB_T2_A_decode(Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1101 @ _ : bits(12) as op_code) if SEE < 621) = {
    SEE = 621;
    cond : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    B_T1_A_decode(cond, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b111 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 622) = {
    SEE = 622;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRSBT_A1pre_A_decode(cond, U, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((_ : bits(4) @ 0b01100001 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 623) = {
    SEE = 623;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SADD8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111110110000 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 624) = {
    SEE = 624;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    MLS_T1_A_decode(Rn, Ra, Rd, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 625) = {
    SEE = 625;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 626) = {
    SEE = 626;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADD_f_T1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110111100 @ _ : bits(12) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 627) = {
    SEE = 627;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SMLAL_T1_A_decode(Rn, RdLo, RdHi, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010000 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 628) = {
    SEE = 628;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QADD_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00011110 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 629) = {
    SEE = 629;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STLEXH_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 630) = {
    SEE = 630;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMVN_i_T2A2_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b11111100 @ _ : bits(2) @ 0b10 @ _ : bits(8) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 631) = {
    SEE = 631;
    S : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFMAL_T1_A_decode(S, D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1100 @ _ : bits(8) as op_code) if SEE < 632) = {
    SEE = 632;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 633) = {
    SEE = 633;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256SU1_A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b100000 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 634) = {
    SEE = 634;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    LDMDA_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b01110101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b00 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 635) = {
    SEE = 635;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Rm : bits(4) = op_code[11 .. 8];
    R : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMMUL_A1_A_decode(cond, Rd, Rm, R, Rn)
}

function clause decode32 ((_ : bits(16) @ 0b01111 @ _ : bits(11) as op_code) if SEE < 636) = {
    SEE = 636;
    imm5 : bits(5) = op_code[10 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDRB_i_T1_A_decode(imm5, Rn, Rt)
}

function clause decode32 ((0b11111000 @ _ : bits(1) @ 0b0111111 @ _ : bits(16) as op_code) if SEE < 637) = {
    SEE = 637;
    U : bits(1) = [op_code[23]];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRH_l_T1_A_decode(U, Rt, imm12)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1011 @ _ : bits(8) as op_code) if SEE < 638) = {
    SEE = 638;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b011 @ _ : bits(4) @ 0b1 @ _ : bits(4) as op_code) if SEE < 639) = {
    SEE = 639;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSHL_i_T1A1_A_decode(U, D, imm6, Vd, op, L, Q, M, Vm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b1111 @ _ : bits(6) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 640) = {
    SEE = 640;
    D : bits(1) = [op_code[22]];
    RM : bits(2) = op_code[17 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVTA_vfp_A1_A_decode(D, RM, Vd, size, op, M, Vm)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 641) = {
    SEE = 641;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULL_T1A1pre_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 642) = {
    SEE = 642;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADD_f_A1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b10 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 643) = {
    SEE = 643;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VORR_i_T2A2_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 644) = {
    SEE = 644;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRD_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 645) = {
    SEE = 645;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SADD8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 646) = {
    SEE = 646;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 647) = {
    SEE = 647;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256H_A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b011010101111 @ _ : bits(8) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 648) = {
    SEE = 648;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    SXTB_A1_A_decode(cond, Rd, rotate, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b01000 @ _ : bits(1) @ 0b11010 @ _ : bits(15) as op_code) if SEE < 649) = {
    SEE = 649;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADD_SP_i_T3_A_decode(i, S, imm3, Rd, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b0100 @ _ : bits(1) @ 0b011 @ _ : bits(20) as op_code) if SEE < 650) = {
    SEE = 650;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRT_A1pre_A_decode(cond, U, Rn, Rt, imm12)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b1111 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 651) = {
    SEE = 651;
    Q : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLSH_T2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 652) = {
    SEE = 652;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSUB_i_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100101 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 653) = {
    SEE = 653;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    USAX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b00 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 654) = {
    SEE = 654;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMVN_i_T1A1_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b0000110 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 655) = {
    SEE = 655;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    SBC_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b01101 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 656) = {
    SEE = 656;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    SUB_i_T3_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 657) = {
    SEE = 657;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSWP_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 658) = {
    SEE = 658;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110111001 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 659) = {
    SEE = 659;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SDIV_T1_A_decode(Rn, Ra, Rd, Rm)
}

function clause decode32 ((0b1111100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(8) @ 0b0101 @ _ : bits(8) as op_code) if SEE < 660) = {
    SEE = 660;
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    mode : bits(5) = op_code[4 .. 0];
    SRS_A1_AS_decode(P, U, W, mode)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0001 @ _ : bits(8) as op_code) if SEE < 661) = {
    SEE = 661;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 662) = {
    SEE = 662;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAEXH_T1_A_decode(Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b01100010 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 663) = {
    SEE = 663;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QSUB16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0010 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 664) = {
    SEE = 664;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSHR_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b111101010111 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 665) = {
    SEE = 665;
    CLREX_A1_A_decode()
}

function clause decode32 ((_ : bits(4) @ 0b00010001 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 666) = {
    SEE = 666;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    TST_r_A1_A_decode(cond, Rn, imm5, typ, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(11) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 667) = {
    SEE = 667;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSUBHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 668) = {
    SEE = 668;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1P_A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01100101 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 669) = {
    SEE = 669;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UADD16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b11111010000111111111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 670) = {
    SEE = 670;
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    UXTH_T2_A_decode(Rd, rotate, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 671) = {
    SEE = 671;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0000 @ _ : bits(8) as op_code) if SEE < 672) = {
    SEE = 672;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01010 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 673) = {
    SEE = 673;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCNT_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(11) @ 0b10 @ _ : bits(1) @ 0b1 @ _ : bits(12) as op_code) if SEE < 674) = {
    SEE = 674;
    S : bits(1) = [op_code[26]];
    imm10 : bits(10) = op_code[25 .. 16];
    J1 : bits(1) = [op_code[13]];
    J2 : bits(1) = [op_code[11]];
    imm11 : bits(11) = op_code[10 .. 0];
    B_T4_A_decode(S, imm10, J1, J2, imm11)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 675) = {
    SEE = 675;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRSHL_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 676) = {
    SEE = 676;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UADD8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 677) = {
    SEE = 677;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110010011 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 678) = {
    SEE = 678;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRSH_i_T2_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((_ : bits(16) @ 0b0001110 @ _ : bits(9) as op_code) if SEE < 679) = {
    SEE = 679;
    imm3 : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    ADD_i_T1_A_decode(imm3, Rn, Rd)
}

function clause decode32 ((_ : bits(4) @ 0b0011110 @ _ : bits(21) as op_code) if SEE < 680) = {
    SEE = 680;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    BIC_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b0010011 @ _ : bits(21) as op_code) if SEE < 681) = {
    SEE = 681;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    RSB_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b00011001 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 682) = {
    SEE = 682;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAEX_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1000 @ _ : bits(4) as op_code) if SEE < 683) = {
    SEE = 683;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QADD_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 684) = {
    SEE = 684;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGT_i_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b111 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 685) = {
    SEE = 685;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VNEG_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 686) = {
    SEE = 686;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    STRD_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b11111000 @ _ : bits(1) @ 0b0011111 @ _ : bits(16) as op_code) if SEE < 687) = {
    SEE = 687;
    U : bits(1) = [op_code[23]];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRB_l_T1_A_decode(U, Rt, imm12)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b001001 @ _ : bits(4) @ 0b0 @ _ : bits(3) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 688) = {
    SEE = 688;
    i : bits(1) = [op_code[26]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    TEQ_i_T1_A_decode(i, Rn, imm3, imm8)
}

function clause decode32 ((0b11110111 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b1111 @ _ : bits(7) @ 0b0 @ _ : bits(4) as op_code) if SEE < 689) = {
    SEE = 689;
    U : bits(1) = [op_code[23]];
    R : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    PLD_r_A1_A_decode(U, R, Rn, imm5, typ, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b10000011110 @ _ : bits(15) as op_code) if SEE < 690) = {
    SEE = 690;
    i : bits(1) = [op_code[26]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADR_T3_A_decode(i, imm3, Rd, imm8)
}

function clause decode32 ((0b111110100100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 691) = {
    SEE = 691;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SXTAB_T1_A_decode(Rn, Rd, rotate, Rm)
}

function clause decode32 ((0b111110110101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b000 @ _ : bits(5) as op_code) if SEE < 692) = {
    SEE = 692;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    R : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMMUL_T1_A_decode(Rn, Rd, R, Rm)
}

function clause decode32 ((0b111101010111 @ _ : bits(12) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 693) = {
    SEE = 693;
    option_name : bits(4) = op_code[3 .. 0];
    ISB_A1_A_decode(option_name)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0101 @ _ : bits(8) as op_code) if SEE < 694) = {
    SEE = 694;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 695) = {
    SEE = 695;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VBIC_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b11101010010 @ _ : bits(1) @ 0b1111 @ _ : bits(16) as op_code) if SEE < 696) = {
    SEE = 696;
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    MOV_r_T3_A_decode(S, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0001110 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 697) = {
    SEE = 697;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    BIC_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b100 @ _ : bits(9) as op_code) if SEE < 698) = {
    SEE = 698;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 699) = {
    SEE = 699;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[3 .. 0];
    STLEXH_T1_A_decode(Rn, Rt, Rd)
}

function clause decode32 ((_ : bits(4) @ 0b01101011 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 700) = {
    SEE = 700;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    REV16_A1_A_decode(cond, Rd, Rm)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 701) = {
    SEE = 701;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFNMA_T1_A_decode(D, Vn, Vd, size, N, op, M, Vm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 702) = {
    SEE = 702;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 703) = {
    SEE = 703;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T4A4_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111111100 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 704) = {
    SEE = 704;
    D : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VFMAL_i_T1_A_decode(D, S, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1010 @ _ : bits(8) as op_code) if SEE < 705) = {
    SEE = 705;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110101100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 706) = {
    SEE = 706;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UQSUB8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b011011001111 @ _ : bits(8) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 707) = {
    SEE = 707;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    UXTB16_A1_A_decode(cond, Rd, rotate, Rm)
}

function clause decode32 ((0b111110101101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 708) = {
    SEE = 708;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SSUB16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b0 @ _ : bits(11) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 709) = {
    SEE = 709;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[9]];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VHADD_T1A1_A_decode(U, D, size, Vn, Vd, op, N, Q, M, Vm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 710) = {
    SEE = 710;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T4A4_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 711) = {
    SEE = 711;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRSHL_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b1111100000 @ _ : bits(1) @ 0b1 @ _ : bits(4) @ 0b1111000000 @ _ : bits(6) as op_code) if SEE < 712) = {
    SEE = 712;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    PLD_r_T1_A_decode(W, Rn, imm2, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0100001001 @ _ : bits(6) as op_code) if SEE < 713) = {
    SEE = 713;
    Rn : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    RSB_i_T1_A_decode(Rn, Rd)
}

function clause decode32 ((_ : bits(4) @ 0b0110 @ _ : bits(1) @ 0b110 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 714) = {
    SEE = 714;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    STRBT_A2pre_A_decode(cond, U, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((0b111101111110 @ _ : bits(4) @ 0b1000 @ _ : bits(12) as op_code) if SEE < 715) = {
    SEE = 715;
    imm4 : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    HVC_T1_A_decode(imm4, imm12)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b1110 @ _ : bits(4) as op_code) if SEE < 716) = {
    SEE = 716;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAEX_T1_A_decode(Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b01100010 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 717) = {
    SEE = 717;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QSUB8_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b11101010000 @ _ : bits(21) as op_code) if SEE < 718) = {
    SEE = 718;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    AND_r_T2_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b001011 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 719) = {
    SEE = 719;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1H_A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 720) = {
    SEE = 720;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256H_T1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01101111 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 721) = {
    SEE = 721;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    UXTAH_A1_A_decode(cond, Rn, Rd, rotate, Rm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b100 @ _ : bits(9) as op_code) if SEE < 722) = {
    SEE = 722;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b01011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 723) = {
    SEE = 723;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTZ_asimd_A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b01 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 724) = {
    SEE = 724;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1P_T1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b1110100010 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 725) = {
    SEE = 725;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    P : bits(1) = [op_code[15]];
    M : bits(1) = [op_code[14]];
    register_list : bits(14) = op_code[13 .. 0];
    STM_T2_A_decode(W, Rn, P, M, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b01100111 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 726) = {
    SEE = 726;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UHASX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b011 @ _ : bits(4) @ 0b1 @ _ : bits(4) as op_code) if SEE < 727) = {
    SEE = 727;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQSHL_i_T1A1_A_decode(U, D, imm6, Vd, op, L, Q, M, Vm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 728) = {
    SEE = 728;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110000010 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 729) = {
    SEE = 729;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    STRH_i_T3_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((0b111010111011 @ _ : bits(8) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 730) = {
    SEE = 730;
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    CMP_r_T3_A_decode(Rn, imm3, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1011101010 @ _ : bits(6) as op_code) if SEE < 731) = {
    SEE = 731;
    imm6 : bits(6) = op_code[5 .. 0];
    HLT_T1_A_decode(imm6)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b1 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 732) = {
    SEE = 732;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    LDRSB_r_A1_A_decode(cond, P, U, W, Rn, Rt, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100011 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 733) = {
    SEE = 733;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SHSUB16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b100000 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 734) = {
    SEE = 734;
    i : bits(1) = [op_code[26]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADD_i_T4_A_decode(i, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b010 @ _ : bits(9) as op_code) if SEE < 735) = {
    SEE = 735;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0100001000 @ _ : bits(6) as op_code) if SEE < 736) = {
    SEE = 736;
    Rm : bits(3) = op_code[5 .. 3];
    Rn : bits(3) = op_code[2 .. 0];
    TST_r_T1_A_decode(Rm, Rn)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b1101 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 737) = {
    SEE = 737;
    Q : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMULH_T2A2_A_decode(Q, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b11100 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 738) = {
    SEE = 738;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VNMLA_A2_A_decode(cond, D, Vn, Vd, size, N, M, Vm)
}

function clause decode32 ((0b111110101110 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 739) = {
    SEE = 739;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    USAX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111100111011 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(4) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 740) = {
    SEE = 740;
    option_name : bits(4) = op_code[3 .. 0];
    DMB_T1_A_decode(option_name)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 741) = {
    SEE = 741;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRECPS_A1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 742) = {
    SEE = 742;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLSH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b1110100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 743) = {
    SEE = 743;
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rt2 : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    STRD_i_T1_A_decode(P, U, W, Rn, Rt, Rt2, imm8)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b0010 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 744) = {
    SEE = 744;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[7 .. 6];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQMOVN_T1A1_A_decode(D, size, Vd, op, M, Vm)
}

function clause decode32 ((0b111110000101 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 745) = {
    SEE = 745;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 746) = {
    SEE = 746;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    op : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAXNM_T2A2pre_A_decode(D, Vn, Vd, size, N, op, M, Vm)
}

function clause decode32 ((0b11101010100 @ _ : bits(21) as op_code) if SEE < 747) = {
    SEE = 747;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    EOR_r_T2_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111010110001 @ _ : bits(8) @ 0b1111 @ _ : bits(8) as op_code) if SEE < 748) = {
    SEE = 748;
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    CMN_r_T2_A_decode(Rn, imm3, imm2, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0100 @ _ : bits(1) @ 0b111 @ _ : bits(20) as op_code) if SEE < 749) = {
    SEE = 749;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRBT_A1pre_A_decode(cond, U, Rn, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b011 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 750) = {
    SEE = 750;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    STR_r_A1_A_decode(cond, P, U, W, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((0b111110000011 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 751) = {
    SEE = 751;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRH_i_T3_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 752) = {
    SEE = 752;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_m_T2A2_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b1111101 @ _ : bits(25) as op_code) if SEE < 753) = {
    SEE = 753;
    H : bits(1) = [op_code[24]];
    imm24 : bits(24) = op_code[23 .. 0];
    BL_i_A2_A_decode(H, imm24)
}

function clause decode32 ((_ : bits(4) @ 0b0010111 @ _ : bits(21) as op_code) if SEE < 754) = {
    SEE = 754;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    RSC_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b01100111 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 755) = {
    SEE = 755;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UHADD16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 756) = {
    SEE = 756;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UQADD8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b1011101001 @ _ : bits(6) as op_code) if SEE < 757) = {
    SEE = 757;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    REV16_T1_A_decode(Rm, Rd)
}

function clause decode32 ((_ : bits(4) @ 0b00011010 @ _ : bits(10) @ 0b101001 @ _ : bits(4) as op_code) if SEE < 758) = {
    SEE = 758;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STLEXD_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b011011111111 @ _ : bits(8) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 759) = {
    SEE = 759;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    UXTH_A1_A_decode(cond, Rd, rotate, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b10 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 760) = {
    SEE = 760;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VBIC_i_T2A2_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 761) = {
    SEE = 761;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UADD16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000100 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 762) = {
    SEE = 762;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    ADD_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((0b1110100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 763) = {
    SEE = 763;
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rt2 : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRD_i_T1_A_decode(P, U, W, Rn, Rt, Rt2, imm8)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b010 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 764) = {
    SEE = 764;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCEQ_i_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b10101011010 @ _ : bits(15) as op_code) if SEE < 765) = {
    SEE = 765;
    i : bits(1) = [op_code[26]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    SUB_SP_i_T3_A_decode(i, imm3, Rd, imm8)
}

function clause decode32 ((0b111110111100 @ _ : bits(12) @ 0b110 @ _ : bits(5) as op_code) if SEE < 766) = {
    SEE = 766;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMLALD_T1_A_decode(Rn, RdLo, RdHi, M, Rm)
}

function clause decode32 ((0b11111010000 @ _ : bits(5) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 767) = {
    SEE = 767;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    LSL_r_T2_A_decode(S, Rn, Rd, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b0010 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 768) = {
    SEE = 768;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADDL_T1A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 769) = {
    SEE = 769;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULL_T1A1pre_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0111110 @ _ : bits(14) @ 0b0011111 as op_code) if SEE < 770) = {
    SEE = 770;
    cond : bits(4) = op_code[31 .. 28];
    msb : bits(5) = op_code[20 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    lsb : bits(5) = op_code[11 .. 7];
    BFC_A1_A_decode(cond, msb, Rd, lsb)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 771) = {
    SEE = 771;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QDSUB_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b111001 @ _ : bits(4) @ 0b101111 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 772) = {
    SEE = 772;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VJCVT_A1_A_decode(cond, D, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b011 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 773) = {
    SEE = 773;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    LDRSHT_A2pre_A_decode(cond, U, Rn, Rt, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000010 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 774) = {
    SEE = 774;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    SUB_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111110101100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 775) = {
    SEE = 775;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SSUB8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b10 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 776) = {
    SEE = 776;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VBIC_i_T2A2_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 777) = {
    SEE = 777;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UHADD16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b00000000101 as op_code) if SEE < 778) = {
    SEE = 778;
    SEVL_T2_A_decode()
}

function clause decode32 ((_ : bits(16) @ 0b1011001010 @ _ : bits(6) as op_code) if SEE < 779) = {
    SEE = 779;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    UXTH_T1_A_decode(Rm, Rd)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 780) = {
    SEE = 780;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSRA_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b0010 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 781) = {
    SEE = 781;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADDL_T1A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b110100 @ _ : bits(4) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 782) = {
    SEE = 782;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    E : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCMP_A1_A_decode(cond, D, Vd, size, E, M, Vm)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 783) = {
    SEE = 783;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    STLH_T1_A_decode(Rn, Rt)
}

function clause decode32 ((_ : bits(16) @ 0b00010 @ _ : bits(11) as op_code) if SEE < 784) = {
    SEE = 784;
    imm5 : bits(5) = op_code[10 .. 6];
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    ASR_i_T1_A_decode(imm5, Rm, Rd)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 785) = {
    SEE = 785;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRECPS_T1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(11) @ 0b0100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 786) = {
    SEE = 786;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSRI_T1A1_A_decode(D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b100000 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 787) = {
    SEE = 787;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHRN_T1A1_A_decode(D, imm6, Vd, M, Vm)
}

function clause decode32 ((0b111110101100 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 788) = {
    SEE = 788;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QSUB8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b001011 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 789) = {
    SEE = 789;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1H_T1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 790) = {
    SEE = 790;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[9]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_i_T2A2_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111011100 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 791) = {
    SEE = 791;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VNMLA_T2_A_decode(D, Vn, Vd, size, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0011100 @ _ : bits(21) as op_code) if SEE < 792) = {
    SEE = 792;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    ORR_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((0b11101010011 @ _ : bits(1) @ 0b1111 @ _ : bits(16) as op_code) if SEE < 793) = {
    SEE = 793;
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    MVN_r_T2_A_decode(S, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 794) = {
    SEE = 794;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHR_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b111010001100 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 795) = {
    SEE = 795;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rt2 : bits(4) = op_code[11 .. 8];
    Rd : bits(4) = op_code[3 .. 0];
    STLEXD_T1_A_decode(Rn, Rt, Rt2, Rd)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b100 @ _ : bits(1) @ 0b01 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 796) = {
    SEE = 796;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRSHRN_T1A1_A_decode(U, D, imm6, Vd, op, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 797) = {
    SEE = 797;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADD_i_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(11) @ 0b1111 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 798) = {
    SEE = 798;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAX_f_A1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b00101 @ _ : bits(11) as op_code) if SEE < 799) = {
    SEE = 799;
    Rn : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    CMP_i_T1_A_decode(Rn, imm8)
}

function clause decode32 ((0b111110101010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 800) = {
    SEE = 800;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UHASX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0101011 @ _ : bits(9) as op_code) if SEE < 801) = {
    SEE = 801;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDRSB_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((0b111110101101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 802) = {
    SEE = 802;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SHSUB16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111110110001 @ _ : bits(12) @ 0b00 @ _ : bits(6) as op_code) if SEE < 803) = {
    SEE = 803;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    N : bits(1) = [op_code[5]];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMLABB_T1_A_decode(Rn, Ra, Rd, N, M, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(11) @ 0b11 @ _ : bits(1) @ 0b0 @ _ : bits(12) as op_code) if SEE < 804) = {
    SEE = 804;
    S : bits(1) = [op_code[26]];
    imm10H : bits(10) = op_code[25 .. 16];
    J1 : bits(1) = [op_code[13]];
    J2 : bits(1) = [op_code[11]];
    imm10L : bits(10) = op_code[10 .. 1];
    H : bits(1) = [op_code[0]];
    BL_i_T2_A_decode(S, imm10H, J1, J2, imm10L, H)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b010 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 805) = {
    SEE = 805;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCEQ_i_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 806) = {
    SEE = 806;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b1110100100 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 807) = {
    SEE = 807;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    P : bits(1) = [op_code[15]];
    M : bits(1) = [op_code[14]];
    register_list : bits(14) = op_code[13 .. 0];
    STMDB_T1_A_decode(W, Rn, P, M, register_list)
}

function clause decode32 ((_ : bits(4) @ 0b00011101 @ _ : bits(10) @ 0b001001 @ _ : bits(4) as op_code) if SEE < 808) = {
    SEE = 808;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAB_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((_ : bits(16) @ 0b101100000 @ _ : bits(7) as op_code) if SEE < 809) = {
    SEE = 809;
    imm7 : bits(7) = op_code[6 .. 0];
    ADD_SP_i_T2_A_decode(imm7)
}

function clause decode32 ((_ : bits(4) @ 0b00010010 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 810) = {
    SEE = 810;
    cond : bits(4) = op_code[31 .. 28];
    Rm : bits(4) = op_code[3 .. 0];
    BX_A1_A_decode(cond, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(11) @ 0b0100 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 811) = {
    SEE = 811;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRADDHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00010110 @ _ : bits(12) @ 0b1 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 812) = {
    SEE = 812;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[6]];
    N : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMULBB_A1_A_decode(cond, Rd, Rm, M, N, Rn)
}

function clause decode32 ((0b111011110 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 813) = {
    SEE = 813;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VORR_r_T1A1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b01 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 814) = {
    SEE = 814;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(3) = op_code[9 .. 7];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTA_asimd_T1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b1101 @ _ : bits(2) @ 0b01 @ _ : bits(8) @ 0b10 @ _ : bits(10) as op_code) if SEE < 815) = {
    SEE = 815;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    VLDR_A1_A_decode(cond, U, D, Rn, Vd, size, imm8)
}

function clause decode32 ((_ : bits(16) @ 0b0101000 @ _ : bits(9) as op_code) if SEE < 816) = {
    SEE = 816;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    STR_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 817) = {
    SEE = 817;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAXNM_A1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100110 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 818) = {
    SEE = 818;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMULH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 819) = {
    SEE = 819;
    D : bits(1) = [op_code[22]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256SU1_T1_A_decode(D, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111010001101 @ _ : bits(12) @ 0b1000 @ _ : bits(4) as op_code) if SEE < 820) = {
    SEE = 820;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDAB_T1_A_decode(Rn, Rt)
}

function clause decode32 ((_ : bits(16) @ 0b010001110 @ _ : bits(7) as op_code) if SEE < 821) = {
    SEE = 821;
    Rm : bits(4) = op_code[6 .. 3];
    BX_T1_A_decode(Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b11 @ _ : bits(4) @ 0b010 @ _ : bits(1) @ 0b1 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 822) = {
    SEE = 822;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[8]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSQRTE_A1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000010 @ _ : bits(1) @ 0b1101 @ _ : bits(11) @ 0b0 @ _ : bits(4) as op_code) if SEE < 823) = {
    SEE = 823;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    SUB_SP_r_A1_A_decode(cond, S, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b000 @ _ : bits(4) @ 0b0 @ _ : bits(4) as op_code) if SEE < 824) = {
    SEE = 824;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[8 .. 7];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VREV16_T1A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b110111 @ _ : bits(4) @ 0b10 @ _ : bits(2) @ 0b01 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 825) = {
    SEE = 825;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTX_vfp_A1_A_decode(cond, D, Vd, size, M, Vm)
}

function clause decode32 ((0b1110100000 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 826) = {
    SEE = 826;
    W : bits(1) = [op_code[21]];
    mode : bits(5) = op_code[4 .. 0];
    SRS_T1_AS_decode(W, mode)
}

function clause decode32 ((_ : bits(16) @ 0b1011111100000000 as op_code) if SEE < 827) = {
    SEE = 827;
    NOP_T1_A_decode()
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0001 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 828) = {
    SEE = 828;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSRA_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b11101101 @ _ : bits(2) @ 0b01 @ _ : bits(8) @ 0b10 @ _ : bits(10) as op_code) if SEE < 829) = {
    SEE = 829;
    U : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    VLDR_T1_A_decode(U, D, Rn, Vd, size, imm8)
}

function clause decode32 ((0b111110101000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 830) = {
    SEE = 830;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QADD8_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1100 @ _ : bits(8) as op_code) if SEE < 831) = {
    SEE = 831;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00011001 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 832) = {
    SEE = 832;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDREX_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1111 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 833) = {
    SEE = 833;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMAXNM_T1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01110101 @ _ : bits(12) @ 0b00 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 834) = {
    SEE = 834;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    R : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMMLA_A1_A_decode(cond, Rd, Ra, Rm, R, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b01100011 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 835) = {
    SEE = 835;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SHSAX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b110100 @ _ : bits(4) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 836) = {
    SEE = 836;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    E : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCMP_T1_A_decode(D, Vd, size, E, M, Vm)
}

function clause decode32 ((0b11111000 @ _ : bits(1) @ 0b1011111 @ _ : bits(16) as op_code) if SEE < 837) = {
    SEE = 837;
    U : bits(1) = [op_code[23]];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDR_l_T2_A_decode(U, Rt, imm12)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b0100 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 838) = {
    SEE = 838;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHL_r_T1A1_A_decode(U, D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100100 @ _ : bits(11) @ 0b1101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 839) = {
    SEE = 839;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_f_A1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0000 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 840) = {
    SEE = 840;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHR_T1A1_A_decode(U, D, imm6, Vd, L, Q, M, Vm)
}

function clause decode32 ((0b1111100000 @ _ : bits(1) @ 0b1 @ _ : bits(4) @ 0b11111100 @ _ : bits(8) as op_code) if SEE < 841) = {
    SEE = 841;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    imm8 : bits(8) = op_code[7 .. 0];
    PLD_i_T2_A_decode(W, Rn, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b01100001 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 842) = {
    SEE = 842;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SADD16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b1 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 843) = {
    SEE = 843;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    LDRH_r_A1_A_decode(cond, P, U, W, Rn, Rt, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(11) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 844) = {
    SEE = 844;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADD_i_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111100010000 @ _ : bits(3) @ 0b0 @ _ : bits(10) @ 0b0 @ _ : bits(5) as op_code) if SEE < 845) = {
    SEE = 845;
    imod : bits(2) = op_code[19 .. 18];
    M : bits(1) = [op_code[17]];
    A : bits(1) = [op_code[8]];
    I : bits(1) = [op_code[7]];
    F : bits(1) = [op_code[6]];
    mode : bits(5) = op_code[4 .. 0];
    CPS_A1_AS_decode(imod, M, A, I, F, mode)
}

function clause decode32 ((0b111110011001 @ _ : bits(4) @ 0b1111 @ _ : bits(12) as op_code) if SEE < 846) = {
    SEE = 846;
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    PLI_i_T1_A_decode(Rn, imm12)
}

function clause decode32 ((0b11101011010 @ _ : bits(21) as op_code) if SEE < 847) = {
    SEE = 847;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    ADC_r_T2_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001110 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 848) = {
    SEE = 848;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1SU1_A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b01000100 @ _ : bits(1) @ 0b1101 @ _ : bits(3) as op_code) if SEE < 849) = {
    SEE = 849;
    DM : bits(1) = [op_code[7]];
    Rdm : bits(3) = op_code[2 .. 0];
    ADD_SP_r_T1_A_decode(DM, Rdm)
}

function clause decode32 ((0b111011110 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 850) = {
    SEE = 850;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMULH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01101100 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 851) = {
    SEE = 851;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    UXTAB16_A1_A_decode(cond, Rn, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100111 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 852) = {
    SEE = 852;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UHSAX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b100000 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 853) = {
    SEE = 853;
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHRN_T1A1_A_decode(D, imm6, Vd, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b00 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 854) = {
    SEE = 854;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T1A1pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((0b111110000001 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 855) = {
    SEE = 855;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    LDRB_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0100 @ _ : bits(1) @ 0b010 @ _ : bits(20) as op_code) if SEE < 856) = {
    SEE = 856;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    STRT_A1pre_A_decode(cond, U, Rn, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b010 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 857) = {
    SEE = 857;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDR_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm12)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b0100 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 858) = {
    SEE = 858;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADDHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b00010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 859) = {
    SEE = 859;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ORR_i_T1_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b1110 @ _ : bits(1) @ 0b0 @ _ : bits(4) @ 0b0 @ _ : bits(15) as op_code) if SEE < 860) = {
    SEE = 860;
    sh : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    sat_imm : bits(5) = op_code[4 .. 0];
    USAT_T1_A_decode(sh, Rn, imm3, Rd, imm2, sat_imm)
}

function clause decode32 ((_ : bits(4) @ 0b00010 @ _ : bits(1) @ 0b00 @ _ : bits(10) @ 0b1 @ _ : bits(1) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 861) = {
    SEE = 861;
    cond : bits(4) = op_code[31 .. 28];
    R : bits(1) = [op_code[22]];
    M1 : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[8]];
    MRS_br_A1_AS_decode(cond, R, M1, Rd, M)
}

function clause decode32 ((0b111110000000 @ _ : bits(8) @ 0b000000 @ _ : bits(6) as op_code) if SEE < 862) = {
    SEE = 862;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm2 : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    STRB_r_T2_A_decode(Rn, Rt, imm2, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010110 @ _ : bits(12) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 863) = {
    SEE = 863;
    cond : bits(4) = op_code[31 .. 28];
    ERET_A1_A_decode(cond)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b11100 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 864) = {
    SEE = 864;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T5A5pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b110110 @ _ : bits(4) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 865) = {
    SEE = 865;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTZ_vfp_A1_A_decode(cond, D, Vd, size, op, M, Vm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 866) = {
    SEE = 866;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(11) @ 0b0100 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 867) = {
    SEE = 867;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRADDHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0010110 @ _ : bits(21) as op_code) if SEE < 868) = {
    SEE = 868;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    SBC_i_A1_A_decode(cond, S, Rn, Rd, imm12)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 869) = {
    SEE = 869;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[9]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_i_T2A2_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b101000 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 870) = {
    SEE = 870;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHLL_T1A1_A_decode(U, D, imm6, Vd, M, Vm)
}

function clause decode32 ((0b111110110001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b00 @ _ : bits(6) as op_code) if SEE < 871) = {
    SEE = 871;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    N : bits(1) = [op_code[5]];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMULBB_T1_A_decode(Rn, Rd, N, M, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b001 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 872) = {
    SEE = 872;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGE_i_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b11101101 @ _ : bits(2) @ 0b00 @ _ : bits(8) @ 0b10 @ _ : bits(10) as op_code) if SEE < 873) = {
    SEE = 873;
    U : bits(1) = [op_code[23]];
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    VSTR_T1_A_decode(U, D, Rn, Vd, size, imm8)
}

function clause decode32 ((0b1111110 @ _ : bits(3) @ 0b1 @ _ : bits(9) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 874) = {
    SEE = 874;
    rot : bits(2) = op_code[24 .. 23];
    D : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCMLA_A1_A_decode(rot, D, S, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110110010 @ _ : bits(12) @ 0b000 @ _ : bits(5) as op_code) if SEE < 875) = {
    SEE = 875;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMLAD_T1_A_decode(Rn, Ra, Rd, M, Rm)
}

function clause decode32 ((0b111110010001 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 876) = {
    SEE = 876;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRSBT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b11 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 877) = {
    SEE = 877;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[9]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_i_A2_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001101 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 878) = {
    SEE = 878;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESD_T1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 879) = {
    SEE = 879;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    STRH_r_A1_A_decode(cond, P, U, W, Rn, Rt, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0001101 @ _ : bits(9) as op_code) if SEE < 880) = {
    SEE = 880;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    SUB_r_T1_A_decode(Rm, Rn, Rd)
}

function clause decode32 ((_ : bits(16) @ 0b01101 @ _ : bits(11) as op_code) if SEE < 881) = {
    SEE = 881;
    imm5 : bits(5) = op_code[10 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDR_i_T1_A_decode(imm5, Rn, Rt)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0001 @ _ : bits(8) as op_code) if SEE < 882) = {
    SEE = 882;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b00001 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 883) = {
    SEE = 883;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    BIC_i_T1_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b11 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 884) = {
    SEE = 884;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[9]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_i_T2_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111100111011 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(4) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 885) = {
    SEE = 885;
    CLREX_T1_A_decode()
}

function clause decode32 ((_ : bits(4) @ 0b011 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 886) = {
    SEE = 886;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    LDRB_r_A1_A_decode(cond, P, U, W, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000001 @ _ : bits(13) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 887) = {
    SEE = 887;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    EOR_rr_A1_A_decode(cond, S, Rn, Rd, Rs, typ, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b01000100 @ _ : bits(8) as op_code) if SEE < 888) = {
    SEE = 888;
    DN : bits(1) = [op_code[7]];
    Rm : bits(4) = op_code[6 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    ADD_r_T2_A_decode(DN, Rm, Rdn)
}

function clause decode32 ((_ : bits(4) @ 0b0000 @ _ : bits(1) @ 0b011 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 889) = {
    SEE = 889;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    LDRHT_A2pre_A_decode(cond, U, Rn, Rt, Rm)
}

function clause decode32 ((0b111011101 @ _ : bits(1) @ 0b110110 @ _ : bits(4) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 890) = {
    SEE = 890;
    D : bits(1) = [op_code[22]];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTZ_vfp_T1_A_decode(D, Vd, size, op, M, Vm)
}

function clause decode32 ((0b11111010000011111111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 891) = {
    SEE = 891;
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SXTH_T2_A_decode(Rd, rotate, Rm)
}

function clause decode32 ((0b111110101110 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 892) = {
    SEE = 892;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UHSAX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b11101011101 @ _ : bits(1) @ 0b1101 @ _ : bits(16) as op_code) if SEE < 893) = {
    SEE = 893;
    S : bits(1) = [op_code[20]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SUB_SP_r_T1_A_decode(S, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b101000 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 894) = {
    SEE = 894;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VSHLL_T1A1_A_decode(U, D, imm6, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b01111 @ _ : bits(8) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 895) = {
    SEE = 895;
    cond : bits(4) = op_code[31 .. 28];
    U : bits(1) = [op_code[23]];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRD_l_A1_A_decode(cond, U, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 896) = {
    SEE = 896;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCGT_i_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111111101 @ _ : bits(1) @ 0b1111 @ _ : bits(6) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 897) = {
    SEE = 897;
    D : bits(1) = [op_code[22]];
    RM : bits(2) = op_code[17 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVTA_vfp_T1_A_decode(D, RM, Vd, size, op, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b01110100 @ _ : bits(12) @ 0b01 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 898) = {
    SEE = 898;
    cond : bits(4) = op_code[31 .. 28];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMLSLD_A1_A_decode(cond, RdHi, RdLo, Rm, M, Rn)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001000 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 899) = {
    SEE = 899;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMOVN_T1A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111110110000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 900) = {
    SEE = 900;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    MUL_T2_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(11) @ 0b1101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 901) = {
    SEE = 901;
    D : bits(1) = [op_code[22]];
    op : bits(1) = [op_code[21]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMLA_f_T1_A_decode(D, op, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b01011 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 902) = {
    SEE = 902;
    i : bits(1) = [op_code[26]];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    SBC_i_T1_A_decode(i, S, Rn, imm3, Rd, imm8)
}

function clause decode32 ((_ : bits(16) @ 0b10010 @ _ : bits(11) as op_code) if SEE < 903) = {
    SEE = 903;
    Rt : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    STR_i_T2_A_decode(Rt, imm8)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1000 @ _ : bits(8) as op_code) if SEE < 904) = {
    SEE = 904;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b1111110 @ _ : bits(3) @ 0b1 @ _ : bits(9) @ 0b1000 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 905) = {
    SEE = 905;
    rot : bits(2) = op_code[24 .. 23];
    D : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCMLA_T1_A_decode(rot, D, S, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0101101 @ _ : bits(9) as op_code) if SEE < 906) = {
    SEE = 906;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    LDRH_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(12) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 907) = {
    SEE = 907;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRSH_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0000 @ _ : bits(8) as op_code) if SEE < 908) = {
    SEE = 908;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111110110101 @ _ : bits(12) @ 0b000 @ _ : bits(5) as op_code) if SEE < 909) = {
    SEE = 909;
    Rn : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    R : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMMLA_T1_A_decode(Rn, Ra, Rd, R, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 910) = {
    SEE = 910;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VZIP_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b11 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 911) = {
    SEE = 911;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T4A4pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001110 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 912) = {
    SEE = 912;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA1SU1_T1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(8) @ 0b00 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 913) = {
    SEE = 913;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    OP : bits(2) = op_code[17 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    RM : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVTA_asimd_A1_A_decode(D, size, OP, Vd, RM, op, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b0 @ _ : bits(1) @ 0b111 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 914) = {
    SEE = 914;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[10]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VNEG_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111101111111 @ _ : bits(4) @ 0b1010 @ _ : bits(12) as op_code) if SEE < 915) = {
    SEE = 915;
    imm4 : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    UDF_T2_A_decode(imm4, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b01110000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b00 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 916) = {
    SEE = 916;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Rm : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMUAD_A1_A_decode(cond, Rd, Rm, M, Rn)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 917) = {
    SEE = 917;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111100111011 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(4) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 918) = {
    SEE = 918;
    option_name : bits(4) = op_code[3 .. 0];
    ISB_T1_A_decode(option_name)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(12) as op_code) if SEE < 919) = {
    SEE = 919;
    imod : bits(2) = op_code[10 .. 9];
    M : bits(1) = [op_code[8]];
    A : bits(1) = [op_code[7]];
    I : bits(1) = [op_code[6]];
    F : bits(1) = [op_code[5]];
    mode : bits(5) = op_code[4 .. 0];
    CPS_T2_AS_decode(imod, M, A, I, F, mode)
}

function clause decode32 ((0b11110101 @ _ : bits(2) @ 0b01 @ _ : bits(4) @ 0b1111 @ _ : bits(12) as op_code) if SEE < 920) = {
    SEE = 920;
    U : bits(1) = [op_code[23]];
    R : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    imm12 : bits(12) = op_code[11 .. 0];
    PLD_i_A1_A_decode(U, R, Rn, imm12)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b00 @ _ : bits(1) @ 0b11 @ _ : bits(4) as op_code) if SEE < 921) = {
    SEE = 921;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMVN_i_T1A1_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 922) = {
    SEE = 922;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VMUL_f_A1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 923) = {
    SEE = 923;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01110 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 924) = {
    SEE = 924;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQABS_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b011010001111 @ _ : bits(8) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 925) = {
    SEE = 925;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    SXTB16_A1_A_decode(cond, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00000100 @ _ : bits(12) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 926) = {
    SEE = 926;
    cond : bits(4) = op_code[31 .. 28];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    UMAAL_A1_A_decode(cond, RdHi, RdLo, Rm, Rn)
}

function clause decode32 ((_ : bits(4) @ 0b001100100000 @ _ : bits(8) @ 0b1111 @ _ : bits(4) as op_code) if SEE < 927) = {
    SEE = 927;
    cond : bits(4) = op_code[31 .. 28];
    option_name : bits(4) = op_code[3 .. 0];
    DBG_A1_A_decode(cond, option_name)
}

function clause decode32 ((0b111110101101 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 928) = {
    SEE = 928;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    QSUB16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000100 @ _ : bits(13) @ 0b1001 @ _ : bits(4) as op_code) if SEE < 929) = {
    SEE = 929;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    RdHi : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    UMULL_A1_A_decode(cond, S, RdHi, RdLo, Rm, Rn)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1101 @ _ : bits(8) as op_code) if SEE < 930) = {
    SEE = 930;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b011 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 931) = {
    SEE = 931;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    STRB_r_A1_A_decode(cond, P, U, W, Rn, Rt, imm5, typ, Rm)
}

function clause decode32 ((0b111100100 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 932) = {
    SEE = 932;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADD_i_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 933) = {
    SEE = 933;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100011 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 934) = {
    SEE = 934;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SHASX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b00000000010 as op_code) if SEE < 935) = {
    SEE = 935;
    WFE_T2_A_decode()
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b0111 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 936) = {
    SEE = 936;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABD_i_T2A2_A_decode(U, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111110010001 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 937) = {
    SEE = 937;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRSB_i_T2_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((0b1110100010 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 938) = {
    SEE = 938;
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    P : bits(1) = [op_code[15]];
    M : bits(1) = [op_code[14]];
    register_list : bits(14) = op_code[13 .. 0];
    LDM_T2_A_decode(W, Rn, P, M, register_list)
}

function clause decode32 ((0b111011111 @ _ : bits(11) @ 0b0100 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 939) = {
    SEE = 939;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADDHN_T1A1_A_decode(D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b1011001001 @ _ : bits(6) as op_code) if SEE < 940) = {
    SEE = 940;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    SXTB_T1_A_decode(Rm, Rd)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 941) = {
    SEE = 941;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01101011 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 942) = {
    SEE = 942;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    rotate : bits(2) = op_code[11 .. 10];
    Rm : bits(4) = op_code[3 .. 0];
    SXTAH_A1_A_decode(cond, Rn, Rd, rotate, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b11 @ _ : bits(4) @ 0b010 @ _ : bits(1) @ 0b1 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 943) = {
    SEE = 943;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    F : bits(1) = [op_code[8]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRSQRTE_T1_A_decode(D, size, Vd, F, Q, M, Vm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b11 @ _ : bits(4) @ 0b011 @ _ : bits(4) @ 0b0 @ _ : bits(4) as op_code) if SEE < 944) = {
    SEE = 944;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[8 .. 7];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_is_A1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b100000 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 945) = {
    SEE = 945;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    STMDA_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 946) = {
    SEE = 946;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[7 .. 6];
    T : bits(1) = [op_code[5]];
    a : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_a_T1A1_A_decode(D, Rn, Vd, size, T, a, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01100110 @ _ : bits(12) @ 0b0111 @ _ : bits(4) as op_code) if SEE < 947) = {
    SEE = 947;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    UQSUB16_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b1110100110 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 948) = {
    SEE = 948;
    W : bits(1) = [op_code[21]];
    mode : bits(5) = op_code[4 .. 0];
    SRS_T2_AS_decode(W, mode)
}

function clause decode32 ((_ : bits(4) @ 0b0000101 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 949) = {
    SEE = 949;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    ADC_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 950) = {
    SEE = 950;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SADD16_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01101000 @ _ : bits(12) @ 0b1011 @ _ : bits(4) as op_code) if SEE < 951) = {
    SEE = 951;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SEL_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b00 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 952) = {
    SEE = 952;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T1A1pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b001001001111 @ _ : bits(16) as op_code) if SEE < 953) = {
    SEE = 953;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    ADR_A2_A_decode(cond, Rd, imm12)
}

function clause decode32 ((0b111111110 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 954) = {
    SEE = 954;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADD_f_T1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((_ : bits(16) @ 0b0101001 @ _ : bits(9) as op_code) if SEE < 955) = {
    SEE = 955;
    Rm : bits(3) = op_code[8 .. 6];
    Rn : bits(3) = op_code[5 .. 3];
    Rt : bits(3) = op_code[2 .. 0];
    STRH_r_T1_A_decode(Rm, Rn, Rt)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b10 @ _ : bits(1) @ 0b10 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 956) = {
    SEE = 956;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VORR_i_T2A2_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b10101011110 @ _ : bits(15) as op_code) if SEE < 957) = {
    SEE = 957;
    i : bits(1) = [op_code[26]];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    ADR_T2_A_decode(i, imm3, Rd, imm8)
}

function clause decode32 ((0b1110100 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b11111 @ _ : bits(16) as op_code) if SEE < 958) = {
    SEE = 958;
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rt : bits(4) = op_code[15 .. 12];
    Rt2 : bits(4) = op_code[11 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRD_l_T1_A_decode(P, U, W, Rt, Rt2, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b0000001 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 959) = {
    SEE = 959;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    EOR_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0000000000 @ _ : bits(6) as op_code) if SEE < 960) = {
    SEE = 960;
    Rm : bits(3) = op_code[5 .. 3];
    Rd : bits(3) = op_code[2 .. 0];
    MOV_r_T2archex_A_decode(Rm, Rd)
}

function clause decode32 ((0b11110 @ _ : bits(1) @ 0b11011011110 @ _ : bits(15) as op_code) if SEE < 961) = {
    SEE = 961;
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    msb : bits(5) = op_code[4 .. 0];
    BFC_T1_A_decode(imm3, Rd, imm2, msb)
}

function clause decode32 ((0b111110111110 @ _ : bits(12) @ 0b0110 @ _ : bits(4) as op_code) if SEE < 962) = {
    SEE = 962;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UMAAL_T1_A_decode(Rn, RdLo, RdHi, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b000 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b1 @ _ : bits(12) @ 0b1101 @ _ : bits(4) as op_code) if SEE < 963) = {
    SEE = 963;
    cond : bits(4) = op_code[31 .. 28];
    P : bits(1) = [op_code[24]];
    U : bits(1) = [op_code[23]];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm4H : bits(4) = op_code[11 .. 8];
    imm4L : bits(4) = op_code[3 .. 0];
    LDRSB_i_A1_A_decode(cond, P, U, W, Rn, Rt, imm4H, imm4L)
}

function clause decode32 ((0b111110100000 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 964) = {
    SEE = 964;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    SXTAH_T1_A_decode(Rn, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b100010 @ _ : bits(1) @ 0b1 @ _ : bits(20) as op_code) if SEE < 965) = {
    SEE = 965;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    LDM_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b11 @ _ : bits(4) @ 0b011 @ _ : bits(4) @ 0b0 @ _ : bits(4) as op_code) if SEE < 966) = {
    SEE = 966;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[8 .. 7];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_is_T1_A_decode(D, size, Vd, op, Q, M, Vm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1000 @ _ : bits(8) as op_code) if SEE < 967) = {
    SEE = 967;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111011110 @ _ : bits(11) @ 0b1011 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 968) = {
    SEE = 968;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VPADD_i_T1A1_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 969) = {
    SEE = 969;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b001111 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 970) = {
    SEE = 970;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    AESIMC_A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b11 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 971) = {
    SEE = 971;
    i : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    op : bits(1) = [op_code[5]];
    imm4 : bits(4) = op_code[3 .. 0];
    VMOV_i_T4A4pre_A_decode(i, D, imm3, Vd, cmode, Q, op, imm4)
}

function clause decode32 ((_ : bits(4) @ 0b01100001 @ _ : bits(12) @ 0b0011 @ _ : bits(4) as op_code) if SEE < 972) = {
    SEE = 972;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    SASX_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0011 @ _ : bits(8) as op_code) if SEE < 973) = {
    SEE = 973;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111100100 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b1110 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 974) = {
    SEE = 974;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCEQ_r_A2_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110101001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1000 @ _ : bits(4) as op_code) if SEE < 975) = {
    SEE = 975;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    REV_T2_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b11111010001111111111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 976) = {
    SEE = 976;
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    UXTB16_T1_A_decode(Rd, rotate, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b000 @ _ : bits(7) @ 0b0 @ _ : bits(2) @ 0b10 @ _ : bits(1) @ 0b01 @ _ : bits(4) as op_code) if SEE < 977) = {
    SEE = 977;
    i : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm3 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    cmode : bits(4) = op_code[11 .. 8];
    Q : bits(1) = [op_code[6]];
    imm4 : bits(4) = op_code[3 .. 0];
    VORR_i_T1A1_A_decode(i, D, imm3, Vd, cmode, Q, imm4)
}

function clause decode32 ((0b111101010111 @ _ : bits(12) @ 0b0100 @ _ : bits(4) as op_code) if SEE < 978) = {
    SEE = 978;
    option_name : bits(4) = op_code[3 .. 0];
    DSB_A1_A_decode(option_name)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b000 @ _ : bits(9) as op_code) if SEE < 979) = {
    SEE = 979;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD4_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b00 @ _ : bits(4) @ 0b01110 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 980) = {
    SEE = 980;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQABS_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b0000100 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 981) = {
    SEE = 981;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    ADD_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00011100 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 982) = {
    SEE = 982;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rt : bits(4) = op_code[3 .. 0];
    STREXB_A1_A_decode(cond, Rn, Rd, Rt)
}

function clause decode32 ((_ : bits(4) @ 0b00010 @ _ : bits(1) @ 0b00 @ _ : bits(10) @ 0b0 @ _ : bits(1) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 983) = {
    SEE = 983;
    cond : bits(4) = op_code[31 .. 28];
    R : bits(1) = [op_code[22]];
    Rd : bits(4) = op_code[15 .. 12];
    MRS_A1_AS_decode(cond, R, Rd)
}

function clause decode32 ((_ : bits(4) @ 0b100010 @ _ : bits(1) @ 0b0 @ _ : bits(20) as op_code) if SEE < 984) = {
    SEE = 984;
    cond : bits(4) = op_code[31 .. 28];
    W : bits(1) = [op_code[21]];
    Rn : bits(4) = op_code[19 .. 16];
    register_list : bits(16) = op_code[15 .. 0];
    STM_A1_A_decode(cond, W, Rn, register_list)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 985) = {
    SEE = 985;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST3_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111100111010 @ _ : bits(4) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b00000000011 as op_code) if SEE < 986) = {
    SEE = 986;
    WFI_T2_A_decode()
}

function clause decode32 ((0b111111110 @ _ : bits(11) @ 0b1100 @ _ : bits(3) @ 0b1 @ _ : bits(4) as op_code) if SEE < 987) = {
    SEE = 987;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQRDMLSH_T1A1pre_A_decode(D, size, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0010 @ _ : bits(8) as op_code) if SEE < 988) = {
    SEE = 988;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST1_m_T4A4_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b01110011 @ _ : bits(12) @ 0b0001 @ _ : bits(4) as op_code) if SEE < 989) = {
    SEE = 989;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    Rn : bits(4) = op_code[3 .. 0];
    UDIV_A1_A_decode(cond, Rd, Ra, Rm, Rn)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b00010 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 990) = {
    SEE = 990;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VUZP_T1A1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b111110010 @ _ : bits(1) @ 0b10 @ _ : bits(20) as op_code) if SEE < 991) = {
    SEE = 991;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD3_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b00111 @ _ : bits(11) as op_code) if SEE < 992) = {
    SEE = 992;
    Rdn : bits(3) = op_code[10 .. 8];
    imm8 : bits(8) = op_code[7 .. 0];
    SUB_i_T2_A_decode(Rdn, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b00010111 @ _ : bits(12) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 993) = {
    SEE = 993;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rs : bits(4) = op_code[11 .. 8];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    CMN_rr_A1_A_decode(cond, Rn, Rs, typ, Rm)
}

function clause decode32 ((0b11110 @ _ : bits(11) @ 0b10 @ _ : bits(1) @ 0b0 @ _ : bits(12) as op_code) if SEE < 994) = {
    SEE = 994;
    S : bits(1) = [op_code[26]];
    cond : bits(4) = op_code[25 .. 22];
    imm6 : bits(6) = op_code[21 .. 16];
    J1 : bits(1) = [op_code[13]];
    J2 : bits(1) = [op_code[11]];
    imm11 : bits(11) = op_code[10 .. 0];
    B_T3_A_decode(S, cond, imm6, J1, J2, imm11)
}

function clause decode32 ((_ : bits(4) @ 0b11101 @ _ : bits(1) @ 0b111 @ _ : bits(7) @ 0b10 @ _ : bits(3) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 995) = {
    SEE = 995;
    cond : bits(4) = op_code[31 .. 28];
    D : bits(1) = [op_code[22]];
    opc2 : bits(3) = op_code[18 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_iv_A1_A_decode(cond, D, opc2, Vd, size, op, M, Vm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11111 @ _ : bits(11) @ 0b0111 @ _ : bits(1) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 996) = {
    SEE = 996;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABD_i_T2A2_A_decode(U, D, size, Vn, Vd, N, M, Vm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0111 @ _ : bits(8) as op_code) if SEE < 997) = {
    SEE = 997;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST4_1_T2A2_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111110011011 @ _ : bits(20) as op_code) if SEE < 998) = {
    SEE = 998;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm12 : bits(12) = op_code[11 .. 0];
    LDRSH_i_T1_A_decode(Rn, Rt, imm12)
}

function clause decode32 ((_ : bits(4) @ 0b00010100 @ _ : bits(12) @ 0b0101 @ _ : bits(4) as op_code) if SEE < 999) = {
    SEE = 999;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[3 .. 0];
    QDADD_A1_A_decode(cond, Rn, Rd, Rm)
}

function clause decode32 ((0b111 @ _ : bits(1) @ 0b11110 @ _ : bits(11) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1000) = {
    SEE = 1000;
    U : bits(1) = [op_code[28]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[9]];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VHADD_T1A1_A_decode(U, D, size, Vn, Vd, op, N, Q, M, Vm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b11 @ _ : bits(4) @ 0b00 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1001) = {
    SEE = 1001;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    RM : bits(2) = op_code[9 .. 8];
    op : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVTA_asimd_T1_A_decode(D, size, Vd, RM, op, Q, M, Vm)
}

function clause decode32 ((0b111100101 @ _ : bits(11) @ 0b0 @ _ : bits(1) @ 0b11 @ _ : bits(1) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1002) = {
    SEE = 1002;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[10]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VQDMLAL_T2A2_A_decode(D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111100110 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b1101 @ _ : bits(3) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1003) = {
    SEE = 1003;
    D : bits(1) = [op_code[22]];
    sz : bits(1) = [op_code[20]];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    N : bits(1) = [op_code[7]];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VABD_f_A1_A_decode(D, sz, Vn, Vd, N, Q, M, Vm)
}

function clause decode32 ((0b111110000001 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 1004) = {
    SEE = 1004;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRB_i_T3_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((0b111100111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b001111 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1005) = {
    SEE = 1005;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    SHA256SU0_A1_A_decode(D, size, Vd, M, Vm)
}

function clause decode32 ((_ : bits(4) @ 0b00011101 @ _ : bits(10) @ 0b111001 @ _ : bits(4) as op_code) if SEE < 1006) = {
    SEE = 1006;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    LDREXB_A1_A_decode(cond, Rn, Rt)
}

function clause decode32 ((0b111110101010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b0010 @ _ : bits(4) as op_code) if SEE < 1007) = {
    SEE = 1007;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    SHASX_T1_A_decode(Rn, Rd, Rm)
}

function clause decode32 ((0b111110110010 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b000 @ _ : bits(5) as op_code) if SEE < 1008) = {
    SEE = 1008;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    M : bits(1) = [op_code[4]];
    Rm : bits(4) = op_code[3 .. 0];
    SMUAD_T1_A_decode(Rn, Rd, M, Rm)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b0110 @ _ : bits(8) as op_code) if SEE < 1009) = {
    SEE = 1009;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD1_m_T3A3_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((_ : bits(16) @ 0b0100000101 @ _ : bits(6) as op_code) if SEE < 1010) = {
    SEE = 1010;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    ADC_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((_ : bits(16) @ 0b0100000011 @ _ : bits(6) as op_code) if SEE < 1011) = {
    SEE = 1011;
    Rm : bits(3) = op_code[5 .. 3];
    Rdn : bits(3) = op_code[2 .. 0];
    LSR_r_T1_A_decode(Rm, Rdn)
}

function clause decode32 ((0b11101010011 @ _ : bits(21) as op_code) if SEE < 1012) = {
    SEE = 1012;
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    imm3 : bits(3) = op_code[14 .. 12];
    Rd : bits(4) = op_code[11 .. 8];
    imm2 : bits(2) = op_code[7 .. 6];
    typ : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    ORN_r_T1_A_decode(S, Rn, imm3, Rd, imm2, typ, Rm)
}

function clause decode32 ((0b111101001 @ _ : bits(1) @ 0b10 @ _ : bits(8) @ 0b1001 @ _ : bits(8) as op_code) if SEE < 1013) = {
    SEE = 1013;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VLD2_1_T3A3_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b00010111 @ _ : bits(15) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1014) = {
    SEE = 1014;
    cond : bits(4) = op_code[31 .. 28];
    Rn : bits(4) = op_code[19 .. 16];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    CMN_r_A1_A_decode(cond, Rn, imm5, typ, Rm)
}

function clause decode32 ((0b111110011 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b0001 @ _ : bits(8) as op_code) if SEE < 1015) = {
    SEE = 1015;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    size : bits(2) = op_code[11 .. 10];
    index_align : bits(4) = op_code[7 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_1_T1A1_A_decode(D, Rn, Vd, size, index_align, Rm)
}

function clause decode32 ((0b111110000001 @ _ : bits(8) @ 0b1110 @ _ : bits(8) as op_code) if SEE < 1016) = {
    SEE = 1016;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    imm8 : bits(8) = op_code[7 .. 0];
    LDRBT_T1pre_A_decode(Rn, Rt, imm8)
}

function clause decode32 ((0b111101000 @ _ : bits(1) @ 0b00 @ _ : bits(8) @ 0b100 @ _ : bits(9) as op_code) if SEE < 1017) = {
    SEE = 1017;
    D : bits(1) = [op_code[22]];
    Rn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    typ : bits(4) = op_code[11 .. 8];
    size : bits(2) = op_code[7 .. 6];
    align : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    VST2_m_T1A1_A_decode(D, Rn, Vd, typ, size, align, Rm)
}

function clause decode32 ((0b111110100001 @ _ : bits(4) @ 0b1111 @ _ : bits(4) @ 0b1 @ _ : bits(7) as op_code) if SEE < 1018) = {
    SEE = 1018;
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[11 .. 8];
    rotate : bits(2) = op_code[5 .. 4];
    Rm : bits(4) = op_code[3 .. 0];
    UXTAH_T1_A_decode(Rn, Rd, rotate, Rm)
}

function clause decode32 ((_ : bits(4) @ 0b0000000 @ _ : bits(16) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1019) = {
    SEE = 1019;
    cond : bits(4) = op_code[31 .. 28];
    S : bits(1) = [op_code[20]];
    Rn : bits(4) = op_code[19 .. 16];
    Rd : bits(4) = op_code[15 .. 12];
    imm5 : bits(5) = op_code[11 .. 7];
    typ : bits(2) = op_code[6 .. 5];
    Rm : bits(4) = op_code[3 .. 0];
    AND_r_A1_A_decode(cond, S, Rn, Rd, imm5, typ, Rm)
}

function clause decode32 ((0b111111111 @ _ : bits(1) @ 0b11 @ _ : bits(2) @ 0b10 @ _ : bits(4) @ 0b01011 @ _ : bits(2) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1020) = {
    SEE = 1020;
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[19 .. 18];
    Vd : bits(4) = op_code[15 .. 12];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VRINTZ_asimd_T1_A_decode(D, size, Vd, Q, M, Vm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b11 @ _ : bits(2) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(4) as op_code) if SEE < 1021) = {
    SEE = 1021;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    imm6 : bits(6) = op_code[21 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(2) = op_code[9 .. 8];
    Q : bits(1) = [op_code[6]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VCVT_xs_A1_A_decode(U, D, imm6, Vd, op, Q, M, Vm)
}

function clause decode32 ((0b111110111010 @ _ : bits(12) @ 0b0000 @ _ : bits(4) as op_code) if SEE < 1022) = {
    SEE = 1022;
    Rn : bits(4) = op_code[19 .. 16];
    RdLo : bits(4) = op_code[15 .. 12];
    RdHi : bits(4) = op_code[11 .. 8];
    Rm : bits(4) = op_code[3 .. 0];
    UMULL_T1_A_decode(Rn, RdLo, RdHi, Rm)
}

function clause decode32 ((0b1111001 @ _ : bits(1) @ 0b1 @ _ : bits(11) @ 0b000 @ _ : bits(2) @ 0b0 @ _ : bits(1) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1023) = {
    SEE = 1023;
    U : bits(1) = [op_code[24]];
    D : bits(1) = [op_code[22]];
    size : bits(2) = op_code[21 .. 20];
    Vn : bits(4) = op_code[19 .. 16];
    Vd : bits(4) = op_code[15 .. 12];
    op : bits(1) = [op_code[8]];
    N : bits(1) = [op_code[7]];
    M : bits(1) = [op_code[5]];
    Vm : bits(4) = op_code[3 .. 0];
    VADDL_T1A1_A_decode(U, D, size, Vn, Vd, op, N, M, Vm)
}

function clause decode32 ((0b111110000000 @ _ : bits(8) @ 0b1 @ _ : bits(11) as op_code) if SEE < 1024) = {
    SEE = 1024;
    Rn : bits(4) = op_code[19 .. 16];
    Rt : bits(4) = op_code[15 .. 12];
    P : bits(1) = [op_code[10]];
    U : bits(1) = [op_code[9]];
    W : bits(1) = [op_code[8]];
    imm8 : bits(8) = op_code[7 .. 0];
    STRB_i_T3_A_decode(Rn, Rt, P, U, W, imm8)
}

function clause decode32 ((_ : bits(4) @ 0b01110101 @ _ : bits(12) @ 0b11 @ _ : bits(1) @ 0b1 @ _ : bits(4) as op_code) if SEE < 1025) = {
    SEE = 1025;
    cond : bits(4) = op_code[31 .. 28];
    Rd : bits(4) = op_code[19 .. 16];
    Ra : bits(4) = op_code[15 .. 12];
    Rm : bits(4) = op_code[11 .. 8];
    R : bits(1) = [op_code[5]];
    Rn : bits(4) = op_code[3 .. 0];
    SMMLS_A1_A_decode(cond, Rd, Ra, Rm, R, Rn)
}

function clause decode64 ((0b10011011001 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1026) = {
    SEE = 1026;
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

function clause decode64 ((_ : bits(1) @ 0b1001011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1027) = {
    SEE = 1027;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101001 @ _ : bits(10) as op_code) if SEE < 1028) = {
    SEE = 1028;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1029) = {
    SEE = 1029;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101011 @ _ : bits(10) as op_code) if SEE < 1030) = {
    SEE = 1030;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b010100111 @ _ : bits(22) as op_code) if SEE < 1031) = {
    SEE = 1031;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_preidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) if SEE < 1032) = {
    SEE = 1032;
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

function clause decode64 ((0b0 @ _ : bits(2) @ 0b0111100000 @ _ : bits(7) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1033) = {
    SEE = 1033;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111100000 @ _ : bits(3) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1034) = {
    SEE = 1034;
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

function clause decode64 ((0b0110100100 @ _ : bits(22) as op_code) if SEE < 1035) = {
    SEE = 1035;
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xt2 : bits(5) = op_code[14 .. 10];
    simm7 : bits(7) = op_code[21 .. 15];
    integer_tags_mcsettaganddatapair_decode(Xt, Xn, Xt2, simm7)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b101 @ _ : bits(10) as op_code) if SEE < 1036) = {
    SEE = 1036;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autib_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1037) = {
    SEE = 1037;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1038) = {
    SEE = 1038;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b0111111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1039) = {
    SEE = 1039;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110011 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1040) = {
    SEE = 1040;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1041) = {
    SEE = 1041;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_truncating_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b01001000110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1042) = {
    SEE = 1042;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) if SEE < 1043) = {
    SEE = 1043;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode64 ((0b11010101000000110010001000011111 as op_code) if SEE < 1044) = {
    SEE = 1044;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) if SEE < 1045) = {
    SEE = 1045;
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

function clause decode64 ((0b11010101000000110011 @ _ : bits(4) @ 0b11011111 as op_code) if SEE < 1046) = {
    SEE = 1046;
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b01111110110 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1047) = {
    SEE = 1047;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) if SEE < 1048) = {
    SEE = 1048;
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

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1049) = {
    SEE = 1049;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(5) @ 0b1110 @ _ : bits(12) as op_code) if SEE < 1050) = {
    SEE = 1050;
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

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b011000 @ _ : bits(16) as op_code) if SEE < 1051) = {
    SEE = 1051;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1052) = {
    SEE = 1052;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111001111001100010 @ _ : bits(10) as op_code) if SEE < 1053) = {
    SEE = 1053;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001110 @ _ : bits(10) as op_code) if SEE < 1054) = {
    SEE = 1054;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_addsub_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) if SEE < 1055) = {
    SEE = 1055;
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

function clause decode64 ((_ : bits(1) @ 0b0111010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1056) = {
    SEE = 1056;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode64 ((0b10111000100 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1057) = {
    SEE = 1057;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101111 @ _ : bits(10) as op_code) if SEE < 1058) = {
    SEE = 1058;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_wrapping_pair_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b10011010110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1059) = {
    SEE = 1059;
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_tags_mcinserttagmask_decode(Xd, Xn, Xm)
}

function clause decode64 ((0b11010101000000110010000001011111 as op_code) if SEE < 1060) = {
    SEE = 1060;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0110100101 @ _ : bits(22) as op_code) if SEE < 1061) = {
    SEE = 1061;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_offset_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b00001000110 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1062) = {
    SEE = 1062;
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

function clause decode64 ((0b0101111010110000110010 @ _ : bits(10) as op_code) if SEE < 1063) = {
    SEE = 1063;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16maxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1064) = {
    SEE = 1064;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_integer_dup_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1065) = {
    SEE = 1065;
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

function clause decode64 ((_ : bits(1) @ 0b0010001 @ _ : bits(24) as op_code) if SEE < 1066) = {
    SEE = 1066;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) if SEE < 1067) = {
    SEE = 1067;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100000111110 @ _ : bits(10) as op_code) if SEE < 1068) = {
    SEE = 1068;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_float_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101011000001110 @ _ : bits(12) as op_code) if SEE < 1069) = {
    SEE = 1069;
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

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1070) = {
    SEE = 1070;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((_ : bits(2) @ 0b10110100 @ _ : bits(22) as op_code) if SEE < 1071) = {
    SEE = 1071;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b010111111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1072) = {
    SEE = 1072;
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

function clause decode64 ((0b00111000000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1073) = {
    SEE = 1073;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b01001000000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1074) = {
    SEE = 1074;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1075) = {
    SEE = 1075;
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

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1076) = {
    SEE = 1076;
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

function clause decode64 ((0b00011111 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1077) = {
    SEE = 1077;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) if SEE < 1078) = {
    SEE = 1078;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_int_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b1001000110 @ _ : bits(22) as op_code) if SEE < 1079) = {
    SEE = 1079;
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    uimm4 : bits(4) = op_code[13 .. 10];
    op3 : bits(2) = op_code[15 .. 14];
    uimm6 : bits(6) = op_code[21 .. 16];
    integer_tags_mcaddtag_decode(Xd, Xn, uimm4, op3, uimm6)
}

function clause decode64 ((_ : bits(1) @ 0b1001011001 @ _ : bits(21) as op_code) if SEE < 1080) = {
    SEE = 1080;
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

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1081) = {
    SEE = 1081;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1082) = {
    SEE = 1082;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_int_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(5) @ 0b0000 @ _ : bits(12) as op_code) if SEE < 1083) = {
    SEE = 1083;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) if SEE < 1084) = {
    SEE = 1084;
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

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1085) = {
    SEE = 1085;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((_ : bits(1) @ 0b0111010010 @ _ : bits(9) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1086) = {
    SEE = 1086;
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

function clause decode64 ((0b010111100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1087) = {
    SEE = 1087;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((0b10111000100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1088) = {
    SEE = 1088;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b01111000000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1089) = {
    SEE = 1089;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1090) = {
    SEE = 1090;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111010110000111110 @ _ : bits(10) as op_code) if SEE < 1091) = {
    SEE = 1091;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16max_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0001011001 @ _ : bits(21) as op_code) if SEE < 1092) = {
    SEE = 1092;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111100000 @ _ : bits(6) @ 0b101 @ _ : bits(10) as op_code) if SEE < 1093) = {
    SEE = 1093;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) if SEE < 1094) = {
    SEE = 1094;
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

function clause decode64 ((_ : bits(1) @ 0b0011011000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1095) = {
    SEE = 1095;
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

function clause decode64 ((0b00001000100 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1096) = {
    SEE = 1096;
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

function clause decode64 ((0b0101111000110000110110 @ _ : bits(10) as op_code) if SEE < 1097) = {
    SEE = 1097;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16add_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1098) = {
    SEE = 1098;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1099) = {
    SEE = 1099;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b0111111011111001101010 @ _ : bits(10) as op_code) if SEE < 1100) = {
    SEE = 1100;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100000110000 @ _ : bits(10) as op_code) if SEE < 1101) = {
    SEE = 1101;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode64 ((0b01111111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1102) = {
    SEE = 1102;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000011010 @ _ : bits(10) as op_code) if SEE < 1103) = {
    SEE = 1103;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100001110000 @ _ : bits(10) as op_code) if SEE < 1104) = {
    SEE = 1104;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b110 @ _ : bits(2) @ 0b1 @ _ : bits(10) as op_code) if SEE < 1105) = {
    SEE = 1105;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rot : bits(2) = op_code[12 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_complex_decode(Rd, Rn, rot, Rm, size, U, Q)
}

function clause decode64 ((0b11010101000000110010000000011111 as op_code) if SEE < 1106) = {
    SEE = 1106;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111000110000110010 @ _ : bits(10) as op_code) if SEE < 1107) = {
    SEE = 1107;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16maxnm_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode64 ((0b0101111001111001110010 @ _ : bits(10) as op_code) if SEE < 1108) = {
    SEE = 1108;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size_1_ : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, size_1_, U)
}

function clause decode64 ((0b00011001001 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1109) = {
    SEE = 1109;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairpre_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b00001000000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1110) = {
    SEE = 1110;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) if SEE < 1111) = {
    SEE = 1111;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b00011001101 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1112) = {
    SEE = 1112;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairandzerodatapost_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) if SEE < 1113) = {
    SEE = 1113;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_extract_sqxtun_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1114) = {
    SEE = 1114;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110000101010 @ _ : bits(10) as op_code) if SEE < 1115) = {
    SEE = 1115;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1116) = {
    SEE = 1116;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode(Rd, Rn, S, Rm, size, U, Q)
}

function clause decode64 ((0b01011110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1117) = {
    SEE = 1117;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) if SEE < 1118) = {
    SEE = 1118;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1hash_majority_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001010 @ _ : bits(10) as op_code) if SEE < 1119) = {
    SEE = 1119;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_addsub_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) if SEE < 1120) = {
    SEE = 1120;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    P : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha256hash_decode(Rd, Rn, P, Rm, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) if SEE < 1121) = {
    SEE = 1121;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100100 @ _ : bits(10) as op_code) if SEE < 1122) = {
    SEE = 1122;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode(Rd, Rn, o1, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) if SEE < 1123) = {
    SEE = 1123;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmax_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1124) = {
    SEE = 1124;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b000010001 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) if SEE < 1125) = {
    SEE = 1125;
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

function clause decode64 ((0b11010101000000110011 @ _ : bits(4) @ 0b01011111 as op_code) if SEE < 1126) = {
    SEE = 1126;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_monitors_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1127) = {
    SEE = 1127;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_int_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b01 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1128) = {
    SEE = 1128;
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

function clause decode64 ((_ : bits(1) @ 0b1101011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1129) = {
    SEE = 1129;
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

function clause decode64 ((0b0101111011111001110110 @ _ : bits(10) as op_code) if SEE < 1130) = {
    SEE = 1130;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size_1_ : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_recip_fp16_sisd_decode(Rd, Rn, opcode, size_1_, U)
}

function clause decode64 ((0b110101010001 @ _ : bits(20) as op_code) if SEE < 1131) = {
    SEE = 1131;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    o0 : bits(1) = [op_code[19]];
    L : bits(1) = [op_code[21]];
    system_register_system_decode(Rt, op2, CRm, CRn, op1, o0, L)
}

function clause decode64 ((0b01111111 @ _ : bits(8) @ 0b1111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1132) = {
    SEE = 1132;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1133) = {
    SEE = 1133;
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

function clause decode64 ((_ : bits(1) @ 0b1111010010 @ _ : bits(9) @ 0b00 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1134) = {
    SEE = 1134;
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

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) if SEE < 1135) = {
    SEE = 1135;
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

function clause decode64 ((_ : bits(1) @ 0b0011010100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1136) = {
    SEE = 1136;
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

function clause decode64 ((0b10011000 @ _ : bits(24) as op_code) if SEE < 1137) = {
    SEE = 1137;
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_general_decode(Rt, imm19, V, opc)
}

function clause decode64 ((_ : bits(1) @ 0b1011010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1138) = {
    SEE = 1138;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1139) = {
    SEE = 1139;
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

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b10 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1140) = {
    SEE = 1140;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_offset_normal_memory_single_simdfp_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) if SEE < 1141) = {
    SEE = 1141;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b11010101000000110011 @ _ : bits(4) @ 0b10111111 as op_code) if SEE < 1142) = {
    SEE = 1142;
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0100111000101000011010 @ _ : bits(10) as op_code) if SEE < 1143) = {
    SEE = 1143;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_mix_decode(Rd, Rn, D, size)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b111 @ _ : bits(10) as op_code) if SEE < 1144) = {
    SEE = 1144;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autdb_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) if SEE < 1145) = {
    SEE = 1145;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_int_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) if SEE < 1146) = {
    SEE = 1146;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000001 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1147) = {
    SEE = 1147;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1148) = {
    SEE = 1148;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1149) = {
    SEE = 1149;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110001101010 @ _ : bits(10) as op_code) if SEE < 1150) = {
    SEE = 1150;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111001101110 @ _ : bits(10) as op_code) if SEE < 1151) = {
    SEE = 1151;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) if SEE < 1152) = {
    SEE = 1152;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) if SEE < 1153) = {
    SEE = 1153;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) if SEE < 1154) = {
    SEE = 1154;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110011 @ _ : bits(10) as op_code) if SEE < 1155) = {
    SEE = 1155;
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

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) if SEE < 1156) = {
    SEE = 1156;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha256sched1_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1157) = {
    SEE = 1157;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_rsqrtsfp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b1101011 @ _ : bits(1) @ 0b0001111100001 @ _ : bits(11) as op_code) if SEE < 1158) = {
    SEE = 1158;
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(5) @ 0b0100 @ _ : bits(12) as op_code) if SEE < 1159) = {
    SEE = 1159;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b1101010100000 @ _ : bits(3) @ 0b0100 @ _ : bits(7) @ 0b11111 as op_code) if SEE < 1160) = {
    SEE = 1160;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_register_cpsr_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) if SEE < 1161) = {
    SEE = 1161;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_xtn_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) if SEE < 1162) = {
    SEE = 1162;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((_ : bits(1) @ 0b1111010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1163) = {
    SEE = 1163;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1164) = {
    SEE = 1164;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1165) = {
    SEE = 1165;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1166) = {
    SEE = 1166;
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

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) if SEE < 1167) = {
    SEE = 1167;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) if SEE < 1168) = {
    SEE = 1168;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b11100101 @ _ : bits(23) as op_code) if SEE < 1169) = {
    SEE = 1169;
    Rd : bits(5) = op_code[4 .. 0];
    imm16 : bits(16) = op_code[20 .. 5];
    hw : bits(2) = op_code[22 .. 21];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_insext_insert_movewide_decode(Rd, imm16, hw, opc, sf)
}

function clause decode64 ((0b0101111100 @ _ : bits(6) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1170) = {
    SEE = 1170;
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

function clause decode64 ((0b00111000010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1171) = {
    SEE = 1171;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1172) = {
    SEE = 1172;
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

function clause decode64 ((0b010111111 @ _ : bits(7) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1173) = {
    SEE = 1173;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) if SEE < 1174) = {
    SEE = 1174;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1175) = {
    SEE = 1175;
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

function clause decode64 ((_ : bits(1) @ 0b0110100 @ _ : bits(24) as op_code) if SEE < 1176) = {
    SEE = 1176;
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    op : bits(1) = [op_code[24]];
    sf : bits(1) = [op_code[31]];
    branch_conditional_compare_decode(Rt, imm19, op, sf)
}

function clause decode64 ((0b10011011101 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1177) = {
    SEE = 1177;
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

function clause decode64 ((0b10111000101 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1178) = {
    SEE = 1178;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000011 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1179) = {
    SEE = 1179;
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

function clause decode64 ((0b01011110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1180) = {
    SEE = 1180;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b01 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1181) = {
    SEE = 1181;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1182) = {
    SEE = 1182;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110101000000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1183) = {
    SEE = 1183;
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

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) if SEE < 1184) = {
    SEE = 1184;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_add_saturating_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110111 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1185) = {
    SEE = 1185;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111000111110 @ _ : bits(10) as op_code) if SEE < 1186) = {
    SEE = 1186;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_fp16_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b1110001 @ _ : bits(24) as op_code) if SEE < 1187) = {
    SEE = 1187;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1188) = {
    SEE = 1188;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode64 ((_ : bits(1) @ 0b010100010 @ _ : bits(22) as op_code) if SEE < 1189) = {
    SEE = 1189;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_postidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1190) = {
    SEE = 1190;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1191) = {
    SEE = 1191;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0100111000101000010010 @ _ : bits(10) as op_code) if SEE < 1192) = {
    SEE = 1192;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_round_decode(Rd, Rn, D, size)
}

function clause decode64 ((0b0101111011111000110010 @ _ : bits(10) as op_code) if SEE < 1193) = {
    SEE = 1193;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1194) = {
    SEE = 1194;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_recpsfp16_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b0101111011111001111110 @ _ : bits(10) as op_code) if SEE < 1195) = {
    SEE = 1195;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_frecpxfp16_decode(Rd, Rn, opcode, a, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000000110 @ _ : bits(10) as op_code) if SEE < 1196) = {
    SEE = 1196;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rev_decode(Rd, Rn, o0, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1197) = {
    SEE = 1197;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_product_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1198) = {
    SEE = 1198;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1199) = {
    SEE = 1199;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_fused_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000101010 @ _ : bits(10) as op_code) if SEE < 1200) = {
    SEE = 1200;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_lessthan_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0101111000101000000010 @ _ : bits(10) as op_code) if SEE < 1201) = {
    SEE = 1201;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha2op_sha1hash_decode(Rd, Rn, opcode, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) if SEE < 1202) = {
    SEE = 1202;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtest_int_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100000000000100 @ _ : bits(12) as op_code) if SEE < 1203) = {
    SEE = 1203;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((_ : bits(1) @ 0b01100100 @ _ : bits(23) as op_code) if SEE < 1204) = {
    SEE = 1204;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000000010 @ _ : bits(10) as op_code) if SEE < 1205) = {
    SEE = 1205;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rev_decode(Rd, Rn, o0, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b000110 @ _ : bits(10) as op_code) if SEE < 1206) = {
    SEE = 1206;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_unzip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111000110110 @ _ : bits(10) as op_code) if SEE < 1207) = {
    SEE = 1207;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b010100000 @ _ : bits(22) as op_code) if SEE < 1208) = {
    SEE = 1208;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_noalloc_memory_pair_general_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) if SEE < 1209) = {
    SEE = 1209;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b10110101 @ _ : bits(22) as op_code) if SEE < 1210) = {
    SEE = 1210;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b011001 @ _ : bits(10) as op_code) if SEE < 1211) = {
    SEE = 1211;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftsat_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b000010 @ _ : bits(16) as op_code) if SEE < 1212) = {
    SEE = 1212;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110100100000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1213) = {
    SEE = 1213;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1214) = {
    SEE = 1214;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_cpydup_simd_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode64 ((0b000101 @ _ : bits(26) as op_code) if SEE < 1215) = {
    SEE = 1215;
    imm26 : bits(26) = op_code[25 .. 0];
    op : bits(1) = [op_code[31]];
    branch_unconditional_immediate_decode(imm26, op)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) if SEE < 1216) = {
    SEE = 1216;
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

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b011001 @ _ : bits(16) as op_code) if SEE < 1217) = {
    SEE = 1217;
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

function clause decode64 ((0b00001000110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1218) = {
    SEE = 1218;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1219) = {
    SEE = 1219;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b101001 @ _ : bits(10) as op_code) if SEE < 1220) = {
    SEE = 1220;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftlong_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) if SEE < 1221) = {
    SEE = 1221;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111000110110 @ _ : bits(10) as op_code) if SEE < 1222) = {
    SEE = 1222;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111000110010 @ _ : bits(10) as op_code) if SEE < 1223) = {
    SEE = 1223;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b10110110 @ _ : bits(22) as op_code) if SEE < 1224) = {
    SEE = 1224;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) if SEE < 1225) = {
    SEE = 1225;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_extended_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1226) = {
    SEE = 1226;
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

function clause decode64 ((0b11010101000000110010000010111111 as op_code) if SEE < 1227) = {
    SEE = 1227;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) if SEE < 1228) = {
    SEE = 1228;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_saturating_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b101101011000000000101 @ _ : bits(10) as op_code) if SEE < 1229) = {
    SEE = 1229;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[10]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_cnt_decode(Rd, Rn, op, opcode2, S, sf)
}

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) if SEE < 1230) = {
    SEE = 1230;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    P : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha256hash_decode(Rd, Rn, P, Rm, size)
}

function clause decode64 ((0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1231) = {
    SEE = 1231;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b10011011001 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1232) = {
    SEE = 1232;
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

function clause decode64 ((_ : bits(1) @ 0b0110111 @ _ : bits(24) as op_code) if SEE < 1233) = {
    SEE = 1233;
    Rt : bits(5) = op_code[4 .. 0];
    imm14 : bits(14) = op_code[18 .. 5];
    b40 : bits(5) = op_code[23 .. 19];
    op : bits(1) = [op_code[24]];
    b5 : bits(1) = [op_code[31]];
    branch_conditional_test_decode(Rt, imm14, b40, op, b5)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b011010 @ _ : bits(10) as op_code) if SEE < 1234) = {
    SEE = 1234;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_transpose_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1235) = {
    SEE = 1235;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0111100101 @ _ : bits(22) as op_code) if SEE < 1236) = {
    SEE = 1236;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) if SEE < 1237) = {
    SEE = 1237;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1238) = {
    SEE = 1238;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_nonuniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111000111010 @ _ : bits(10) as op_code) if SEE < 1239) = {
    SEE = 1239;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_lessthan_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000011 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1240) = {
    SEE = 1240;
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

function clause decode64 ((0b10111000100 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1241) = {
    SEE = 1241;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111001111001110010 @ _ : bits(10) as op_code) if SEE < 1242) = {
    SEE = 1242;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1243) = {
    SEE = 1243;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0001010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) if SEE < 1244) = {
    SEE = 1244;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b011110 @ _ : bits(10) as op_code) if SEE < 1245) = {
    SEE = 1245;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_zip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b0100 @ _ : bits(12) as op_code) if SEE < 1246) = {
    SEE = 1246;
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

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1247) = {
    SEE = 1247;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_float_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1248) = {
    SEE = 1248;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) if SEE < 1249) = {
    SEE = 1249;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftsat_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) if SEE < 1250) = {
    SEE = 1250;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b011000 @ _ : bits(24) as op_code) if SEE < 1251) = {
    SEE = 1251;
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_general_decode(Rt, imm19, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101010000001110 @ _ : bits(12) as op_code) if SEE < 1252) = {
    SEE = 1252;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000001 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1253) = {
    SEE = 1253;
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

function clause decode64 ((0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1254) = {
    SEE = 1254;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1255) = {
    SEE = 1255;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_left_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0110001 @ _ : bits(24) as op_code) if SEE < 1256) = {
    SEE = 1256;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) if SEE < 1257) = {
    SEE = 1257;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((0b00001000010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1258) = {
    SEE = 1258;
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

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1259) = {
    SEE = 1259;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_recip_float_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) if SEE < 1260) = {
    SEE = 1260;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010010 @ _ : bits(10) as op_code) if SEE < 1261) = {
    SEE = 1261;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1262) = {
    SEE = 1262;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_int_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111001111001101110 @ _ : bits(10) as op_code) if SEE < 1263) = {
    SEE = 1263;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b101001000000 @ _ : bits(10) as op_code) if SEE < 1264) = {
    SEE = 1264;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1265) = {
    SEE = 1265;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111001100010 @ _ : bits(10) as op_code) if SEE < 1266) = {
    SEE = 1266;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1267) = {
    SEE = 1267;
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

function clause decode64 ((0b11010101000000110011 @ _ : bits(4) @ 0b10011111 as op_code) if SEE < 1268) = {
    SEE = 1268;
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101000 @ _ : bits(10) as op_code) if SEE < 1269) = {
    SEE = 1269;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) if SEE < 1270) = {
    SEE = 1270;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_nosat_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1271) = {
    SEE = 1271;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1272) = {
    SEE = 1272;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp16_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1273) = {
    SEE = 1273;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1274) = {
    SEE = 1274;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b010001 @ _ : bits(10) as op_code) if SEE < 1275) = {
    SEE = 1275;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightinsert_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b110 @ _ : bits(10) as op_code) if SEE < 1276) = {
    SEE = 1276;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autda_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b11100100 @ _ : bits(22) as op_code) if SEE < 1277) = {
    SEE = 1277;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1278) = {
    SEE = 1278;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101101 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1279) = {
    SEE = 1279;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1280) = {
    SEE = 1280;
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

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1281) = {
    SEE = 1281;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((_ : bits(1) @ 0b1101010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) if SEE < 1282) = {
    SEE = 1282;
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

function clause decode64 ((0b10011001100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1283) = {
    SEE = 1283;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1284) = {
    SEE = 1284;
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

function clause decode64 ((0b0111111011111001110110 @ _ : bits(10) as op_code) if SEE < 1285) = {
    SEE = 1285;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_sqrtest_fp16_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode64 ((_ : bits(1) @ 0b0101010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) if SEE < 1286) = {
    SEE = 1286;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011111 @ _ : bits(10) as op_code) if SEE < 1287) = {
    SEE = 1287;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000101 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) if SEE < 1288) = {
    SEE = 1288;
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

function clause decode64 ((0b0110100110 @ _ : bits(22) as op_code) if SEE < 1289) = {
    SEE = 1289;
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xt2 : bits(5) = op_code[14 .. 10];
    simm7 : bits(7) = op_code[21 .. 15];
    integer_tags_mcsettaganddatapairpre_decode(Xt, Xn, Xt2, simm7)
}

function clause decode64 ((0b00001000010 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1290) = {
    SEE = 1290;
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

function clause decode64 ((0b01111000010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1291) = {
    SEE = 1291;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100011000000 @ _ : bits(10) as op_code) if SEE < 1292) = {
    SEE = 1292;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) if SEE < 1293) = {
    SEE = 1293;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_extract_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) if SEE < 1294) = {
    SEE = 1294;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011101 @ _ : bits(10) as op_code) if SEE < 1295) = {
    SEE = 1295;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) if SEE < 1296) = {
    SEE = 1296;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) if SEE < 1297) = {
    SEE = 1297;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1298) = {
    SEE = 1298;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_divfp16_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b00011001100 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1299) = {
    SEE = 1299;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagandzerodatapre_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1300) = {
    SEE = 1300;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_nonuniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1301) = {
    SEE = 1301;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((0b00011111 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1302) = {
    SEE = 1302;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111000100000010110 @ _ : bits(10) as op_code) if SEE < 1303) = {
    SEE = 1303;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_not_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) if SEE < 1304) = {
    SEE = 1304;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_tieaway_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b11010110101111110000001111100000 as op_code) if SEE < 1305) = {
    SEE = 1305;
    op4 : bits(5) = op_code[4 .. 0];
    Rt : bits(5) = op_code[9 .. 5];
    op3 : bits(6) = op_code[15 .. 10];
    op2 : bits(5) = op_code[20 .. 16];
    opc : bits(4) = op_code[24 .. 21];
    branch_unconditional_dret_decode(op4, Rt, op3, op2, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) if SEE < 1306) = {
    SEE = 1306;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[23]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower_decode(Rd, Rn, Rm, sz, S, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0011011000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1307) = {
    SEE = 1307;
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

function clause decode64 ((0b00011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1308) = {
    SEE = 1308;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b00011001010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1309) = {
    SEE = 1309;
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcgettag_decode(Xt, Xn, imm9)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000011010 @ _ : bits(10) as op_code) if SEE < 1310) = {
    SEE = 1310;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100010000001000 @ _ : bits(12) as op_code) if SEE < 1311) = {
    SEE = 1311;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((0b01011111 @ _ : bits(8) @ 0b0111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1312) = {
    SEE = 1312;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b111 @ _ : bits(1) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1313) = {
    SEE = 1313;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rot : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp_complex_decode(Rd, Rn, rot, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) if SEE < 1314) = {
    SEE = 1314;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(2) @ 0b011100 @ _ : bits(1) @ 0b100001111 @ _ : bits(1) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1315) = {
    SEE = 1315;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_frint_32_64_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000110 @ _ : bits(10) as op_code) if SEE < 1316) = {
    SEE = 1316;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_div_decode(Rd, Rn, opcode, Rm, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1317) = {
    SEE = 1317;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) if SEE < 1318) = {
    SEE = 1318;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0010000 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) if SEE < 1319) = {
    SEE = 1319;
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

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) if SEE < 1320) = {
    SEE = 1320;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111000110000111110 @ _ : bits(10) as op_code) if SEE < 1321) = {
    SEE = 1321;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16max_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) if SEE < 1322) = {
    SEE = 1322;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b00001000100 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1323) = {
    SEE = 1323;
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

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) if SEE < 1324) = {
    SEE = 1324;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1325) = {
    SEE = 1325;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) if SEE < 1326) = {
    SEE = 1326;
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

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1327) = {
    SEE = 1327;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b101001 @ _ : bits(10) as op_code) if SEE < 1328) = {
    SEE = 1328;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftlong_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001011110 @ _ : bits(10) as op_code) if SEE < 1329) = {
    SEE = 1329;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_widen_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b011100 @ _ : bits(24) as op_code) if SEE < 1330) = {
    SEE = 1330;
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_simdfp_decode(Rt, imm19, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111000111110 @ _ : bits(10) as op_code) if SEE < 1331) = {
    SEE = 1331;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_fp16_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) if SEE < 1332) = {
    SEE = 1332;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110100 @ _ : bits(10) as op_code) if SEE < 1333) = {
    SEE = 1333;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_disparate_mul_double_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1334) = {
    SEE = 1334;
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

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) if SEE < 1335) = {
    SEE = 1335;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmax_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1336) = {
    SEE = 1336;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp16_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100100010000 @ _ : bits(10) as op_code) if SEE < 1337) = {
    SEE = 1337;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1338) = {
    SEE = 1338;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) if SEE < 1339) = {
    SEE = 1339;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b1010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1340) = {
    SEE = 1340;
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

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b110001000000 @ _ : bits(10) as op_code) if SEE < 1341) = {
    SEE = 1341;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1342) = {
    SEE = 1342;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_int_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1343) = {
    SEE = 1343;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b01011001110 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1344) = {
    SEE = 1344;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b1101011000111111000000 @ _ : bits(5) @ 0b00000 as op_code) if SEE < 1345) = {
    SEE = 1345;
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110011 @ _ : bits(10) as op_code) if SEE < 1346) = {
    SEE = 1346;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    S : bits(1) = [op_code[23]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper_decode(Rd, Rn, Rm, sz, S, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0011010000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1347) = {
    SEE = 1347;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_carry_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode64 ((_ : bits(1) @ 0b00100111 @ _ : bits(1) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1348) = {
    SEE = 1348;
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

function clause decode64 ((0b0011100100 @ _ : bits(22) as op_code) if SEE < 1349) = {
    SEE = 1349;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) if SEE < 1350) = {
    SEE = 1350;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((_ : bits(1) @ 0b010100011 @ _ : bits(22) as op_code) if SEE < 1351) = {
    SEE = 1351;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_postidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b01111000001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1352) = {
    SEE = 1352;
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

function clause decode64 ((0b11010100101 @ _ : bits(16) @ 0b00001 as op_code) if SEE < 1353) = {
    SEE = 1353;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_exception_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1354) = {
    SEE = 1354;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1355) = {
    SEE = 1355;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftinsert_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode64 ((0b1101000110 @ _ : bits(22) as op_code) if SEE < 1356) = {
    SEE = 1356;
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    uimm4 : bits(4) = op_code[13 .. 10];
    op3 : bits(2) = op_code[15 .. 14];
    uimm6 : bits(6) = op_code[21 .. 16];
    integer_tags_mcsubtag_decode(Xd, Xn, uimm4, op3, uimm6)
}

function clause decode64 ((_ : bits(1) @ 0b010100100 @ _ : bits(22) as op_code) if SEE < 1357) = {
    SEE = 1357;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_offset_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100001010000 @ _ : bits(10) as op_code) if SEE < 1358) = {
    SEE = 1358;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1359) = {
    SEE = 1359;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1360) = {
    SEE = 1360;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1361) = {
    SEE = 1361;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_logical_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111001111001100010 @ _ : bits(10) as op_code) if SEE < 1362) = {
    SEE = 1362;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) if SEE < 1363) = {
    SEE = 1363;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1364) = {
    SEE = 1364;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((0b0110100111 @ _ : bits(22) as op_code) if SEE < 1365) = {
    SEE = 1365;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_preidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) if SEE < 1366) = {
    SEE = 1366;
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

function clause decode64 ((0b11010101000000000100 @ _ : bits(4) @ 0b00111111 as op_code) if SEE < 1367) = {
    SEE = 1367;
    CRm : bits(4) = op_code[11 .. 8];
    integer_flags_xaflag_decode(CRm)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111001111001101010 @ _ : bits(10) as op_code) if SEE < 1368) = {
    SEE = 1368;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001100010 @ _ : bits(10) as op_code) if SEE < 1369) = {
    SEE = 1369;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1370) = {
    SEE = 1370;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b01011111 @ _ : bits(8) @ 0b0011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1371) = {
    SEE = 1371;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101101 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1372) = {
    SEE = 1372;
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

function clause decode64 ((0b01111110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1373) = {
    SEE = 1373;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode64 ((0b10011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1374) = {
    SEE = 1374;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1375) = {
    SEE = 1375;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_rounding_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b111101 @ _ : bits(1) @ 0b0 @ _ : bits(22) as op_code) if SEE < 1376) = {
    SEE = 1376;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b001110 @ _ : bits(10) as op_code) if SEE < 1377) = {
    SEE = 1377;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_zip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1378) = {
    SEE = 1378;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1379) = {
    SEE = 1379;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0100111000101000010110 @ _ : bits(10) as op_code) if SEE < 1380) = {
    SEE = 1380;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_round_decode(Rd, Rn, D, size)
}

function clause decode64 ((0b010111100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1381) = {
    SEE = 1381;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_int_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110001 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1382) = {
    SEE = 1382;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b01111000000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1383) = {
    SEE = 1383;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1384) = {
    SEE = 1384;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode64 ((0b0101111001111001101010 @ _ : bits(10) as op_code) if SEE < 1385) = {
    SEE = 1385;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1386) = {
    SEE = 1386;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1387) = {
    SEE = 1387;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111001101010 @ _ : bits(10) as op_code) if SEE < 1388) = {
    SEE = 1388;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1389) = {
    SEE = 1389;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0101011001 @ _ : bits(21) as op_code) if SEE < 1390) = {
    SEE = 1390;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) if SEE < 1391) = {
    SEE = 1391;
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

function clause decode64 ((0b0111111001111001101110 @ _ : bits(10) as op_code) if SEE < 1392) = {
    SEE = 1392;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((_ : bits(1) @ 0b1010001 @ _ : bits(24) as op_code) if SEE < 1393) = {
    SEE = 1393;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    shift : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_addsub_immediate_decode(Rd, Rn, imm12, shift, S, op, sf)
}

function clause decode64 ((0b1 @ _ : bits(2) @ 0b10000 @ _ : bits(24) as op_code) if SEE < 1394) = {
    SEE = 1394;
    Rd : bits(5) = op_code[4 .. 0];
    immhi : bits(19) = op_code[23 .. 5];
    immlo : bits(2) = op_code[30 .. 29];
    op : bits(1) = [op_code[31]];
    integer_arithmetic_address_pcrel_decode(Rd, immhi, immlo, op)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100100110000 @ _ : bits(10) as op_code) if SEE < 1395) = {
    SEE = 1395;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101011000001100 @ _ : bits(12) as op_code) if SEE < 1396) = {
    SEE = 1396;
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

function clause decode64 ((0b10011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1397) = {
    SEE = 1397;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111001111001110010 @ _ : bits(10) as op_code) if SEE < 1398) = {
    SEE = 1398;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((0b00001000000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1399) = {
    SEE = 1399;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100000000000000 @ _ : bits(12) as op_code) if SEE < 1400) = {
    SEE = 1400;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1401) = {
    SEE = 1401;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_recps_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) if SEE < 1402) = {
    SEE = 1402;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(8) @ 0b10000000 @ _ : bits(5) as op_code) if SEE < 1403) = {
    SEE = 1403;
    Rd : bits(5) = op_code[4 .. 0];
    imm5 : bits(5) = op_code[9 .. 5];
    imm8 : bits(8) = op_code[20 .. 13];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_move_fp_imm_decode(Rd, imm5, imm8, typ, S, M)
}

function clause decode64 ((0b0101111001111001110110 @ _ : bits(10) as op_code) if SEE < 1404) = {
    SEE = 1404;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_int_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(5) @ 0b0000 @ _ : bits(12) as op_code) if SEE < 1405) = {
    SEE = 1405;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) if SEE < 1406) = {
    SEE = 1406;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101100 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1407) = {
    SEE = 1407;
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

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011110 @ _ : bits(10) as op_code) if SEE < 1408) = {
    SEE = 1408;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1000 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1409) = {
    SEE = 1409;
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

function clause decode64 ((0b11001110100 @ _ : bits(21) as op_code) if SEE < 1410) = {
    SEE = 1410;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    vector_crypto_sha3_xar_decode(Rd, Rn, imm6, Rm)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000001010 @ _ : bits(10) as op_code) if SEE < 1411) = {
    SEE = 1411;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) if SEE < 1412) = {
    SEE = 1412;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b011110011 @ _ : bits(23) as op_code) if SEE < 1413) = {
    SEE = 1413;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) if SEE < 1414) = {
    SEE = 1414;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_fp_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b00100110 @ _ : bits(23) as op_code) if SEE < 1415) = {
    SEE = 1415;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_bitfield_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1416) = {
    SEE = 1416;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1417) = {
    SEE = 1417;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1418) = {
    SEE = 1418;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode(Rd, Rn, S, Rm, size, U, Q)
}

function clause decode64 ((0b01111000010 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1419) = {
    SEE = 1419;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1420) = {
    SEE = 1420;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_div_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101010000001100 @ _ : bits(12) as op_code) if SEE < 1421) = {
    SEE = 1421;
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

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) if SEE < 1422) = {
    SEE = 1422;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1100 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1423) = {
    SEE = 1423;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) if SEE < 1424) = {
    SEE = 1424;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_long_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b01111110010 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1425) = {
    SEE = 1425;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1426) = {
    SEE = 1426;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_fused_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1427) = {
    SEE = 1427;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110101100000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1428) = {
    SEE = 1428;
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

function clause decode64 ((0b00111000000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1429) = {
    SEE = 1429;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100111 @ _ : bits(10) as op_code) if SEE < 1430) = {
    SEE = 1430;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_product_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1431) = {
    SEE = 1431;
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

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1432) = {
    SEE = 1432;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((_ : bits(1) @ 0b0011010100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1433) = {
    SEE = 1433;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) if SEE < 1434) = {
    SEE = 1434;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftsat_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b101000000000 @ _ : bits(10) as op_code) if SEE < 1435) = {
    SEE = 1435;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b00011001101 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1436) = {
    SEE = 1436;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairandzerodata_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0000 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1437) = {
    SEE = 1437;
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

function clause decode64 ((0b1101101011000000000010 @ _ : bits(10) as op_code) if SEE < 1438) = {
    SEE = 1438;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[11 .. 10];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rev_decode(Rd, Rn, opc, opcode2, S, sf)
}

function clause decode64 ((0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1439) = {
    SEE = 1439;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((_ : bits(2) @ 0b10110010 @ _ : bits(22) as op_code) if SEE < 1440) = {
    SEE = 1440;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110001101010 @ _ : bits(10) as op_code) if SEE < 1441) = {
    SEE = 1441;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b010100110 @ _ : bits(22) as op_code) if SEE < 1442) = {
    SEE = 1442;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_preidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) if SEE < 1443) = {
    SEE = 1443;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmaxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100010000000100 @ _ : bits(12) as op_code) if SEE < 1444) = {
    SEE = 1444;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((0b01011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1445) = {
    SEE = 1445;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b11010101000000110010000010011111 as op_code) if SEE < 1446) = {
    SEE = 1446;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1447) = {
    SEE = 1447;
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

function clause decode64 ((0b00111000011 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1448) = {
    SEE = 1448;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101001 @ _ : bits(10) as op_code) if SEE < 1449) = {
    SEE = 1449;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1450) = {
    SEE = 1450;
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

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) if SEE < 1451) = {
    SEE = 1451;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101100 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1452) = {
    SEE = 1452;
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

function clause decode64 ((0b0111111001111001110110 @ _ : bits(10) as op_code) if SEE < 1453) = {
    SEE = 1453;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_int_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1454) = {
    SEE = 1454;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_rsqrts_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1455) = {
    SEE = 1455;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtest_float_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b1011010100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1456) = {
    SEE = 1456;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111000110010 @ _ : bits(10) as op_code) if SEE < 1457) = {
    SEE = 1457;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_fp16_bulk_simd_decode(Rd, Rn, op, a, U, Q)
}

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1458) = {
    SEE = 1458;
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

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b0 @ _ : bits(1) @ 0b000 as op_code) if SEE < 1459) = {
    SEE = 1459;
    opc : bits(2) = op_code[4 .. 3];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[15 .. 14];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_compare_uncond_decode(opc, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b001010 @ _ : bits(10) as op_code) if SEE < 1460) = {
    SEE = 1460;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_transpose_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0110110 @ _ : bits(24) as op_code) if SEE < 1461) = {
    SEE = 1461;
    Rt : bits(5) = op_code[4 .. 0];
    imm14 : bits(14) = op_code[18 .. 5];
    b40 : bits(5) = op_code[23 .. 19];
    op : bits(1) = [op_code[24]];
    b5 : bits(1) = [op_code[31]];
    branch_conditional_test_decode(Rt, imm14, b40, op, b5)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1462) = {
    SEE = 1462;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1463) = {
    SEE = 1463;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1464) = {
    SEE = 1464;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1465) = {
    SEE = 1465;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110100000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1466) = {
    SEE = 1466;
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

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) if SEE < 1467) = {
    SEE = 1467;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1sched0_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1468) = {
    SEE = 1468;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((0b0101111100 @ _ : bits(6) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1469) = {
    SEE = 1469;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b010110 @ _ : bits(10) as op_code) if SEE < 1470) = {
    SEE = 1470;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_permute_unzip_decode(Rd, Rn, op, Rm, size, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111001111001100110 @ _ : bits(10) as op_code) if SEE < 1471) = {
    SEE = 1471;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(5) @ 0b1110 @ _ : bits(12) as op_code) if SEE < 1472) = {
    SEE = 1472;
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

function clause decode64 ((0b10011011110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1473) = {
    SEE = 1473;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111100 @ _ : bits(6) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1474) = {
    SEE = 1474;
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

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1475) = {
    SEE = 1475;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110101 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1476) = {
    SEE = 1476;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1477) = {
    SEE = 1477;
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

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) if SEE < 1478) = {
    SEE = 1478;
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

function clause decode64 ((0b1101010100000010001001 @ _ : bits(10) as op_code) if SEE < 1479) = {
    SEE = 1479;
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    integer_tags_mcgettagarray_decode(Xt, Xn)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) if SEE < 1480) = {
    SEE = 1480;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_narrow_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) if SEE < 1481) = {
    SEE = 1481;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_recip_int_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000000 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1482) = {
    SEE = 1482;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1483) = {
    SEE = 1483;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1484) = {
    SEE = 1484;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp16_extended_simd_decode(Rd, Rn, opcode, Rm, a, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b111000000000 @ _ : bits(10) as op_code) if SEE < 1485) = {
    SEE = 1485;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((_ : bits(1) @ 0b10100101 @ _ : bits(23) as op_code) if SEE < 1486) = {
    SEE = 1486;
    Rd : bits(5) = op_code[4 .. 0];
    imm16 : bits(16) = op_code[20 .. 5];
    hw : bits(2) = op_code[22 .. 21];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_insext_insert_movewide_decode(Rd, imm16, hw, opc, sf)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1487) = {
    SEE = 1487;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_int_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001111110 @ _ : bits(10) as op_code) if SEE < 1488) = {
    SEE = 1488;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrt_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) if SEE < 1489) = {
    SEE = 1489;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(5) @ 0b1100 @ _ : bits(12) as op_code) if SEE < 1490) = {
    SEE = 1490;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1491) = {
    SEE = 1491;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1492) = {
    SEE = 1492;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_int_simd_decode(Rd, Rn, eq, Rm, size, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100110010000 @ _ : bits(10) as op_code) if SEE < 1493) = {
    SEE = 1493;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1494) = {
    SEE = 1494;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1495) = {
    SEE = 1495;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_float_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) if SEE < 1496) = {
    SEE = 1496;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_diff_decode(Rd, Rn, op, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) if SEE < 1497) = {
    SEE = 1497;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b01010100 @ _ : bits(19) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1498) = {
    SEE = 1498;
    cond : bits(4) = op_code[3 .. 0];
    o0 : bits(1) = [op_code[4]];
    imm19 : bits(19) = op_code[23 .. 5];
    o1 : bits(1) = [op_code[24]];
    branch_conditional_cond_decode(cond, o0, imm19, o1)
}

function clause decode64 ((0b0101111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1499) = {
    SEE = 1499;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b011001 @ _ : bits(10) as op_code) if SEE < 1500) = {
    SEE = 1500;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftsat_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b11 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1501) = {
    SEE = 1501;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(5) @ 0b1000 @ _ : bits(12) as op_code) if SEE < 1502) = {
    SEE = 1502;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b01001110000 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1503) = {
    SEE = 1503;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_integer_insert_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1504) = {
    SEE = 1504;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) if SEE < 1505) = {
    SEE = 1505;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmax_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1506) = {
    SEE = 1506;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((_ : bits(2) @ 0b10110001 @ _ : bits(22) as op_code) if SEE < 1507) = {
    SEE = 1507;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b001110001 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1508) = {
    SEE = 1508;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b0 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1509) = {
    SEE = 1509;
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

function clause decode64 ((0b00011111 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1510) = {
    SEE = 1510;
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

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1511) = {
    SEE = 1511;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b00 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1512) = {
    SEE = 1512;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) if SEE < 1513) = {
    SEE = 1513;
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

function clause decode64 ((0b10111000100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1514) = {
    SEE = 1514;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b01111000000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1515) = {
    SEE = 1515;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000010 @ _ : bits(10) as op_code) if SEE < 1516) = {
    SEE = 1516;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_product_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b1101010100000011001000 @ _ : bits(1) @ 0b100 @ _ : bits(1) @ 0b11111 as op_code) if SEE < 1517) = {
    SEE = 1517;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_pacia_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b110000000000 @ _ : bits(10) as op_code) if SEE < 1518) = {
    SEE = 1518;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000011 @ _ : bits(10) as op_code) if SEE < 1519) = {
    SEE = 1519;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_saturating_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(5) @ 0b1 @ _ : bits(1) @ 0b000 as op_code) if SEE < 1520) = {
    SEE = 1520;
    opc : bits(2) = op_code[4 .. 3];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[15 .. 14];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_compare_uncond_decode(opc, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) if SEE < 1521) = {
    SEE = 1521;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b1101011001011111000000 @ _ : bits(5) @ 0b00000 as op_code) if SEE < 1522) = {
    SEE = 1522;
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b10001 @ _ : bits(2) @ 0b10000 @ _ : bits(10) as op_code) if SEE < 1523) = {
    SEE = 1523;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_convert_fp_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000010 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1524) = {
    SEE = 1524;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000010010 @ _ : bits(10) as op_code) if SEE < 1525) = {
    SEE = 1525;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_clsz_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b00011001001 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1526) = {
    SEE = 1526;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairpost_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b00111000000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1527) = {
    SEE = 1527;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b001 @ _ : bits(10) as op_code) if SEE < 1528) = {
    SEE = 1528;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacib_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b10 @ _ : bits(1) @ 0b11 @ _ : bits(1) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1529) = {
    SEE = 1529;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b11100101 @ _ : bits(22) as op_code) if SEE < 1530) = {
    SEE = 1530;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1531) = {
    SEE = 1531;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1532) = {
    SEE = 1532;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000100 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1533) = {
    SEE = 1533;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1534) = {
    SEE = 1534;
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

function clause decode64 ((0b11011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1535) = {
    SEE = 1535;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1536) = {
    SEE = 1536;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) if SEE < 1537) = {
    SEE = 1537;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) if SEE < 1538) = {
    SEE = 1538;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b00111000010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1539) = {
    SEE = 1539;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b0 @ _ : bits(2) @ 0b000 @ _ : bits(10) as op_code) if SEE < 1540) = {
    SEE = 1540;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    len : bits(2) = op_code[14 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    op2 : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_table_decode(Rd, Rn, op, len, Rm, op2, Q)
}

function clause decode64 ((_ : bits(1) @ 0b00100101 @ _ : bits(23) as op_code) if SEE < 1541) = {
    SEE = 1541;
    Rd : bits(5) = op_code[4 .. 0];
    imm16 : bits(16) = op_code[20 .. 5];
    hw : bits(2) = op_code[22 .. 21];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_insext_insert_movewide_decode(Rd, imm16, hw, opc, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) if SEE < 1542) = {
    SEE = 1542;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110110 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1543) = {
    SEE = 1543;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode64 ((0b11010100101 @ _ : bits(16) @ 0b00010 as op_code) if SEE < 1544) = {
    SEE = 1544;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_exception_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101100 @ _ : bits(10) as op_code) if SEE < 1545) = {
    SEE = 1545;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode(Rd, Rn, o1, Rm, size, U)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1546) = {
    SEE = 1546;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1547) = {
    SEE = 1547;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001001010 @ _ : bits(10) as op_code) if SEE < 1548) = {
    SEE = 1548;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_sqxtun_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b00111000101 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) if SEE < 1549) = {
    SEE = 1549;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1550) = {
    SEE = 1550;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_nonuniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) if SEE < 1551) = {
    SEE = 1551;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111001100000010110 @ _ : bits(10) as op_code) if SEE < 1552) = {
    SEE = 1552;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rbit_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) if SEE < 1553) = {
    SEE = 1553;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) if SEE < 1554) = {
    SEE = 1554;
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

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1555) = {
    SEE = 1555;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1hash_choose_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111001110110 @ _ : bits(10) as op_code) if SEE < 1556) = {
    SEE = 1556;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtest_fp16_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((0b11010100000 @ _ : bits(16) @ 0b00010 as op_code) if SEE < 1557) = {
    SEE = 1557;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_runtime_hvc_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110011 @ _ : bits(10) as op_code) if SEE < 1558) = {
    SEE = 1558;
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

function clause decode64 ((0b00011001000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1559) = {
    SEE = 1559;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettag_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) if SEE < 1560) = {
    SEE = 1560;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_extract_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b10011010110 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1561) = {
    SEE = 1561;
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_arithmetic_pointer_mcsubtracttaggedaddress_decode(Xd, Xn, Xm)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0 @ _ : bits(2) @ 0b1 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1562) = {
    SEE = 1562;
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

function clause decode64 ((0b0101111011111001101110 @ _ : bits(10) as op_code) if SEE < 1563) = {
    SEE = 1563;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100100 @ _ : bits(10) as op_code) if SEE < 1564) = {
    SEE = 1564;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_dmacc_simd_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011111 @ _ : bits(7) @ 0b1 @ _ : bits(1) @ 0b00 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1565) = {
    SEE = 1565;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) if SEE < 1566) = {
    SEE = 1566;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110001 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1567) = {
    SEE = 1567;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1568) = {
    SEE = 1568;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b00 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1569) = {
    SEE = 1569;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_offset_normal_memory_single_simdfp_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b01111000010 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1570) = {
    SEE = 1570;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) if SEE < 1571) = {
    SEE = 1571;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101011 @ _ : bits(10) as op_code) if SEE < 1572) = {
    SEE = 1572;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_pair_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001100010 @ _ : bits(10) as op_code) if SEE < 1573) = {
    SEE = 1573;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110000001110 @ _ : bits(10) as op_code) if SEE < 1574) = {
    SEE = 1574;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_addlong_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111001111110 @ _ : bits(10) as op_code) if SEE < 1575) = {
    SEE = 1575;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_sqrtfp16_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000001010 @ _ : bits(10) as op_code) if SEE < 1576) = {
    SEE = 1576;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[14]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_pairwise_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1577) = {
    SEE = 1577;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_int_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111001110110 @ _ : bits(10) as op_code) if SEE < 1578) = {
    SEE = 1578;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_recip_fp16_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b10100100 @ _ : bits(23) as op_code) if SEE < 1579) = {
    SEE = 1579;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode64 ((0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1580) = {
    SEE = 1580;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) if SEE < 1581) = {
    SEE = 1581;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_bulk_sisd_decode(Rd, Rn, op, size, U)
}

function clause decode64 ((_ : bits(2) @ 0b10110011 @ _ : bits(22) as op_code) if SEE < 1582) = {
    SEE = 1582;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011001 @ _ : bits(10) as op_code) if SEE < 1583) = {
    SEE = 1583;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010100 @ _ : bits(10) as op_code) if SEE < 1584) = {
    SEE = 1584;
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

function clause decode64 ((0b00011001100 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1585) = {
    SEE = 1585;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagandzerodata_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) if SEE < 1586) = {
    SEE = 1586;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1587) = {
    SEE = 1587;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1588) = {
    SEE = 1588;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) if SEE < 1589) = {
    SEE = 1589;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_wide_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b110000111110 @ _ : bits(10) as op_code) if SEE < 1590) = {
    SEE = 1590;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmax_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100111 @ _ : bits(10) as op_code) if SEE < 1591) = {
    SEE = 1591;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_product_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011111 @ _ : bits(10) as op_code) if SEE < 1592) = {
    SEE = 1592;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111011111001100110 @ _ : bits(10) as op_code) if SEE < 1593) = {
    SEE = 1593;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b11010101000000110010 @ _ : bits(7) @ 0b11111 as op_code) if SEE < 1594) = {
    SEE = 1594;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110101000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1595) = {
    SEE = 1595;
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

function clause decode64 ((0b010010001 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) if SEE < 1596) = {
    SEE = 1596;
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

function clause decode64 ((0b100101 @ _ : bits(26) as op_code) if SEE < 1597) = {
    SEE = 1597;
    imm26 : bits(26) = op_code[25 .. 0];
    op : bits(1) = [op_code[31]];
    branch_unconditional_immediate_decode(imm26, op)
}

function clause decode64 ((0b01111000010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1598) = {
    SEE = 1598;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001011010 @ _ : bits(10) as op_code) if SEE < 1599) = {
    SEE = 1599;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_xtn_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b000 @ _ : bits(10) as op_code) if SEE < 1600) = {
    SEE = 1600;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacia_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) if SEE < 1601) = {
    SEE = 1601;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_bulk_simd_decode(Rd, Rn, op, sz, U, Q)
}

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) if SEE < 1602) = {
    SEE = 1602;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[14 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha3op_sha1hash_parity_decode(Rd, Rn, opcode, Rm, size)
}

function clause decode64 ((0b0101111000101000001010 @ _ : bits(10) as op_code) if SEE < 1603) = {
    SEE = 1603;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha2op_sha256sched0_decode(Rd, Rn, opcode, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b1111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1604) = {
    SEE = 1604;
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

function clause decode64 ((0b1101010100000010001000 @ _ : bits(10) as op_code) if SEE < 1605) = {
    SEE = 1605;
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    integer_tags_mcsettagarray_decode(Xt, Xn)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b100000101010 @ _ : bits(10) as op_code) if SEE < 1606) = {
    SEE = 1606;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_int_lessthan_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1607) = {
    SEE = 1607;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100010000000000 @ _ : bits(12) as op_code) if SEE < 1608) = {
    SEE = 1608;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1609) = {
    SEE = 1609;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_conv_float_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode64 ((0b11010101000000000100 @ _ : bits(4) @ 0b01011111 as op_code) if SEE < 1610) = {
    SEE = 1610;
    CRm : bits(4) = op_code[11 .. 8];
    integer_flags_axflag_decode(CRm)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011001 @ _ : bits(10) as op_code) if SEE < 1611) = {
    SEE = 1611;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100101 @ _ : bits(10) as op_code) if SEE < 1612) = {
    SEE = 1612;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_accum_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100010000000 @ _ : bits(10) as op_code) if SEE < 1613) = {
    SEE = 1613;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((_ : bits(1) @ 0b00100100 @ _ : bits(23) as op_code) if SEE < 1614) = {
    SEE = 1614;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) if SEE < 1615) = {
    SEE = 1615;
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

function clause decode64 ((_ : bits(1) @ 0b1111010010 @ _ : bits(9) @ 0b10 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1616) = {
    SEE = 1616;
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

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b100000111010 @ _ : bits(10) as op_code) if SEE < 1617) = {
    SEE = 1617;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_lessthan_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000100 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1618) = {
    SEE = 1618;
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

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b111001000000 @ _ : bits(10) as op_code) if SEE < 1619) = {
    SEE = 1619;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1620) = {
    SEE = 1620;
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

function clause decode64 ((0b11010101000000110010001000111111 as op_code) if SEE < 1621) = {
    SEE = 1621;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b1101010100101 @ _ : bits(19) as op_code) if SEE < 1622) = {
    SEE = 1622;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_sysops_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1623) = {
    SEE = 1623;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b100111 @ _ : bits(10) as op_code) if SEE < 1624) = {
    SEE = 1624;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b00011001100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1625) = {
    SEE = 1625;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100010 @ _ : bits(10) as op_code) if SEE < 1626) = {
    SEE = 1626;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[15]];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_mul_product_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) if SEE < 1627) = {
    SEE = 1627;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_add_saturating_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1628) = {
    SEE = 1628;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b111000 @ _ : bits(10) as op_code) if SEE < 1629) = {
    SEE = 1629;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_poly_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100111010000 @ _ : bits(10) as op_code) if SEE < 1630) = {
    SEE = 1630;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110000000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1631) = {
    SEE = 1631;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((0b11111000 @ _ : bits(2) @ 0b1 @ _ : bits(10) @ 0b1 @ _ : bits(10) as op_code) if SEE < 1632) = {
    SEE = 1632;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1633) = {
    SEE = 1633;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1634) = {
    SEE = 1634;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) if SEE < 1635) = {
    SEE = 1635;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((0b1101010100001 @ _ : bits(19) as op_code) if SEE < 1636) = {
    SEE = 1636;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_sysops_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b1101011000011111000000 @ _ : bits(5) @ 0b00000 as op_code) if SEE < 1637) = {
    SEE = 1637;
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) if SEE < 1638) = {
    SEE = 1638;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b01011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1639) = {
    SEE = 1639;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) if SEE < 1640) = {
    SEE = 1640;
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

function clause decode64 ((0b0101111011111001101010 @ _ : bits(10) as op_code) if SEE < 1641) = {
    SEE = 1641;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((_ : bits(1) @ 0b101101011000000000000 @ _ : bits(10) as op_code) if SEE < 1642) = {
    SEE = 1642;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rbit_decode(Rd, Rn, opcode2, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) if SEE < 1643) = {
    SEE = 1643;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_fp_product_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) if SEE < 1644) = {
    SEE = 1644;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1645) = {
    SEE = 1645;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b1101011 @ _ : bits(1) @ 0b0011111100001 @ _ : bits(11) as op_code) if SEE < 1646) = {
    SEE = 1646;
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1647) = {
    SEE = 1647;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_leftinsert_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b011111111 @ _ : bits(7) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1648) = {
    SEE = 1648;
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

function clause decode64 ((0b01011110010 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1649) = {
    SEE = 1649;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_recpsfp16_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) if SEE < 1650) = {
    SEE = 1650;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightnarrow_uniform_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b1101010100000011001000 @ _ : bits(1) @ 0b101 @ _ : bits(1) @ 0b11111 as op_code) if SEE < 1651) = {
    SEE = 1651;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_pacib_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1652) = {
    SEE = 1652;
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

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010110 @ _ : bits(10) as op_code) if SEE < 1653) = {
    SEE = 1653;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000011110 @ _ : bits(10) as op_code) if SEE < 1654) = {
    SEE = 1654;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_sat_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b11010100010 @ _ : bits(16) @ 0b00000 as op_code) if SEE < 1655) = {
    SEE = 1655;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_halt_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b11010101000000110010000000111111 as op_code) if SEE < 1656) = {
    SEE = 1656;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1657) = {
    SEE = 1657;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b11100100 @ _ : bits(23) as op_code) if SEE < 1658) = {
    SEE = 1658;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_immediate_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1659) = {
    SEE = 1659;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_nonuniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b10 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1660) = {
    SEE = 1660;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_preidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) if SEE < 1661) = {
    SEE = 1661;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1662) = {
    SEE = 1662;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) if SEE < 1663) = {
    SEE = 1663;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) if SEE < 1664) = {
    SEE = 1664;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_addsub_narrow_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1665) = {
    SEE = 1665;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_recps_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b11011001000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1666) = {
    SEE = 1666;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((_ : bits(1) @ 0b1101010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1667) = {
    SEE = 1667;
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

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b01 @ _ : bits(5) @ 0b1 @ _ : bits(4) as op_code) if SEE < 1668) = {
    SEE = 1668;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011100 @ _ : bits(10) as op_code) if SEE < 1669) = {
    SEE = 1669;
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

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1670) = {
    SEE = 1670;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_left_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) if SEE < 1671) = {
    SEE = 1671;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b100001111110 @ _ : bits(10) as op_code) if SEE < 1672) = {
    SEE = 1672;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_frecpx_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) if SEE < 1673) = {
    SEE = 1673;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b0011100101 @ _ : bits(22) as op_code) if SEE < 1674) = {
    SEE = 1674;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0100 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1675) = {
    SEE = 1675;
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

function clause decode64 ((0b0111111001111001110010 @ _ : bits(10) as op_code) if SEE < 1676) = {
    SEE = 1676;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size_1_ : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, size_1_, U)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000011 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1677) = {
    SEE = 1677;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1678) = {
    SEE = 1678;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110100100000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1679) = {
    SEE = 1679;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1680) = {
    SEE = 1680;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode64 ((0b11010101000000000100000000011111 as op_code) if SEE < 1681) = {
    SEE = 1681;
    CRm : bits(4) = op_code[11 .. 8];
    integer_flags_cfinv_decode(CRm)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b110000110110 @ _ : bits(10) as op_code) if SEE < 1682) = {
    SEE = 1682;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpadd_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b00111000010 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1683) = {
    SEE = 1683;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011011 @ _ : bits(10) as op_code) if SEE < 1684) = {
    SEE = 1684;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b10011010110 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) if SEE < 1685) = {
    SEE = 1685;
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_tags_mcinsertrandomtag_decode(Xd, Xn, Xm)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111001111001110110 @ _ : bits(10) as op_code) if SEE < 1686) = {
    SEE = 1686;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_int_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b0001011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1687) = {
    SEE = 1687;
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

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011010 @ _ : bits(10) as op_code) if SEE < 1688) = {
    SEE = 1688;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[13 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_maxmin_decode(Rd, Rn, op, Rm, typ, S, M)
}

function clause decode64 ((_ : bits(1) @ 0b1011010100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1689) = {
    SEE = 1689;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111010110000110010 @ _ : bits(10) as op_code) if SEE < 1690) = {
    SEE = 1690;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fp16maxnm_simd_decode(Rd, Rn, opcode, o1, U, Q)
}

function clause decode64 ((0b10011010110 @ _ : bits(5) @ 0b001100 @ _ : bits(10) as op_code) if SEE < 1691) = {
    SEE = 1691;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    op : bits(1) = [op_code[30]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacga_dp_2src_decode(Rd, Rn, opcode2, Rm, S, op, sf)
}

function clause decode64 ((0b0 @ _ : bits(2) @ 0b0111100000 @ _ : bits(3) @ 0b111101 @ _ : bits(10) as op_code) if SEE < 1692) = {
    SEE = 1692;
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

function clause decode64 ((0b00011001001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1693) = {
    SEE = 1693;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpair_decode(Rt, Xn, imm9)
}

function clause decode64 ((_ : bits(1) @ 0b01100110 @ _ : bits(23) as op_code) if SEE < 1694) = {
    SEE = 1694;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_bitfield_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b0101 @ _ : bits(12) as op_code) if SEE < 1695) = {
    SEE = 1695;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111100000 @ _ : bits(7) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1696) = {
    SEE = 1696;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111001111001101110 @ _ : bits(10) as op_code) if SEE < 1697) = {
    SEE = 1697;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b1101010100000011001000 @ _ : bits(1) @ 0b110 @ _ : bits(1) @ 0b11111 as op_code) if SEE < 1698) = {
    SEE = 1698;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_autia_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1699) = {
    SEE = 1699;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_sub_int_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) if SEE < 1700) = {
    SEE = 1700;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_tieaway_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0111111011111000110110 @ _ : bits(10) as op_code) if SEE < 1701) = {
    SEE = 1701;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode64 ((0b0111111011111000110010 @ _ : bits(10) as op_code) if SEE < 1702) = {
    SEE = 1702;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode64 ((_ : bits(1) @ 0b0111010000 @ _ : bits(6) @ 0b00001 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1703) = {
    SEE = 1703;
    mask : bits(4) = op_code[3 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[20 .. 15];
    sf : bits(1) = [op_code[31]];
    integer_flags_rmif_decode(mask, Rn, imm6, sf)
}

function clause decode64 ((0b11010100000 @ _ : bits(16) @ 0b00001 as op_code) if SEE < 1704) = {
    SEE = 1704;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_runtime_svc_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) if SEE < 1705) = {
    SEE = 1705;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b100000001110 @ _ : bits(10) as op_code) if SEE < 1706) = {
    SEE = 1706;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_add_saturating_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b11001110100 @ _ : bits(21) as op_code) if SEE < 1707) = {
    SEE = 1707;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    vector_crypto_sha3_xar_decode(Rd, Rn, imm6, Rm)
}

function clause decode64 ((0b0 @ _ : bits(2) @ 0b10000 @ _ : bits(24) as op_code) if SEE < 1708) = {
    SEE = 1708;
    Rd : bits(5) = op_code[4 .. 0];
    immhi : bits(19) = op_code[23 .. 5];
    immlo : bits(2) = op_code[30 .. 29];
    op : bits(1) = [op_code[31]];
    integer_arithmetic_address_pcrel_decode(Rd, immhi, immlo, op)
}

function clause decode64 ((0b110101101001111100001 @ _ : bits(1) @ 0b1111111111 as op_code) if SEE < 1709) = {
    SEE = 1709;
    op4 : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    branch_unconditional_eret_decode(op4, Rn, M, A, op2)
}

function clause decode64 ((0b01001000000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1710) = {
    SEE = 1710;
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

function clause decode64 ((0b01111000101 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) if SEE < 1711) = {
    SEE = 1711;
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

function clause decode64 ((_ : bits(1) @ 0b010100001 @ _ : bits(22) as op_code) if SEE < 1712) = {
    SEE = 1712;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_noalloc_memory_pair_general_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100101110000 @ _ : bits(10) as op_code) if SEE < 1713) = {
    SEE = 1713;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110001101110 @ _ : bits(10) as op_code) if SEE < 1714) = {
    SEE = 1714;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_add_simd_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0101111011111000110110 @ _ : bits(10) as op_code) if SEE < 1715) = {
    SEE = 1715;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode(Rd, Rn, op, a, U)
}

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000100 @ _ : bits(10) as op_code) if SEE < 1716) = {
    SEE = 1716;
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

function clause decode64 ((0b00111000001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1717) = {
    SEE = 1717;
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

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) if SEE < 1718) = {
    SEE = 1718;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_int_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b01111110110 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1719) = {
    SEE = 1719;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_fp16_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode64 ((0b0100111000101000011110 @ _ : bits(10) as op_code) if SEE < 1720) = {
    SEE = 1720;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_aes_mix_decode(Rd, Rn, D, size)
}

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100000 @ _ : bits(10) as op_code) if SEE < 1721) = {
    SEE = 1721;
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

function clause decode64 ((_ : bits(1) @ 0b0111010010 @ _ : bits(9) @ 0b00 @ _ : bits(5) @ 0b0 @ _ : bits(4) as op_code) if SEE < 1722) = {
    SEE = 1722;
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

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) if SEE < 1723) = {
    SEE = 1723;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101111 @ _ : bits(8) @ 0b0110 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1724) = {
    SEE = 1724;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110011 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1725) = {
    SEE = 1725;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    opc2 : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_bsleor_decode(Rd, Rn, opcode, Rm, opc2, U, Q)
}

function clause decode64 ((0b11010110100111110000001111100000 as op_code) if SEE < 1726) = {
    SEE = 1726;
    op4 : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    branch_unconditional_eret_decode(op4, Rn, M, A, op2)
}

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1727) = {
    SEE = 1727;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100101 @ _ : bits(10) as op_code) if SEE < 1728) = {
    SEE = 1728;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_accum_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1729) = {
    SEE = 1729;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100111110000 @ _ : bits(10) as op_code) if SEE < 1730) = {
    SEE = 1730;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b110000101010 @ _ : bits(10) as op_code) if SEE < 1731) = {
    SEE = 1731;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[16]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_intmax_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b10011011101 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1732) = {
    SEE = 1732;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110100000000 @ _ : bits(2) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1733) = {
    SEE = 1733;
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

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100101000000 @ _ : bits(10) as op_code) if SEE < 1734) = {
    SEE = 1734;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) if SEE < 1735) = {
    SEE = 1735;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmaxnm_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b10 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1736) = {
    SEE = 1736;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b0111 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1737) = {
    SEE = 1737;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) if SEE < 1738) = {
    SEE = 1738;
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

function clause decode64 ((0b010111100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1739) = {
    SEE = 1739;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((0b0101111000110000111110 @ _ : bits(10) as op_code) if SEE < 1740) = {
    SEE = 1740;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16max_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) if SEE < 1741) = {
    SEE = 1741;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100000010000 @ _ : bits(10) as op_code) if SEE < 1742) = {
    SEE = 1742;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_unary_decode(Rd, Rn, opc, typ, S, M)
}

function clause decode64 ((0b01011001100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1743) = {
    SEE = 1743;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((_ : bits(1) @ 0b0111010000000000 @ _ : bits(1) @ 0b0010 @ _ : bits(5) @ 0b01101 as op_code) if SEE < 1744) = {
    SEE = 1744;
    mask : bits(4) = op_code[3 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode2 : bits(4) = op_code[13 .. 10];
    sz : bits(1) = [op_code[14]];
    imm6 : bits(6) = op_code[20 .. 15];
    sf : bits(1) = [op_code[31]];
    integer_flags_setf_decode(mask, Rn, opcode2, sz, imm6, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1745) = {
    SEE = 1745;
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

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100000000000 @ _ : bits(10) as op_code) if SEE < 1746) = {
    SEE = 1746;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b11010100001 @ _ : bits(16) @ 0b00000 as op_code) if SEE < 1747) = {
    SEE = 1747;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_breakpoint_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b010001 @ _ : bits(10) as op_code) if SEE < 1748) = {
    SEE = 1748;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_rightinsert_sisd_decode(Rd, Rn, opcode, immb, immh, U)
}

function clause decode64 ((0b11111000100 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1749) = {
    SEE = 1749;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100001000000 @ _ : bits(10) as op_code) if SEE < 1750) = {
    SEE = 1750;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1751) = {
    SEE = 1751;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_logical_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b010 @ _ : bits(10) as op_code) if SEE < 1752) = {
    SEE = 1752;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacda_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1753) = {
    SEE = 1753;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_special_recip_float_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011101 @ _ : bits(10) as op_code) if SEE < 1754) = {
    SEE = 1754;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_diff_decode(Rd, Rn, ac, Rm, size, U, Q)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b110001101110 @ _ : bits(10) as op_code) if SEE < 1755) = {
    SEE = 1755;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_reduce_add_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b01111000000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1756) = {
    SEE = 1756;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010111 @ _ : bits(10) as op_code) if SEE < 1757) = {
    SEE = 1757;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1758) = {
    SEE = 1758;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111101 @ _ : bits(10) as op_code) if SEE < 1759) = {
    SEE = 1759;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100011 @ _ : bits(10) as op_code) if SEE < 1760) = {
    SEE = 1760;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode(Rd, Rn, S, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(5) @ 0b1100 @ _ : bits(12) as op_code) if SEE < 1761) = {
    SEE = 1761;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011011 @ _ : bits(10) as op_code) if SEE < 1762) = {
    SEE = 1762;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_single_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000100010 @ _ : bits(10) as op_code) if SEE < 1763) = {
    SEE = 1763;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b00011001000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1764) = {
    SEE = 1764;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpost_decode(Rt, Xn, imm9)
}

function clause decode64 ((_ : bits(1) @ 0b10110101100000000001 @ _ : bits(11) as op_code) if SEE < 1765) = {
    SEE = 1765;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[11 .. 10];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rev_decode(Rd, Rn, opc, opcode2, S, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100000100110 @ _ : bits(10) as op_code) if SEE < 1766) = {
    SEE = 1766;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_int_bulk_simd_decode(Rd, Rn, op, size, U, Q)
}

function clause decode64 ((0b001110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1767) = {
    SEE = 1767;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111001100110 @ _ : bits(10) as op_code) if SEE < 1768) = {
    SEE = 1768;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((_ : bits(1) @ 0b10100110 @ _ : bits(23) as op_code) if SEE < 1769) = {
    SEE = 1769;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imms : bits(6) = op_code[15 .. 10];
    immr : bits(6) = op_code[21 .. 16];
    N : bits(1) = [op_code[22]];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_bitfield_decode(Rd, Rn, imms, immr, N, opc, sf)
}

function clause decode64 ((0b01101110000 @ _ : bits(5) @ 0b0 @ _ : bits(4) @ 0b1 @ _ : bits(10) as op_code) if SEE < 1770) = {
    SEE = 1770;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_insert_decode(Rd, Rn, imm4, imm5, op, Q)
}

function clause decode64 ((0b110101100101111100001 @ _ : bits(1) @ 0b1111111111 as op_code) if SEE < 1771) = {
    SEE = 1771;
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100110 @ _ : bits(5) @ 0b0100 @ _ : bits(12) as op_code) if SEE < 1772) = {
    SEE = 1772;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000000 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1773) = {
    SEE = 1773;
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

function clause decode64 ((0b01111110110 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1774) = {
    SEE = 1774;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode(Rd, Rn, ac, Rm, E, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) if SEE < 1775) = {
    SEE = 1775;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_fp_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b00011111 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1776) = {
    SEE = 1776;
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

function clause decode64 ((0b0111100100 @ _ : bits(22) as op_code) if SEE < 1777) = {
    SEE = 1777;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1778) = {
    SEE = 1778;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode64 ((0b0101111000110000110010 @ _ : bits(10) as op_code) if SEE < 1779) = {
    SEE = 1779;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16maxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b110110101100000101000 @ _ : bits(1) @ 0b11111 @ _ : bits(5) as op_code) if SEE < 1780) = {
    SEE = 1780;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    D : bits(1) = [op_code[10]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_strip_dp_1src_decode(Rd, Rn, D, opcode2, S, sf)
}

function clause decode64 ((_ : bits(2) @ 0b111100 @ _ : bits(1) @ 0b00 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1781) = {
    SEE = 1781;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_signed_preidx_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1782) = {
    SEE = 1782;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_int_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1783) = {
    SEE = 1783;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_int_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b011 @ _ : bits(10) as op_code) if SEE < 1784) = {
    SEE = 1784;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_pacdb_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((0b00011001100 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1785) = {
    SEE = 1785;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagandzerodatapost_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100000000001000 @ _ : bits(12) as op_code) if SEE < 1786) = {
    SEE = 1786;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) if SEE < 1787) = {
    SEE = 1787;
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

function clause decode64 ((_ : bits(1) @ 0b1001010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1788) = {
    SEE = 1788;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1789) = {
    SEE = 1789;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000110 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1790) = {
    SEE = 1790;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110000 @ _ : bits(5) @ 0b0 @ _ : bits(2) @ 0b100 @ _ : bits(10) as op_code) if SEE < 1791) = {
    SEE = 1791;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    len : bits(2) = op_code[14 .. 13];
    Rm : bits(5) = op_code[20 .. 16];
    op2 : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_table_decode(Rd, Rn, op, len, Rm, op2, Q)
}

function clause decode64 ((0b10111010110 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1792) = {
    SEE = 1792;
    Xd : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xm : bits(5) = op_code[20 .. 16];
    integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags_decode(Xd, Xn, Xm)
}

function clause decode64 ((0b01011110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1793) = {
    SEE = 1793;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1794) = {
    SEE = 1794;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b100001010010 @ _ : bits(10) as op_code) if SEE < 1795) = {
    SEE = 1795;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_extract_sat_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010101 @ _ : bits(10) as op_code) if SEE < 1796) = {
    SEE = 1796;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    R : bits(1) = [op_code[12]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_shift_sisd_decode(Rd, Rn, S, R, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000010010 @ _ : bits(10) as op_code) if SEE < 1797) = {
    SEE = 1797;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_clsz_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b100000101110 @ _ : bits(10) as op_code) if SEE < 1798) = {
    SEE = 1798;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_diffneg_int_sisd_decode(Rd, Rn, opcode, size, U)
}

function clause decode64 ((0b11010101000000110010000001111111 as op_code) if SEE < 1799) = {
    SEE = 1799;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_hints_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b110101010011 @ _ : bits(20) as op_code) if SEE < 1800) = {
    SEE = 1800;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    o0 : bits(1) = [op_code[19]];
    L : bits(1) = [op_code[21]];
    system_register_system_decode(Rt, op2, CRm, CRn, op1, o0, L)
}

function clause decode64 ((0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111001 @ _ : bits(10) as op_code) if SEE < 1801) = {
    SEE = 1801;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_fp_sisd_decode(Rd, Rn, ac, Rm, sz, E, U)
}

function clause decode64 ((_ : bits(1) @ 0b101101011000000000001 @ _ : bits(10) as op_code) if SEE < 1802) = {
    SEE = 1802;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opc : bits(2) = op_code[11 .. 10];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_rev_decode(Rd, Rn, opc, opcode2, S, sf)
}

function clause decode64 ((0b011111100 @ _ : bits(1) @ 0b100001101010 @ _ : bits(10) as op_code) if SEE < 1803) = {
    SEE = 1803;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_bulk_sisd_decode(Rd, Rn, o1, sz, o2, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111001111001100110 @ _ : bits(10) as op_code) if SEE < 1804) = {
    SEE = 1804;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_round_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110100 @ _ : bits(10) as op_code) if SEE < 1805) = {
    SEE = 1805;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_double_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010011 @ _ : bits(10) as op_code) if SEE < 1806) = {
    SEE = 1806;
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

function clause decode64 ((0b0111111011111001101110 @ _ : bits(10) as op_code) if SEE < 1807) = {
    SEE = 1807;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) if SEE < 1808) = {
    SEE = 1808;
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

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1809) = {
    SEE = 1809;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1810) = {
    SEE = 1810;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode(Rd, Rn, opcode, Rm, o1, U, Q)
}

function clause decode64 ((0b0001111001111110000000 @ _ : bits(10) as op_code) if SEE < 1811) = {
    SEE = 1811;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b11010100101 @ _ : bits(16) @ 0b00011 as op_code) if SEE < 1812) = {
    SEE = 1812;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_debug_exception_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b01011110110 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1813) = {
    SEE = 1813;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_rsqrtsfp16_sisd_decode(Rd, Rn, opcode, Rm, a, U)
}

function clause decode64 ((_ : bits(1) @ 0b101101011000000000100 @ _ : bits(10) as op_code) if SEE < 1814) = {
    SEE = 1814;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[10]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_arithmetic_cnt_decode(Rd, Rn, op, opcode2, S, sf)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b011000 @ _ : bits(10) as op_code) if SEE < 1815) = {
    SEE = 1815;
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

function clause decode64 ((0b1101010100000011001000 @ _ : bits(1) @ 0b111 @ _ : bits(1) @ 0b11111 as op_code) if SEE < 1816) = {
    SEE = 1816;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_autib_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0111111001111001101010 @ _ : bits(10) as op_code) if SEE < 1817) = {
    SEE = 1817;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110111 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1818) = {
    SEE = 1818;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b01001000110 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1819) = {
    SEE = 1819;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(7) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1820) = {
    SEE = 1820;
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

function clause decode64 ((0b00111000010 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1821) = {
    SEE = 1821;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1822) = {
    SEE = 1822;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_saturating_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b00111000000 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1823) = {
    SEE = 1823;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111100 @ _ : bits(6) @ 0b1001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1824) = {
    SEE = 1824;
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

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b10100 @ _ : bits(2) @ 0b10000 @ _ : bits(10) as op_code) if SEE < 1825) = {
    SEE = 1825;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(2) = op_code[16 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    float_arithmetic_round_frint_32_64_decode(Rd, Rn, op, typ)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000010 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1826) = {
    SEE = 1826;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101101 @ _ : bits(10) as op_code) if SEE < 1827) = {
    SEE = 1827;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b0010001 @ _ : bits(1) @ 0b1 @ _ : bits(6) @ 0b11111 @ _ : bits(10) as op_code) if SEE < 1828) = {
    SEE = 1828;
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

function clause decode64 ((0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1829) = {
    SEE = 1829;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b001000110 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1830) = {
    SEE = 1830;
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

function clause decode64 ((_ : bits(1) @ 0b0101011 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1831) = {
    SEE = 1831;
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

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001010 @ _ : bits(10) as op_code) if SEE < 1832) = {
    SEE = 1832;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001111 @ _ : bits(10) as op_code) if SEE < 1833) = {
    SEE = 1833;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    eq : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_cmp_int_sisd_decode(Rd, Rn, eq, Rm, size, U)
}

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b000011 @ _ : bits(16) as op_code) if SEE < 1834) = {
    SEE = 1834;
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

function clause decode64 ((0b11010101000000110011 @ _ : bits(4) @ 0b11111111 as op_code) if SEE < 1835) = {
    SEE = 1835;
    Rt : bits(5) = op_code[4 .. 0];
    opc : bits(2) = op_code[6 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    system_barriers_decode(Rt, opc, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) if SEE < 1836) = {
    SEE = 1836;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_fpmaxnm_simd_decode(Rd, Rn, opcode, sz, o1, U, Q)
}

function clause decode64 ((0b01001000010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1837) = {
    SEE = 1837;
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

function clause decode64 ((0b01011111 @ _ : bits(8) @ 0b1100 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1838) = {
    SEE = 1838;
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

function clause decode64 ((0b01111000011 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1839) = {
    SEE = 1839;
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

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010000 @ _ : bits(10) as op_code) if SEE < 1840) = {
    SEE = 1840;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111011 @ _ : bits(10) as op_code) if SEE < 1841) = {
    SEE = 1841;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111001101110 @ _ : bits(10) as op_code) if SEE < 1842) = {
    SEE = 1842;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b01011110000 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1843) = {
    SEE = 1843;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    imm5 : bits(5) = op_code[20 .. 16];
    op : bits(1) = [op_code[29]];
    vector_transfer_vector_cpydup_sisd_decode(Rd, Rn, imm4, imm5, op)
}

function clause decode64 ((0b01001000100 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1844) = {
    SEE = 1844;
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

function clause decode64 ((_ : bits(1) @ 0b0001010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1845) = {
    SEE = 1845;
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

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b0 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1846) = {
    SEE = 1846;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    S : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode(Rd, Rn, S, Rm, size, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101000 @ _ : bits(10) as op_code) if SEE < 1847) = {
    SEE = 1847;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_accum_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0101111000101000000110 @ _ : bits(10) as op_code) if SEE < 1848) = {
    SEE = 1848;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    vector_crypto_sha2op_sha1sched1_decode(Rd, Rn, opcode, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111001111001101010 @ _ : bits(10) as op_code) if SEE < 1849) = {
    SEE = 1849;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b100101010000 @ _ : bits(10) as op_code) if SEE < 1850) = {
    SEE = 1850;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    rmode : bits(3) = op_code[17 .. 15];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_arithmetic_round_frint_decode(Rd, Rn, rmode, typ, S, M)
}

function clause decode64 ((0b00011001101 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1851) = {
    SEE = 1851;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpairandzerodatapre_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b0101111010110000111110 @ _ : bits(10) as op_code) if SEE < 1852) = {
    SEE = 1852;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fp16max_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110101 @ _ : bits(5) @ 0b000111 @ _ : bits(10) as op_code) if SEE < 1853) = {
    SEE = 1853;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_logical_andorr_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b011110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1854) = {
    SEE = 1854;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b011110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b001100 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1855) = {
    SEE = 1855;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001100100 @ _ : bits(5) @ 0b1000 @ _ : bits(12) as op_code) if SEE < 1856) = {
    SEE = 1856;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, Rm, L, Q)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b100000110010 @ _ : bits(10) as op_code) if SEE < 1857) = {
    SEE = 1857;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode64 ((_ : bits(1) @ 0b0101010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1858) = {
    SEE = 1858;
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

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110101 @ _ : bits(10) as op_code) if SEE < 1859) = {
    SEE = 1859;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_sub_fp_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode64 ((0b001110011 @ _ : bits(23) as op_code) if SEE < 1860) = {
    SEE = 1860;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1861) = {
    SEE = 1861;
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

function clause decode64 ((_ : bits(1) @ 0b1101011001 @ _ : bits(21) as op_code) if SEE < 1862) = {
    SEE = 1862;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b101100 @ _ : bits(10) as op_code) if SEE < 1863) = {
    SEE = 1863;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[13]];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_disparate_mul_dmacc_simd_decode(Rd, Rn, o1, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101110 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1864) = {
    SEE = 1864;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b110000 @ _ : bits(10) as op_code) if SEE < 1865) = {
    SEE = 1865;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000101 @ _ : bits(10) as op_code) if SEE < 1866) = {
    SEE = 1866;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_rounding_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110001 @ _ : bits(10) as op_code) if SEE < 1867) = {
    SEE = 1867;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000000010 @ _ : bits(10) as op_code) if SEE < 1868) = {
    SEE = 1868;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_rev_decode(Rd, Rn, o0, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1869) = {
    SEE = 1869;
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

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) if SEE < 1870) = {
    SEE = 1870;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftsat_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b11011000 @ _ : bits(24) as op_code) if SEE < 1871) = {
    SEE = 1871;
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_literal_general_decode(Rt, imm19, V, opc)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b110000110010 @ _ : bits(10) as op_code) if SEE < 1872) = {
    SEE = 1872;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    o1 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_reduce_fpmaxnm_sisd_decode(Rd, Rn, opcode, sz, o1, U)
}

function clause decode64 ((0b010111100 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b110111 @ _ : bits(10) as op_code) if SEE < 1873) = {
    SEE = 1873;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_mul_fp_extended_sisd_decode(Rd, Rn, opcode, Rm, sz, U)
}

function clause decode64 ((_ : bits(1) @ 0b0110101 @ _ : bits(24) as op_code) if SEE < 1874) = {
    SEE = 1874;
    Rt : bits(5) = op_code[4 .. 0];
    imm19 : bits(19) = op_code[23 .. 5];
    op : bits(1) = [op_code[24]];
    sf : bits(1) = [op_code[31]];
    branch_conditional_compare_decode(Rt, imm19, op, sf)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011100 @ _ : bits(1) @ 0b100001100010 @ _ : bits(10) as op_code) if SEE < 1875) = {
    SEE = 1875;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b10110111 @ _ : bits(22) as op_code) if SEE < 1876) = {
    SEE = 1876;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b00011001010 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1877) = {
    SEE = 1877;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b11010101000000110010000011111111 as op_code) if SEE < 1878) = {
    SEE = 1878;
    Rt : bits(5) = op_code[4 .. 0];
    op2 : bits(3) = op_code[7 .. 5];
    CRm : bits(4) = op_code[11 .. 8];
    CRn : bits(4) = op_code[15 .. 12];
    op1 : bits(3) = op_code[18 .. 16];
    op0 : bits(2) = op_code[20 .. 19];
    L : bits(1) = [op_code[21]];
    integer_pac_strip_hint_decode(Rt, op2, CRm, CRn, op1, op0, L)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000001 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1879) = {
    SEE = 1879;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110110 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1880) = {
    SEE = 1880;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b100001001110 @ _ : bits(10) as op_code) if SEE < 1881) = {
    SEE = 1881;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_shift_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100001100110 @ _ : bits(10) as op_code) if SEE < 1882) = {
    SEE = 1882;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_round_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110010 @ _ : bits(5) @ 0b001011 @ _ : bits(10) as op_code) if SEE < 1883) = {
    SEE = 1883;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    ac : bits(1) = [op_code[11]];
    Rm : bits(5) = op_code[20 .. 16];
    E : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_cmp_fp16_simd_decode(Rd, Rn, ac, Rm, E, U, Q)
}

function clause decode64 ((0b011111110 @ _ : bits(7) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1884) = {
    SEE = 1884;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110000 @ _ : bits(5) @ 0b0 @ _ : bits(4) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1885) = {
    SEE = 1885;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm4 : bits(4) = op_code[14 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    op2 : bits(2) = op_code[23 .. 22];
    Q : bits(1) = [op_code[30]];
    vector_transfer_vector_extract_decode(Rd, Rn, imm4, Rm, op2, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001111 @ _ : bits(8) @ 0b1010 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1886) = {
    SEE = 1886;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110010 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1887) = {
    SEE = 1887;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Op3 : bits(3) = op_code[13 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode(Rd, Rn, Op3, Rm, a, U, Q)
}

function clause decode64 ((0b01001000010 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1888) = {
    SEE = 1888;
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

function clause decode64 ((0b11010100000 @ _ : bits(16) @ 0b00011 as op_code) if SEE < 1889) = {
    SEE = 1889;
    LL : bits(2) = op_code[1 .. 0];
    op2 : bits(3) = op_code[4 .. 2];
    imm16 : bits(16) = op_code[20 .. 5];
    opc : bits(3) = op_code[23 .. 21];
    system_exceptions_runtime_smc_decode(LL, op2, imm16, opc)
}

function clause decode64 ((0b001110001 @ _ : bits(1) @ 0b0 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1890) = {
    SEE = 1890;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0101111011111000111010 @ _ : bits(10) as op_code) if SEE < 1891) = {
    SEE = 1891;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_fp16_lessthan_sisd_decode(Rd, Rn, opcode, a, U)
}

function clause decode64 ((0b01111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) if SEE < 1892) = {
    SEE = 1892;
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

function clause decode64 ((0b00111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(10) as op_code) if SEE < 1893) = {
    SEE = 1893;
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

function clause decode64 ((0b11111000101 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1894) = {
    SEE = 1894;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110101100000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1895) = {
    SEE = 1895;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00110001000000 @ _ : bits(2) @ 0b1 @ _ : bits(13) as op_code) if SEE < 1896) = {
    SEE = 1896;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    size : bits(2) = op_code[11 .. 10];
    opcode : bits(4) = op_code[15 .. 12];
    L : bits(1) = [op_code[22]];
    Q : bits(1) = [op_code[30]];
    memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode(Rt, Rn, size, opcode, L, Q)
}

function clause decode64 ((0b010111101 @ _ : bits(1) @ 0b100000110110 @ _ : bits(10) as op_code) if SEE < 1897) = {
    SEE = 1897;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_cmp_float_bulk_sisd_decode(Rd, Rn, op, sz, U)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000000 @ _ : bits(9) @ 0b01 @ _ : bits(10) as op_code) if SEE < 1898) = {
    SEE = 1898;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm9, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111100000 @ _ : bits(6) @ 0b101 @ _ : bits(10) as op_code) if SEE < 1899) = {
    SEE = 1899;
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

function clause decode64 ((0b01011111 @ _ : bits(8) @ 0b1011 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1900) = {
    SEE = 1900;
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

function clause decode64 ((0b01001000100 @ _ : bits(5) @ 0b1 @ _ : bits(15) as op_code) if SEE < 1901) = {
    SEE = 1901;
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

function clause decode64 ((_ : bits(1) @ 0b1001010 @ _ : bits(2) @ 0b1 @ _ : bits(21) as op_code) if SEE < 1902) = {
    SEE = 1902;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b000001 @ _ : bits(10) as op_code) if SEE < 1903) = {
    SEE = 1903;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_add_halving_truncating_decode(Rd, Rn, opcode, Rm, size, U, Q)
}

function clause decode64 ((0b1111100110 @ _ : bits(22) as op_code) if SEE < 1904) = {
    SEE = 1904;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_unsigned__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b011111101 @ _ : bits(1) @ 0b100001110110 @ _ : bits(10) as op_code) if SEE < 1905) = {
    SEE = 1905;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_special_sqrtest_float_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b01111110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b100001 @ _ : bits(10) as op_code) if SEE < 1906) = {
    SEE = 1906;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode(Rd, Rn, opcode, Rm, size, U)
}

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b001101 @ _ : bits(10) as op_code) if SEE < 1907) = {
    SEE = 1907;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o0 : bits(1) = [op_code[12]];
    o1 : bits(1) = [op_code[13]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_right_sisd_decode(Rd, Rn, o0, o1, immb, immh, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011101 @ _ : bits(1) @ 0b100001101110 @ _ : bits(10) as op_code) if SEE < 1908) = {
    SEE = 1908;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    sz : bits(1) = [op_code[22]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_float_conv_float_bulk_simd_decode(Rd, Rn, o1, sz, o2, U, Q)
}

function clause decode64 ((_ : bits(2) @ 0b111101 @ _ : bits(1) @ 0b1 @ _ : bits(22) as op_code) if SEE < 1909) = {
    SEE = 1909;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((_ : bits(2) @ 0b10110000 @ _ : bits(22) as op_code) if SEE < 1910) = {
    SEE = 1910;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111100 @ _ : bits(6) @ 0b0101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1911) = {
    SEE = 1911;
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

function clause decode64 ((_ : bits(1) @ 0b010100101 @ _ : bits(22) as op_code) if SEE < 1912) = {
    SEE = 1912;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_offset_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b000010 @ _ : bits(10) as op_code) if SEE < 1913) = {
    SEE = 1913;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b101110 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b010001 @ _ : bits(10) as op_code) if SEE < 1914) = {
    SEE = 1914;
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

function clause decode64 ((0b00011001000 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1915) = {
    SEE = 1915;
    Rt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    integer_tags_mcsettagpre_decode(Rt, Xn, imm9)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b100000010110 @ _ : bits(10) as op_code) if SEE < 1916) = {
    SEE = 1916;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cnt_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b010111110 @ _ : bits(7) @ 0b011101 @ _ : bits(10) as op_code) if SEE < 1917) = {
    SEE = 1917;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[12]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    vector_shift_leftsat_sisd_decode(Rd, Rn, op, immb, immh, U)
}

function clause decode64 ((0b010111111 @ _ : bits(7) @ 0b0001 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1918) = {
    SEE = 1918;
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

function clause decode64 ((0b011110001 @ _ : bits(1) @ 0b1 @ _ : bits(9) @ 0b10 @ _ : bits(10) as op_code) if SEE < 1919) = {
    SEE = 1919;
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

function clause decode64 ((0b10011011010 @ _ : bits(5) @ 0b0 @ _ : bits(15) as op_code) if SEE < 1920) = {
    SEE = 1920;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000111110 @ _ : bits(10) as op_code) if SEE < 1921) = {
    SEE = 1921;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_diffneg_float_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b00011001110 @ _ : bits(9) @ 0b00 @ _ : bits(10) as op_code) if SEE < 1922) = {
    SEE = 1922;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm9 : bits(9) = op_code[20 .. 12];
    opc : bits(2) = op_code[23 .. 22];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode(Rt, Rn, imm9, opc, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011110 @ _ : bits(7) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1923) = {
    SEE = 1923;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_conv_float_simd_decode(Rd, Rn, opcode, immb, immh, U, Q)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b1110000 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b000000 @ _ : bits(5) @ 0b11111 as op_code) if SEE < 1924) = {
    SEE = 1924;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b00111011111001101010 @ _ : bits(10) as op_code) if SEE < 1925) = {
    SEE = 1925;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode(Rd, Rn, o1, o2, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001101111 @ _ : bits(7) @ 0b0 @ _ : bits(13) as op_code) if SEE < 1926) = {
    SEE = 1926;
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

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b100000111010 @ _ : bits(10) as op_code) if SEE < 1927) = {
    SEE = 1927;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_cmp_float_lessthan_simd_decode(Rd, Rn, opcode, sz, U, Q)
}

function clause decode64 ((0b0110100011 @ _ : bits(22) as op_code) if SEE < 1928) = {
    SEE = 1928;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Rt2 : bits(5) = op_code[14 .. 10];
    imm7 : bits(7) = op_code[21 .. 15];
    L : bits(1) = [op_code[22]];
    V : bits(1) = [op_code[26]];
    opc : bits(2) = op_code[31 .. 30];
    memory_pair_general_postidx_memory_pair_general_postidx__decode(Rt, Rn, Rt2, imm7, L, V, opc)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b10111001111001110110 @ _ : bits(10) as op_code) if SEE < 1929) = {
    SEE = 1929;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    a : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_unary_fp16_conv_int_simd_decode(Rd, Rn, opcode, a, U, Q)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b0011101 @ _ : bits(1) @ 0b1 @ _ : bits(5) @ 0b111111 @ _ : bits(10) as op_code) if SEE < 1930) = {
    SEE = 1930;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[15 .. 11];
    Rm : bits(5) = op_code[20 .. 16];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_arithmetic_binary_uniform_rsqrts_simd_decode(Rd, Rn, opcode, Rm, sz, U, Q)
}

function clause decode64 ((0b1011100110 @ _ : bits(22) as op_code) if SEE < 1931) = {
    SEE = 1931;
    Rt : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm12 : bits(12) = op_code[21 .. 10];
    opc : bits(2) = op_code[23 .. 22];
    V : bits(1) = [op_code[26]];
    size : bits(2) = op_code[31 .. 30];
    memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt, Rn, imm12, opc, V, size)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b1011110 @ _ : bits(7) @ 0b100101 @ _ : bits(10) as op_code) if SEE < 1932) = {
    SEE = 1932;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    op : bits(1) = [op_code[11]];
    immb : bits(3) = op_code[18 .. 16];
    immh : bits(4) = op_code[22 .. 19];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_shift_rightnarrow_uniform_simd_decode(Rd, Rn, op, immb, immh, U, Q)
}

function clause decode64 ((0b0101111001111001101110 @ _ : bits(10) as op_code) if SEE < 1933) = {
    SEE = 1933;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    o1 : bits(1) = [op_code[12]];
    o2 : bits(1) = [op_code[23]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode(Rd, Rn, o1, o2, U)
}

function clause decode64 ((0b010111100 @ _ : bits(1) @ 0b100001110010 @ _ : bits(10) as op_code) if SEE < 1934) = {
    SEE = 1934;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    sz : bits(1) = [op_code[22]];
    U : bits(1) = [op_code[29]];
    vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode(Rd, Rn, opcode, sz, U)
}

function clause decode64 ((0b0 @ _ : bits(1) @ 0b001110 @ _ : bits(2) @ 0b110000001110 @ _ : bits(10) as op_code) if SEE < 1935) = {
    SEE = 1935;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(5) = op_code[16 .. 12];
    size : bits(2) = op_code[23 .. 22];
    U : bits(1) = [op_code[29]];
    Q : bits(1) = [op_code[30]];
    vector_reduce_addlong_decode(Rd, Rn, opcode, size, U, Q)
}

function clause decode64 ((0b0110100010 @ _ : bits(22) as op_code) if SEE < 1936) = {
    SEE = 1936;
    Xt : bits(5) = op_code[4 .. 0];
    Xn : bits(5) = op_code[9 .. 5];
    Xt2 : bits(5) = op_code[14 .. 10];
    simm7 : bits(7) = op_code[21 .. 15];
    integer_tags_mcsettaganddatapairpost_decode(Xt, Xn, Xt2, simm7)
}

function clause decode64 ((0b00011110 @ _ : bits(2) @ 0b1 @ _ : bits(9) @ 0b11 @ _ : bits(10) as op_code) if SEE < 1937) = {
    SEE = 1937;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    cond : bits(4) = op_code[15 .. 12];
    Rm : bits(5) = op_code[20 .. 16];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    M : bits(1) = [op_code[31]];
    float_move_fp_select_decode(Rd, Rn, cond, Rm, typ, S, M)
}

function clause decode64 ((_ : bits(1) @ 0b0011010110 @ _ : bits(5) @ 0b001001 @ _ : bits(10) as op_code) if SEE < 1938) = {
    SEE = 1938;
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

function clause decode64 ((0b01011111 @ _ : bits(8) @ 0b1101 @ _ : bits(1) @ 0b0 @ _ : bits(10) as op_code) if SEE < 1939) = {
    SEE = 1939;
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

function clause decode64 ((_ : bits(1) @ 0b0011110 @ _ : bits(2) @ 0b100100000000 @ _ : bits(10) as op_code) if SEE < 1940) = {
    SEE = 1940;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    opcode : bits(3) = op_code[18 .. 16];
    rmode : bits(2) = op_code[20 .. 19];
    typ : bits(2) = op_code[23 .. 22];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    float_convert_int_decode(Rd, Rn, opcode, rmode, typ, S, sf)
}

function clause decode64 ((0b110110101100000100 @ _ : bits(1) @ 0b100 @ _ : bits(10) as op_code) if SEE < 1941) = {
    SEE = 1941;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    Z : bits(1) = [op_code[13]];
    opcode2 : bits(5) = op_code[20 .. 16];
    S : bits(1) = [op_code[29]];
    sf : bits(1) = [op_code[31]];
    integer_pac_autia_dp_1src_decode(Rd, Rn, Z, opcode2, S, sf)
}

function clause decode64 ((0b1 @ _ : bits(1) @ 0b111000 @ _ : bits(2) @ 0b1 @ _ : bits(5) @ 0b001000 @ _ : bits(10) as op_code) if SEE < 1942) = {
    SEE = 1942;
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
