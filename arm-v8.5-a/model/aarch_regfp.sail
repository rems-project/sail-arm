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

$ifndef AARCH64_REGFP
$define AARCH64_REGFP

enum read_kind = {
  Read_plain,
  Read_reserve,
  Read_acquire,
  Read_exclusive,
  Read_exclusive_acquire,
  Read_stream,
  Read_ifetch
}

enum write_kind = {
  Write_plain,
  Write_conditional,
  Write_release,
  Write_exclusive,
  Write_exclusive_release,
  Write_RISCV_release,
  Write_RISCV_strong_release,
  Write_RISCV_conditional,
  Write_RISCV_conditional_release,
  Write_RISCV_conditional_strong_release,
  Write_X86_locked
}

enum barrier_kind = {
  Barrier_DMB_SY,
  Barrier_DMB_ST,
  Barrier_DMB_LD,
  Barrier_DMB_ISH,
  Barrier_DMB_ISHST,
  Barrier_DMB_ISHLD,
  Barrier_DMB_NSH,
  Barrier_DMB_NSHST,
  Barrier_DMB_NSHLD,
  Barrier_DMB_OSH,
  Barrier_DMB_OSHST,
  Barrier_DMB_OSHLD,
  Barrier_DSB_SY,
  Barrier_DSB_ST,
  Barrier_DSB_LD,
  Barrier_DSB_ISH,
  Barrier_DSB_ISHST,
  Barrier_DSB_ISHLD,
  Barrier_DSB_NSH,
  Barrier_DSB_NSHST,
  Barrier_DSB_NSHLD,
  Barrier_DSB_OSH,
  Barrier_DSB_OSHST,
  Barrier_DSB_OSHLD,
  Barrier_ISB,
  Barrier_ERET
}

/* cache maintenance instructions */
enum cache_op_kind = {
  /* AArch64 DC */
  Cache_op_D_IVAC, Cache_op_D_ISW,  Cache_op_D_CSW,  Cache_op_D_CISW,
  Cache_op_D_ZVA,  Cache_op_D_CVAC, Cache_op_D_CVAU, Cache_op_D_CIVAC,
  /* AArch64 IC */
  Cache_op_I_IALLUIS, Cache_op_I_IALLU, Cache_op_I_IVAU,
  /* AArch64 TLBI */
  Cache_op_TLBI_VMALLS12E1OS,
  Cache_op_TLBI_VMALLS12E1IS,
  Cache_op_TLBI_VMALLS12E1,
  Cache_op_TLBI_VMALLE1OS,
  Cache_op_TLBI_VMALLE1IS,
  Cache_op_TLBI_VMALLE1,
  Cache_op_TLBI_VALE3OS,
  Cache_op_TLBI_VALE3IS,
  Cache_op_TLBI_VALE3,
  Cache_op_TLBI_VALE1OS,
  Cache_op_TLBI_VALE1IS,
  Cache_op_TLBI_VALE1,
  Cache_op_TLBI_VAE3OS,
  Cache_op_TLBI_VAE3IS,
  Cache_op_TLBI_VAE3,
  Cache_op_TLBI_VAE1OS,
  Cache_op_TLBI_VAE1IS,
  Cache_op_TLBI_VAE1,
  Cache_op_TLBI_VAALE1OS,
  Cache_op_TLBI_VAALE1IS,
  Cache_op_TLBI_VAALE1,
  Cache_op_TLBI_VAAE1OS,
  Cache_op_TLBI_VAAE1IS,
  Cache_op_TLBI_VAAE1,
  Cache_op_TLBI_RVALE3IS,
  Cache_op_TLBI_RVALE3,
  Cache_op_TLBI_RVALE1OS,
  Cache_op_TLBI_RVALE1IS,
  Cache_op_TLBI_RVALE1,
  Cache_op_TLBI_RVAE3OS,
  Cache_op_TLBI_RVAE3IS,
  Cache_op_TLBI_RVAE3,
  Cache_op_TLBI_RVAE1OS,
  Cache_op_TLBI_RVAE1IS,
  Cache_op_TLBI_RVAE1,
  Cache_op_TLBI_RVAALE1OS,
  Cache_op_TLBI_RVAALE1IS,
  Cache_op_TLBI_RVAALE1,
  Cache_op_TLBI_RVAAE1OS,
  Cache_op_TLBI_RVAAE1IS,
  Cache_op_TLBI_RVAAE1,
  Cache_op_TLBI_RIPAS2LE1OS,
  Cache_op_TLBI_RIPAS2LE1IS,
  Cache_op_TLBI_RIPAS2LE1,
  Cache_op_TLBI_RIPAS2E1OS,
  Cache_op_TLBI_RIPAS2E1IS,
  Cache_op_TLBI_RIPAS2E1,
  Cache_op_TLBI_IPAS2LE1OS,
  Cache_op_TLBI_IPAS2LE1IS,
  Cache_op_TLBI_IPAS2LE1,
  Cache_op_TLBI_IPAS2E1OS,
  Cache_op_TLBI_IPAS2E1IS,
  Cache_op_TLBI_IPAS2E1,
  Cache_op_TLBI_ASIDE1OS,
  Cache_op_TLBI_ASIDE1IS,
  Cache_op_TLBI_ASIDE1,
  Cache_op_TLBI_ALLE3OS,
  Cache_op_TLBI_ALLE3IS,
  Cache_op_TLBI_ALLE3,
  Cache_op_TLBI_ALLE1OS,
  Cache_op_TLBI_ALLE1IS,
  Cache_op_TLBI_ALLE1,
  Cache_op_TLBI_VALE2OS,
  Cache_op_TLBI_VALE2IS,
  Cache_op_TLBI_VALE2,
  Cache_op_TLBI_VAE2OS,
  Cache_op_TLBI_VAE2IS,
  Cache_op_TLBI_VAE2,
  Cache_op_TLBI_RVALE2OS,
  Cache_op_TLBI_RVALE2IS,
  Cache_op_TLBI_RVALE2,
  Cache_op_TLBI_RVAE2OS,
  Cache_op_TLBI_RVAE2IS,
  Cache_op_TLBI_RVAE2,
  Cache_op_TLBI_ALLE2OS,
  Cache_op_TLBI_ALLE2IS,
  Cache_op_TLBI_ALLE2
}

val __read_mem
  = { ocaml: "Platform.read_mem", c: "platform_read_mem", _: "read_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n) effect {rmem}

val __read_memt
  = { ocaml: "Platform.read_memt", c: "platform_read_memt", _: "read_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, bits('addrsize), int('n)) -> (bits(8 * 'n), bit) effect {rmemt}

val __write_mem_ea
  = { ocaml: "Platform.write_mem_ea", c: "platform_write_mem_ea", _: "write_mem_ea" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n)) -> unit effect {eamem}

val __write_mem
  = { ocaml: "Platform.write_mem", c: "platform_write_mem", _: "write_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool effect {wmv}

val __write_memt
  = { ocaml: "Platform.write_memt", c: "platform_write_memt", _: "write_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, bits('addrsize), int('n), bits(8 * 'n), bit) -> bool effect {wmvt}

val __write_tag
  = { ocaml: "Platform.write_tag", c: "platform_write_tag", _: "write_tag" }
  : forall (constant 'addrsize : Int), 'addrsize in {32, 64}.
  (write_kind, bits('addrsize), bit) -> bool effect {wmvt}

val __excl_res
  = { ocaml: "Platform.excl_res", c: "platform_excl_res", _: "excl_result" }
  : unit -> bool effect {exmem}

val __barrier
  = { ocaml: "Platform.barrier", c: "platform_barrier", _: "barrier" }
  : barrier_kind -> unit effect {barr}

val __branch_announce
  = { ocaml: "Platform.branch_announce", c: "platform_branch_announce", _ : "branch_announce" }
  : forall (constant 'addrsize : Int), 'addrsize in {32, 64}.
  (int('addrsize), bits('addrsize)) -> unit

val __cache_maintenance
  = { ocaml: "Platform.cache_maintenance", c: "platform_cache_maintenance", _ : "cache_maintenance" }
  : forall (constant 'addrsize : Int), 'addrsize in {32, 64}.
  (cache_op_kind, int('addrsize), bits('addrsize)) -> unit

val __instr_announce
  = { ocaml: "Platform.instr_announce", c: "platform_instr_announce", _: "instr_announce" }
  : forall 'n, 'n > 0.
  bits('n) -> unit

$endif
