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

$define ARM_SPEC

$include <regfp.sail>

val acctype_to_read_kind : AccType -> read_kind

function acctype_to_read_kind(acctype) = {
    match acctype {
        AccType_NORMAL => Read_plain,
        AccType_IFETCH => Read_ifetch,
        AccType_ORDERED => Read_acquire,
        AccType_ATOMIC => Read_exclusive,
        AccType_ORDEREDATOMIC => Read_exclusive_acquire,
        _ => Read_plain
    }
}

val sail_zero_extend = "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), int('m)) -> bits('m)

val __InitRAM : forall 'm. (atom('m), int, bits('m), bits(8)) -> unit

function __InitRAM (_, _, _, _) = ()

val __bad_read = "bad_read" : forall 'n. int('n) -> bits(8 * 'n)

val __ReadRAM : forall 'n 'm.
  (AccType, atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

function __ReadRAM(acctype, addr_length, bytes, hex_ram, addr) =
    if addr_length > 0 & addr_length <= 64 & bytes > 0 then {
        let addr = if acctype == AccType_IFETCH then __monomorphize(addr) else addr;
        __read_mem(acctype_to_read_kind(acctype), 64, sail_zero_extend(addr, 64), bytes)
    } else {
        __bad_read(bytes)
    }

val __TraceMemoryWrite : forall 'n 'm.
  (atom('n), bits('m), bits(8 * 'n)) -> unit

val __bad_write = "bad_write" : unit -> unit

/* FIXME: wmv vs wmem effect? */
val __write_mem2
  = { ocaml: "Platform.write_mem", c: "platform_write_mem", _: "write_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool effect {wmem}

val __bad_read = "bad_read" : forall 'n. int('n) -> bits(8 * 'n)

val acctype_to_write_kind : AccType -> write_kind

function acctype_to_write_kind(acctype) = {
    match acctype {
        AccType_ORDERED => Write_release,
        AccType_ATOMIC => Write_exclusive,
        AccType_ORDEREDATOMIC => Write_exclusive_release,
        _ => Write_plain
    }
}

val __WriteRAM : forall 'n 'm.
  (AccType, atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit effect {wmem}

function __WriteRAM(acctype, addr_length, bytes, hex_ram, addr, data) =
    if addr_length > 0 & addr_length <= 64 & bytes > 0 then {
      let _ = __write_mem2(acctype_to_write_kind(acctype), 64, sail_zero_extend(addr, 64), bytes, data);
      ()
    } else {
      __bad_write()
    }

function __TraceMemoryWrite(bytes, addr, data) = ()

val __TraceMemoryRead : forall 'n 'm. (atom('n), bits('m), bits(8 * 'n)) -> unit

function __TraceMemoryRead(bytes, addr, data) = ()

// Translates an Arm DSB or DMB into a Isla compatible barrier kind.
val to_barrier_kind : (bool, MBReqDomain, MBReqTypes) -> barrier_kind

function to_barrier_kind (is_dsb, domain, types) = {
    match (is_dsb, domain, types) {
      (false, MBReqDomain_FullSystem, MBReqTypes_All) => Barrier_DMB_SY,
      (false, MBReqDomain_FullSystem, MBReqTypes_Writes) => Barrier_DMB_ST,
      (false, MBReqDomain_FullSystem, MBReqTypes_Reads) => Barrier_DMB_LD,

      (false, MBReqDomain_InnerShareable, MBReqTypes_All) => Barrier_DMB_ISH,
      (false, MBReqDomain_InnerShareable, MBReqTypes_Writes) => Barrier_DMB_ISHST,
      (false, MBReqDomain_InnerShareable, MBReqTypes_Reads) => Barrier_DMB_ISHLD,

      (false, MBReqDomain_NonShareable, MBReqTypes_All) => Barrier_DMB_NSH,
      (false, MBReqDomain_NonShareable, MBReqTypes_Writes) => Barrier_DMB_NSHST,
      (false, MBReqDomain_NonShareable, MBReqTypes_Reads) => Barrier_DMB_NSHLD,

      (false, MBReqDomain_OuterShareable, MBReqTypes_All) => Barrier_DMB_OSH,
      (false, MBReqDomain_OuterShareable, MBReqTypes_Writes) => Barrier_DMB_OSHST,
      (false, MBReqDomain_OuterShareable, MBReqTypes_Reads) => Barrier_DMB_OSHLD,

      (true, MBReqDomain_FullSystem, MBReqTypes_All) => Barrier_DSB_SY,
      (true, MBReqDomain_FullSystem, MBReqTypes_Writes) => Barrier_DSB_ST,
      (true, MBReqDomain_FullSystem, MBReqTypes_Reads) => Barrier_DSB_LD,

      (true, MBReqDomain_InnerShareable, MBReqTypes_All) => Barrier_DSB_ISH,
      (true, MBReqDomain_InnerShareable, MBReqTypes_ST) => Barrier_DSB_ISHST,
      (true, MBReqDomain_InnerShareable, MBReqTypes_LD) => Barrier_DSB_ISHLD,

      (true, MBReqDomain_NonShareable, MBReqTypes_All) => Barrier_DSB_NSH,
      (true, MBReqDomain_NonShareable, MBReqTypes_ST) => Barrier_DSB_NSHST,
      (true, MBReqDomain_NonShareable, MBReqTypes_LD) => Barrier_DSB_NSHLD,

      (true, MBReqDomain_OuterShareable, MBReqTypes_All) => Barrier_DSB_OSH,
      (true, MBReqDomain_OuterShareable, MBReqTypes_ST) => Barrier_DSB_OSHST,
      (true, MBReqDomain_OuterShareable, MBReqTypes_LD) => Barrier_DSB_OSHLD
    }
}

/* FIXME: ARM stubs don't have effects */
val __barrier_no_effect
  = { ocaml: "Platform.barrier", c: "platform_barrier", _: "barrier" }
  : barrier_kind -> unit
