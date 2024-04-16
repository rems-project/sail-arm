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

$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>
$include <concurrency_interface/translation.sail>

// This the set of all Arm access types that are not covered by the generic
// interface access type.
union arm_acc_type = {
  // Software ASIMD extension load/store instructions
  SAcc_ASIMD : /* streaming access :*/ bool,
  // Software SVE load/store instructions
  SAcc_SVE : /* streaming access :*/ bool,
  // Software SME load/store instructions
  SAcc_SME : /* streaming access :*/ bool,
  // Sysop IC
  SAcc_IC : unit,
  // Sysop DC (not DC {Z,G,GZ}VA)
  SAcc_DC : unit,
  // Sysop DC {Z,G,GZ}VA
  SAcc_DCZero : unit,
  // Sysop AT
  SAcc_AT : unit,
  // NV2 memory redirected access
  SAcc_NV2 : unit,
  // Statistical Profiling buffer access
  SAcc_SPE : unit,
  // Guarded Control Stack access
  SAcc_GCS : unit,
  // Granule Protection Table Walk
  SAcc_GPTW : unit
}

function AccessDescriptor_to_Access_kind(accdesc : AccessDescriptor) -> Access_kind(arm_acc_type) = {
  // TODO
  match accdesc.acctype {
    AccessType_IFETCH => AK_ifetch(),
    AccessType_GPR =>
      let variety =
        if accdesc.exclusive then AV_exclusive
        else if accdesc.atomicop then AV_atomic_rmw
        else AV_plain
      in
      let strength =
        if accdesc.acqpc then AS_acq_rcpc
        else if accdesc.acqsc | accdesc.relsc then AS_rel_or_acq
        else AS_normal
      in
      AK_explicit(struct { variety, strength }),
    AccessType_TTW => AK_ttw(),
    AccessType_ASIMD => AK_arch(SAcc_ASIMD(accdesc.streamingsve)),
    AccessType_SVE => AK_arch(SAcc_SVE(accdesc.streamingsve)),
    AccessType_SME => AK_arch(SAcc_SME(accdesc.streamingsve)),
    AccessType_IC => AK_arch(SAcc_IC()),
    AccessType_DC => AK_arch(SAcc_DC()),
    AccessType_DCZero => AK_arch(SAcc_DCZero()),
    AccessType_AT => AK_arch(SAcc_AT()),
    AccessType_NV2 => AK_arch(SAcc_NV2()),
    AccessType_SPE => AK_arch(SAcc_SPE()),
    AccessType_GCS => AK_arch(SAcc_GCS()),
    AccessType_GPTW => AK_arch(SAcc_GPTW())
  }
}

val pa_bits : bits(56) -> bits(64)

function pa_bits(bv) = sail_zero_extend(bv, 64)

instantiation sail_mem_read with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = Fault,
  pa_bits = pa_bits

val read_request : forall 'n, 'n > 0. (AccessDescriptor, option(TranslationInfo), int('n), bits(64), bits(56)) -> Mem_read_request('n, 64, bits(56), option(TranslationInfo), arm_acc_type)

function read_request(accdesc, ti, size, va, pa) = struct {
  access_kind = AccessDescriptor_to_Access_kind(accdesc),
  va = Some(va),
  pa = pa,
  translation = ti,
  size = size,
  tag = false
}

instantiation sail_mem_write with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = Fault,
  pa_bits = pa_bits

val write_request : forall 'n, 'n > 0. (AccessDescriptor, option(TranslationInfo), int('n), bits(64), bits(56), bits(8 * 'n)) -> Mem_write_request('n, 64, bits(56), option(TranslationInfo), arm_acc_type)

function write_request(accdesc, ti, size, va, pa, value) = struct {
  access_kind = AccessDescriptor_to_Access_kind(accdesc),
  va = Some(va),
  pa = pa,
  translation = ti,
  size = size,
  value = Some(value),
  tag = None(),
}

instantiation sail_translation_start with
  'trans_start = TranslationStartInfo

function start_translation(tsi) = sail_translation_start(tsi)

instantiation sail_translation_end with
  'trans_end = AddressDescriptor

function end_translation(desc) = sail_translation_end(desc)

struct TLBIInfo = {
  rec: TLBIRecord,
  shareability : Shareability,
}

instantiation sail_tlbi with
  'tlbi = TLBIInfo

function report_tlbi(r, s) = sail_tlbi(struct { rec = r, shareability = s })

// The details of a data memory/synchonisation barrier
struct DxB = {
  domain : MBReqDomain,
  types : MBReqTypes,
  nXS : bool
}

// An Arm barrier
union Barrier = {
  Barrier_DSB : DxB,
  Barrier_DMB : DxB, // The nXS field is ignored from DMBs
  Barrier_ISB : unit,
  Barrier_SSBB : unit,
  Barrier_PSSBB : unit,
  Barrier_SB : unit,
}

instantiation sail_cache_op with
  'cache_op = CacheRecord

function CACHE_OP(r) = sail_cache_op(r)

instantiation sail_barrier with
  'barrier = Barrier

instantiation sail_return_exception

instantiation sail_take_exception with
  'fault = option(FaultRecord)

val return_exception : bits(56) -> unit

function return_exception(x) = sail_return_exception(x)
function take_exception(fault) = sail_take_exception(fault)
