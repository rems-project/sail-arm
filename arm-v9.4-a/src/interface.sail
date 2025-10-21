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

function mem_acc_is_explicit     (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR
function mem_acc_is_ifetch       (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_IFETCH
function mem_acc_is_ttw          (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_TTW
function mem_acc_is_relaxed      (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.acqpc) & not_bool(acc.acqsc) & not_bool(acc.relsc)
function mem_acc_is_rel_acq_rcpc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.acqpc
function mem_acc_is_rel_acq_rcsc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & (acc.acqsc | acc.relsc)
function mem_acc_is_standalone   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.exclusive) & not_bool(acc.atomicop)
function mem_acc_is_exclusive    (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.exclusive
function mem_acc_is_atomic_rmw   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.atomicop

instantiation sail_mem_read with
  'addr_size = 56,
  'addr_space = PASpace,
  'mem_acc = AccessDescriptor,
  'abort = Fault,
  'CHERI = false,
  'cap_size_log = 0,
  mem_acc_is_explicit = mem_acc_is_explicit,
  mem_acc_is_ifetch = mem_acc_is_ifetch,
  mem_acc_is_ttw = mem_acc_is_ttw,
  mem_acc_is_relaxed = mem_acc_is_relaxed,
  mem_acc_is_rel_acq_rcpc = mem_acc_is_rel_acq_rcpc,
  mem_acc_is_rel_acq_rcsc = mem_acc_is_rel_acq_rcsc,
  mem_acc_is_standalone = mem_acc_is_standalone,
  mem_acc_is_exclusive = mem_acc_is_exclusive,
  mem_acc_is_atomic_rmw = mem_acc_is_atomic_rmw

val memory_request : forall 'n, 'n > 0. (AccessDescriptor, int('n), FullAddress) -> Mem_request('n, 0, 56, PASpace, AccessDescriptor)

function memory_request(accdesc, size, pa) = struct {
  access_kind = accdesc,
  address = pa.address,
  address_space = pa.paspace,
  size = size,
  num_tag = 0
}

instantiation sail_mem_write with
  'addr_size = 56,
  'addr_space = PASpace,
  'mem_acc = AccessDescriptor,
  'abort = Fault,
  'CHERI = false,
  'cap_size_log = 0,
  mem_acc_is_explicit = mem_acc_is_explicit,
  mem_acc_is_ifetch = mem_acc_is_ifetch,
  mem_acc_is_ttw = mem_acc_is_ttw,
  mem_acc_is_relaxed = mem_acc_is_relaxed,
  mem_acc_is_rel_acq_rcpc = mem_acc_is_rel_acq_rcpc,
  mem_acc_is_rel_acq_rcsc = mem_acc_is_rel_acq_rcsc,
  mem_acc_is_standalone = mem_acc_is_standalone,
  mem_acc_is_exclusive = mem_acc_is_exclusive,
  mem_acc_is_atomic_rmw = mem_acc_is_atomic_rmw

instantiation sail_mem_address_announce with
  'addr_size = 56,
  'addr_space = PASpace,
  'mem_acc = AccessDescriptor,
  'abort = Fault,
  'CHERI = false,
  'cap_size_log = 0

val address_announce : forall 'n, 'n > 0. (AccessDescriptor, int('n), FullAddress) -> unit

function address_announce(accdesc, size, pa) = {
  sail_mem_address_announce(memory_request(accdesc, size, pa))
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
  'exn = option(FaultRecord)

val return_exception : bits(56) -> unit

function return_exception(x) = sail_return_exception(())
function take_exception(fault) = sail_take_exception(fault)
