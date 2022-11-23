/******************************************************************************/
/*  BSD 3-clause Clear License                                                */
/*                                                                            */
/*  Copyright (c) 2022                                                        */
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

function AArch32_CurrentCond () = {
    return(__UNKNOWN_bits(4))
}

function AArch32_IsExclusiveVA (address, processorid, size) = {
    return(__UNKNOWN_boolean())
}

function AArch32_MarkExclusiveVA (address, processorid, size) = {
    return()
}

function AArch32_PhysicalSErrorSyndrome () = {
    return(__UNKNOWN_AArch32_SErrorSyndrome())
}

function AArch32_SetLSInstructionSyndrome (size, sign_extend, Rt, acq_rel) = {
    return()
}

function AddressSupportsLS64 address = {
    return(__UNKNOWN_boolean())
}

function CPYPostSizeChoice (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_bits(64))
}

function CPYPreSizeChoice (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_bits(64))
}

function CPYSizeChoice (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_integer())
}

function CTI_SignalEvent id = {
    return()
}

function ChooseRandomNonExcludedTag exclude_in = {
    return(__UNKNOWN_bits(4))
}

function ClearExclusiveByAddress (paddress, processorid, size) = {
    return()
}

function ClearExclusiveLocal processorid = {
    return()
}

function CommitTransactionalWrites () = {
    return()
}

function ConsumptionOfSpeculativeDataBarrier () = {
    return()
}

function DataMemoryBarrier (domain, types) = {
    return()
}

function DataSynchronizationBarrier (domain, types, nXS) = {
    return()
}

function DiscardTransactionalWrites () = {
    return()
}

function EnterLowPowerState () = {
    return()
}

function GetAccumulatedFPExceptions () = {
    return(__UNKNOWN_bits(8))
}

function Hint_Branch hint = {
    return()
}

function Hint_DGH () = {
    return()
}

function Hint_Prefetch (address, hint, target, stream) = {
    return()
}

function Hint_PreloadData address = {
    return()
}

function Hint_PreloadDataForWrite address = {
    return()
}

function Hint_PreloadInstr address = {
    return()
}

function Hint_Yield () = {
    return()
}

function InstructionSynchronizationBarrier () = {
    return()
}

function IsASEInstruction () = {
    return(__UNKNOWN_boolean())
}

function IsCMOWControlledInstruction () = {
    return(__UNKNOWN_boolean())
}

function IsExternalAbortTakenSynchronously (memstatus, iswrite, desc, size, accdesc) = {
    return(__UNKNOWN_boolean())
}

function IsSIMDFPLoadStore () = {
    return(__UNKNOWN_boolean())
}

function IsSMESaveRestore () = {
    return(__UNKNOWN_boolean())
}

function IsSynchronizablePhysicalSErrorPending () = {
    return(__UNKNOWN_boolean())
}

function IsTagCheckedInstruction () = {
    return(__UNKNOWN_boolean())
}

function IsVirtualSErrorPending () = {
    return(__UNKNOWN_boolean())
}

function LS64InstructionSyndrome () = {
    return(undefined : (bits(5), bits(11), bits(2)))
}

function LocalTimeoutEvent localtimeout = {
    return(__UNKNOWN_boolean())
}

function MarkExclusiveGlobal (paddress, processorid, size) = {
    return()
}

function MarkExclusiveLocal (paddress, processorid, size) = {
    return()
}

function MemCpyDirectionChoice (fromaddress, toaddress, cpysize) = {
    return(__UNKNOWN_boolean())
}

function MemCpyParametersIllformedE (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_boolean())
}

function MemCpyParametersIllformedM (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_boolean())
}

function MemCpyZeroSizeCheck () = {
    return(__UNKNOWN_boolean())
}

function MemSetParametersIllformedE (toaddress, setsize, IsSETGE) = {
    return(__UNKNOWN_boolean())
}

function MemSetParametersIllformedM (toaddress, setsize, IsSETGM) = {
    return(__UNKNOWN_boolean())
}

function MemSetZeroSizeCheck () = {
    return(__UNKNOWN_boolean())
}

function PEErrorState memstatus = {
    return(__UNKNOWN_bits(2))
}

function PendSErrorInterrupt fault = {
    return()
}

function ProfilingSynchronizationBarrier () = {
    return()
}

function RemapRegsHaveResetValues () = {
    return(__UNKNOWN_boolean())
}

function ResetExternalDebugRegisters cold_reset = {
    return()
}

function S1TLBCache tlbrecord = {
    return()
}

function S1TLBLookup tlbcontext = {
    return(__UNKNOWN_TLBLine())
}

function S2TLBCache tlbrecord = {
    return()
}

function S2TLBLookup tlbcontext = {
    return(__UNKNOWN_TLBLine())
}

function SETPostSizeChoice (toaddress, setsize, IsSETGE) = {
    return(__UNKNOWN_bits(64))
}

function SETPreSizeChoice (toaddress, setsize, IsSETGP) = {
    return(__UNKNOWN_bits(64))
}

function SETSizeChoice (toaddress, setsize, AlignSize) = {
    return(__UNKNOWN_integer())
}

function SendEvent () = {
    return()
}

function SetAccumulatedFPExceptions accumulated_exceptions = {
    return()
}

function SetIss2 rs = {
    return()
}

function SetLoadStoreType instr = {
    return()
}

function SetTagCheckedInstruction checked = {
    return()
}

function SpeculationBarrier () = {
    return()
}

function SpeculativeStoreBypassBarrierToPA () = {
    return()
}

function SpeculativeStoreBypassBarrierToVA () = {
    return()
}

function StartTrackingTransactionalReadsWrites () = {
    return()
}

function StopInstructionPrefetchAndEnableITR () = {
    return()
}

function SupportedNonPowerTwoVL nbits = {
    return(__UNKNOWN_boolean())
}

function SupportedPowerTwoSVL nbits = {
    return(__UNKNOWN_boolean())
}

function SynchronizeContext () = {
    return()
}

function SynchronizeErrors () = {
    return()
}

function TLBReset () = {
    return()
}

function VirtualFIQPending () = {
    return(__UNKNOWN_boolean())
}

function VirtualIRQPending () = {
    return(__UNKNOWN_boolean())
}

function WaitForEventUntilDelay (delay_enabled, delay) = {
    return(__UNKNOWN_boolean())
}
