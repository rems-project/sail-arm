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

// Redirect memory primitives to Sail builtins

val __ReadMem
  = { ocaml: "Platform.read_mem", c: "platform_read_mem", _: "read_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n) effect {rmem}

val __ReadTaggedMem
  = { lem: "read_memt", coq: "read_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, bits('addrsize), int('n)) -> (bits(8 * 'n), bit) effect {rmemt}

val __WriteMem
  = { lem: "write_mem", coq: "write_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool effect {wmv}

function __WriteMem(wk, addrsize, addr, size, data) = {
  match('addrsize) {
    32 => __write_mem(wk, 32, addr, size, data),
    64 => __write_mem(wk, 64, addr, size, data)
  }
}

val acctype_to_read_kind : AccType -> read_kind

function acctype_to_read_kind(acctype) = {
    match acctype {
        AccType_NORMAL => Read_plain,
        AccType_IFETCH => Read_ifetch,
        AccType_ORDERED => Read_acquire,
        AccType_ATOMIC => Read_exclusive,
        AccType_ATOMICRW => Read_exclusive,
        AccType_ORDEREDATOMIC => Read_exclusive_acquire,
        AccType_ORDEREDATOMICRW => Read_exclusive_acquire,
        _ => Read_plain
    }
}

val _Mem_read : forall 'size, 'size > 0. (AddressDescriptor, int('size), AccessDescriptor) -> bits(8 * 'size)

$ifdef HAVE_DEVICES
function _Mem_read (desc, size, accdesc) = {
  let paddress = desc.paddress.address;
  if (size >= 4 & paddress[(length(paddress) - 1) .. 16] == ZeroExtend(GIC_BASE)) then {
    // TODO: Pass read kind?
    ZeroExtend(__ReadGIC(paddress[15 .. 0]), 8 * size);
  } else if (paddress[(length(paddress) - 1) .. 16] == ZeroExtend(UART_BASE)) then {
    __ReadUART(paddress[15 .. 0], size);
  } else {
    __ReadMem(acctype_to_read_kind(accdesc.acctype), 64, ZeroExtend(paddress, 64), size)
  }
}
$else
function _Mem_read (desc, size, accdesc) = {
  __ReadMem(acctype_to_read_kind(accdesc.acctype), 64, ZeroExtend(desc.paddress.address, 64), size)
}
$endif

val acctype_to_write_kind : AccType -> write_kind

function acctype_to_write_kind(acctype) = {
    match acctype {
        AccType_ORDERED => Write_release,
        AccType_ATOMIC => Write_exclusive,
        AccType_ATOMICRW => Write_exclusive,
        AccType_ORDEREDATOMIC => Write_exclusive_release,
        AccType_ORDEREDATOMICRW => Write_exclusive_release,
        _ => Write_plain
    }
}

val _Mem_set : forall 'size, 'size > 0. (AddressDescriptor, int('size), AccessDescriptor, bits(8 * 'size)) -> unit

$ifdef HAVE_DEVICES
function _Mem_set (desc, size, accdesc, data) = {
  let paddress = desc.paddress.address;
  if (size == 4 & paddress[(length(paddress) - 1) .. 16] == ZeroExtend(GIC_BASE)) then {
    __WriteGIC(paddress[15 .. 0], data)
  } else if (paddress[(length(paddress) - 1) .. 16] == ZeroExtend(UART_BASE)) then {
    __WriteUART(paddress[15 .. 0], size, data)
  } else {
    let _ = __WriteMem(acctype_to_write_kind(accdesc.acctype), 64, ZeroExtend(paddress, 64), size, data);
    ()
  }
}
$else
function _Mem_set (desc, size, accdesc, data) = {
  let _ = __WriteMem(acctype_to_write_kind(accdesc.acctype), 64, ZeroExtend(desc.paddress.address, 64), size, data);
  ()
}
$endif

function PhysMemTagWrite (desc, accdesc, data) = {
  // TODO
  return undefined;
}

function PhysMemTagRead (desc, accdesc) = {
  // TODO
  return (undefined, undefined);
}

val CreatePhysMemRetStatus : (Fault, AccType) -> PhysMemRetStatus

function CreatePhysMemRetStatus (fault, acctype) = struct { statuscode = fault, extflag = 0b0, errortype = 0b00, store64bstatus = Zeros(), acctype = acctype }

function PhysMemRead (desc, size, accdesc) = {
  return (CreatePhysMemRetStatus(Fault_None, accdesc.acctype), _Mem_read(desc, size, accdesc));
}

function PhysMemWrite (desc, size, accdesc, data) = {
  _Mem_set(desc, size, accdesc, data);
  return CreatePhysMemRetStatus(Fault_None, accdesc.acctype);
}
