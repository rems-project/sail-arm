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

function PhysMemTagWrite (desc, accdesc, data) = {
  // TODO
  return undefined;
}

function PhysMemTagRead (desc, accdesc) = {
  // TODO
  return (undefined, undefined);
}

val CreatePhysMemRetStatus : (Fault, AccType) -> PhysMemRetStatus

function CreatePhysMemRetStatus (fault, acctype) = struct {
  statuscode = fault,
  extflag = 0b0,
  errortype = 0b00,
  store64bstatus = Zeros(),
  acctype = acctype
}

function PhysMemRead (desc, size, accdesc) = {
  match sail_mem_read(read_request(accdesc.acctype, None(), size, desc.vaddress, 0x0 @ desc.paddress.address)) {
    Ok((value, _)) => (CreatePhysMemRetStatus(Fault_None, accdesc.acctype), value),
    Err(statuscode) => (CreatePhysMemRetStatus(statuscode, accdesc.acctype), sail_zeros(8 * size))
  }
}

function PhysMemWrite (desc, size, accdesc, data) = {
  if size > 0 then {
    match sail_mem_write(write_request(accdesc.acctype, None(), size, desc.vaddress, 0x0 @ desc.paddress.address, data)) {
      Ok(_) => CreatePhysMemRetStatus(Fault_None, accdesc.acctype),
      Err(statuscode) => CreatePhysMemRetStatus(statuscode, accdesc.acctype)
    }
  } else {
    CreatePhysMemRetStatus(Fault_None, accdesc.acctype)
  }
}
