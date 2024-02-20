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

function clause __DecodeA64_Reserved(_, _) = throw (Error_Undefined())
function clause __DecodeA64_SME(_, _) = throw (Error_Undefined())
function clause __DecodeA64_Unallocated1(_, _) = throw (Error_Undefined())
function clause __DecodeA64_SVE(_, _) = throw (Error_Undefined())
function clause __DecodeA64_Unallocated2(_, _) = throw (Error_Undefined())
function clause __DecodeA64_DataProcImm(_, _) = throw (Error_Undefined())
function clause __DecodeA64_BranchExcSys(_, _) = throw (Error_Undefined())
function clause __DecodeA64_LoadStore(_, _) = throw (Error_Undefined())
function clause __DecodeA64_DataProcReg(_, _) = throw (Error_Undefined())
function clause __DecodeA64_DataProcFPSIMD(_, _) = throw (Error_Undefined())

function clause __DecodeA32_Unconditional(_, _) = throw (Error_Undefined())
function clause __DecodeA32_DataProMisc(_, _) = throw (Error_Undefined())
function clause __DecodeA32_LoadStoreImmLit(_, _) = throw (Error_Undefined())
function clause __DecodeA32_LoadStoreReg(_, _) = throw (Error_Undefined())
function clause __DecodeA32_Media(_, _) = throw (Error_Undefined())
function clause __DecodeA32_BranchBlock(_, _) = throw (Error_Undefined())
function clause __DecodeA32_SysASIMDFP(_, _) = throw (Error_Undefined())

function clause __DecodeT32(_, _) = throw (Error_Undefined())
function clause __DecodeT16(_, _) = throw (Error_Undefined())

end __DecodeA64_Reserved
end __DecodeA64_SME
end __DecodeA64_Unallocated1
end __DecodeA64_SVE
end __DecodeA64_Unallocated2
end __DecodeA64_DataProcImm
end __DecodeA64_BranchExcSys
end __DecodeA64_LoadStore
end __DecodeA64_DataProcReg
end __DecodeA64_DataProcFPSIMD

end __DecodeA32_Unconditional
end __DecodeA32_DataProMisc
end __DecodeA32_LoadStoreImmLit
end __DecodeA32_LoadStoreReg
end __DecodeA32_Media
end __DecodeA32_BranchBlock
end __DecodeA32_SysASIMDFP

end __DecodeT32
end __DecodeT16

function clause __DecodeA64(pc, opcode) =
  match opcode {
  [bitzero, _, _] @ 0x0 @ _ => __DecodeA64_Reserved(pc, opcode),
  [bitone, _ ,_] @ 0x0 @ _ => __DecodeA64_SME(pc, opcode),
  [_, _, _] @ 0x1 @ _ => __DecodeA64_Unallocated1(pc, opcode),
  [_, _, _] @ 0x2 @ _ => __DecodeA64_SVE(pc, opcode),
  [_, _, _] @ 0x3 @ _ => __DecodeA64_Unallocated2(pc, opcode),
  [_, _, _] @ 0b100 @ _ => __DecodeA64_DataProcImm(pc, opcode),
  [_, _, _] @ 0b101 @ _ => __DecodeA64_BranchExcSys(pc, opcode),
  [_, _, _, _, bitone, _, bitzero] @ _ => __DecodeA64_LoadStore(pc, opcode),
  [_, _, _, _] @ 0b101 @ _ => __DecodeA64_DataProcReg(pc, opcode),
  [_, _, _, _] @ 0b111 @ _ => __DecodeA64_DataProcFPSIMD(pc, opcode),
  }

function clause __DecodeA32(pc, opcode) =
  match opcode {
  0b11110 @ _ => __DecodeA32_Unconditional(pc, opcode),
  [_, _, _, _] @ 0b00 @ _ => __DecodeA32_DataProMisc(pc, opcode),
  [_, _, _, _] @ 0b010 @ _ => __DecodeA32_LoadStoreImmLit(pc, opcode),
  [_, _, _, _] @ 0b011 @ _ @ 0b0 @ (_ : bits(4)) => __DecodeA32_LoadStoreReg(pc, opcode),
  [_, _, _, _] @ 0b011 @ _ @ 0b1 @ (_ : bits(4)) => __DecodeA32_Media(pc, opcode),
  [_, _, _, _] @ 0b10 @ _ => __DecodeA32_BranchBlock(pc, opcode),
  [_, _, _, _] @ 0b11 @ _ => __DecodeA32_SysASIMDFP(pc, opcode),
  }

end __DecodeA64
end __DecodeA32
