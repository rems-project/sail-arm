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

register SEE : int

val __DecodeA64 : (int, bits(32)) -> unit
val __DecodeA32 : (int, bits(32)) -> unit
val __DecodeT32 : (int, bits(32)) -> unit
val __DecodeT16 : (int, bits(16)) -> unit

val __DecodeA64_Reserved : (int, bits(32)) -> unit
val __DecodeA64_SME : (int, bits(32)) -> unit
val __DecodeA64_Unallocated1 : (int, bits(32)) -> unit
val __DecodeA64_SVE : (int, bits(32)) -> unit
val __DecodeA64_Unallocated2 : (int, bits(32)) -> unit
val __DecodeA64_DataProcImm : (int, bits(32)) -> unit
val __DecodeA64_BranchExcSys : (int, bits(32)) -> unit
val __DecodeA64_LoadStore : (int, bits(32)) -> unit
val __DecodeA64_DataProcReg : (int, bits(32)) -> unit
val __DecodeA64_DataProcFPSIMD : (int, bits(32)) -> unit

val __DecodeA32_Unconditional : (int, bits(32)) -> unit
val __DecodeA32_DataProMisc : (int, bits(32)) -> unit
val __DecodeA32_LoadStoreImmLit : (int, bits(32)) -> unit
val __DecodeA32_LoadStoreReg : (int, bits(32)) -> unit
val __DecodeA32_Media : (int, bits(32)) -> unit
val __DecodeA32_BranchBlock : (int, bits(32)) -> unit
val __DecodeA32_SysASIMDFP : (int, bits(32)) -> unit

scattered function __DecodeA64_Reserved
scattered function __DecodeA64_SME
scattered function __DecodeA64_Unallocated1
scattered function __DecodeA64_SVE
scattered function __DecodeA64_Unallocated2
scattered function __DecodeA64_DataProcImm
scattered function __DecodeA64_BranchExcSys
scattered function __DecodeA64_LoadStore
scattered function __DecodeA64_DataProcReg
scattered function __DecodeA64_DataProcFPSIMD

scattered function __DecodeA32_Unconditional
scattered function __DecodeA32_DataProMisc
scattered function __DecodeA32_LoadStoreImmLit
scattered function __DecodeA32_LoadStoreReg
scattered function __DecodeA32_Media
scattered function __DecodeA32_BranchBlock
scattered function __DecodeA32_SysASIMDFP

scattered function __DecodeA64
scattered function __DecodeA32
scattered function __DecodeT32
scattered function __DecodeT16
