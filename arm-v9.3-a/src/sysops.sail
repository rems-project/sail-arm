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

function _TLBInvalidate () = {
    TLBReset();
    return()
}

function ReportedPARAttrs parattrs = {
    return(parattrs)
}

function ReportedPARShareability sh = {
    return(sh)
}

function AArch32_ReportedInnerAttrs attrs = {
    return(attrs)
}

function AArch32_ReportedOuterAttrs attrs = {
    return(attrs)
}

function GetCacheInfo (level, cachetype) = {
    let 'numsets = __IMPDEF_integer("Numsets for DC SW instructions");
    let 'assosciativity = __IMPDEF_integer("Assosciativity for DC SW instructions");
    let 'linesize = __IMPDEF_integer("Linesize for DC SW instructions");
    return((numsets, assosciativity, linesize))
}

function DC_CIPAPA val_name = {
    return()
}

function DC_CIGDPAPA val_name = {
    return()
}

function BPIALLIS () = {
    return()
}

function BPIALL () = {
    return()
}

function BPIMVA val_name = {
    return()
}

function CP15DMB () = {
    return()
}

function CP15DSB () = {
    return()
}

function CP15ISB () = {
    return()
}

function AArch64_CheckNVCondsIfCurrentEL (op0, op1, crn, crm, op2) = {
    let is_reg_current_el : bool = (((op0 == 3 & op1 == 0) & crn == 4) & crm == 2) & op2 == 2;
    let have_nv_trap_conds : bool = ((HaveNVExt() & PSTATE.EL == EL1) & EL2Enabled()) & Slice(HCR_EL2, 42, 1) == 0b1;
    return(is_reg_current_el & have_nv_trap_conds)
}
