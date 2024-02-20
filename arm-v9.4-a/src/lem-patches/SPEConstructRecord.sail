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

val SPEConstructRecord : unit -> unit

function SPEConstructRecord () = {
    payload_size : int = undefined;
    SPEEmptyRecord();
    if SPESampleContextEL1Valid then {
        SPEAddPacketToRecord(0b01, 0b0100, SPESampleContextEL1)
    };
    if SPESampleContextEL2Valid then {
        SPEAddPacketToRecord(0b01, 0b0101, SPESampleContextEL2)
    };
    foreach (counter_index from 0 to (SPEMaxCounters - 1) by 1 in inc) {
        if SPESampleCounterValid[counter_index] then {
            if counter_index >= 8 then {
                SPEAddByteToRecord(0b001000 @ counter_index[4 .. 3])
            };
            let large_counters : bool = __IMPDEF_boolean("SPE 16bit counters");
            if SPESampleCounter[counter_index] > UInt(0xFFFF) & large_counters then {
                SPESampleCounter[counter_index] = UInt(0xFFFF)
            } else if SPESampleCounter[counter_index] > UInt(0xFFF) then {
                SPESampleCounter[counter_index] = UInt(0xFFF)
            } else ();
            SPEAddPacketToRecord(0b10, 0b1 @ counter_index[2 .. 0], SPESampleCounter[counter_index][15 .. 0])
        };
        ()
    };
    if HaveStatisticalProfilingv1p2() then {
        let include_prev_br_name : bool = __IMPDEF_boolean("SPE get prev br if not br");
        if SPESampleOpType != OpType_Branch & not_bool(include_prev_br_name) then {
            SPESampleAddressValid[SPEAddrPosPrevBranchTarget] = false
        };
        ()
    };
    if not_bool(StatisticalProfilingEnabled__1(EL2)) & SPESampleInstIsNV2 then {
        SPESampleAddressValid[SPEAddrPosDataVirtual] = false
    };
    foreach (address_index from 0 to (SPEMaxAddrs - 1) by 1 in inc) {
        if SPESampleAddressValid[address_index] then {
            if address_index >= 8 then {
                SPEAddByteToRecord(0b001000 @ address_index[4 .. 3])
            };
            SPEAddPacketToRecord(0b10, 0b0 @ address_index[2 .. 0], SPESampleAddress[address_index])
        };
        ()
    };
    if SPESampleDataSourceValid then {
        match SPEGetDataSourcePayloadSize() {
            1 => SPEAddPacketToRecord(0b01, 0b0011, SPESampleDataSource[7 .. 0]),
            2 => SPEAddPacketToRecord(0b01, 0b0011, SPESampleDataSource[15 .. 0]),
            _ => Unreachable()
        }
    };
    SPEAddPacketToRecord(0b01, 0b10 @ SPESampleClass, SPESampleSubclass);
    match SPEGetEventsPayloadSize() {
        1 => SPEAddPacketToRecord(0b01, 0b0010, SPESampleEvents[7 .. 0]),
        2 => SPEAddPacketToRecord(0b01, 0b0010, SPESampleEvents[15 .. 0]),
        4 => SPEAddPacketToRecord(0b01, 0b0010, SPESampleEvents[31 .. 0]),
        8 => SPEAddPacketToRecord(0b01, 0b0010, SPESampleEvents[63 .. 0]),
        _ => Unreachable()
    };
    if SPESampleTimestampValid then {
        SPEAddPacketToRecord(0b01, 0b0001, SPESampleTimestamp)
    } else {
        SPEAddByteToRecord(0b00000001)
    };
    while MOD(SPERecordSize, (1 << UInt(PMBIDR_EL1[Align]))) != 0 do {
        SPEAddByteToRecord(Zeros(8))
    };
    SPEWriteToBuffer()
}
