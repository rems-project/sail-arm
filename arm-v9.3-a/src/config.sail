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

function __ConfigureV81Features enabled = {
    __v81_implemented = enabled
}

function __ConfigureV82Features enabled = {
    __v82_implemented = enabled;
    if enabled then {
        __ConfigureV81Features(enabled)
    };
    ()
}

function __ConfigureV83Features enabled = {
    __v83_implemented = enabled;
    if enabled then {
        __ConfigureV82Features(enabled)
    };
    ()
}

function __ConfigureV84Features enabled = {
    __v84_implemented = enabled;
    if enabled then {
        __ConfigureV83Features(enabled)
    };
    ()
}

function __ConfigureV85Features enabled = {
    __v85_implemented = enabled;
    if enabled then {
        __ConfigureV84Features(enabled)
    };
    ()
}

function __ConfigureV86Features enabled = {
    __v86_implemented = enabled;
    if enabled then {
        __ConfigureV85Features(enabled)
    };
    ()
}

function __ConfigureV87Features enabled = {
    __v87_implemented = enabled;
    if enabled then {
        __ConfigureV86Features(enabled)
    };
    ()
}

function __ConfigureV88Features enabled = {
    __v88_implemented = enabled;
    if enabled then {
        __ConfigureV87Features(enabled)
    };
    ()
}

function __ConfigureV90Features enabled = {
    __v90_implemented = enabled;
    if enabled then {
        __ConfigureV85Features(enabled)
    };
    ()
}

function __ConfigureV91Features enabled = {
    __v91_implemented = enabled;
    if enabled then {
        __ConfigureV90Features(enabled);
        __ConfigureV86Features(enabled)
    };
    ()
}

function __ConfigureV92Features enabled = {
    __v92_implemented = enabled;
    if enabled then {
        __ConfigureV91Features(enabled);
        __ConfigureV87Features(enabled)
    };
    ()
}

function __ConfigureV93Features enabled = {
    __v93_implemented = enabled;
    if enabled then {
        __ConfigureV92Features(enabled);
        __ConfigureV88Features(enabled)
    };
    ()
}

function __decode_maxveclen value_name = {
    max_svl : {|128, 256, 512, 1024, 2048|} = 128;
    match value_name {
      1 => {
          max_svl = 128
      },
      3 => {
          max_svl = 256
      },
      7 => {
          max_svl = 512
      },
      15 => {
          max_svl = 1024
      },
      31 => {
          max_svl = 2048
      },
      _ => {
          max_svl = 512
      }
    };
    let 'max_svl = max_svl;
    return(max_svl)
}
