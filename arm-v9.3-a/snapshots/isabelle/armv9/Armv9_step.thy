theory "Armv9_step" 

imports
  "Sail-Armv9-Instrs.Armv9_decode"

begin 

\<comment> \<open>\<open>val is_none : forall 'a. maybe 'a -> bool\<close>\<close>

fun is_none  :: \<open> 'a option \<Rightarrow> bool \<close>  where 
     \<open> is_none (Some (_)) = ( False )\<close>
|\<open> is_none None = ( True )\<close>


\<comment> \<open>\<open>val __GIC_ClearPendingInterrupt : mword ty32 -> M unit\<close>\<close>

definition GIC_ClearPendingInterrupt  :: \<open>(32)Word.word \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> GIC_ClearPendingInterrupt intid = (
   read_reg GIC_Pending_ref \<bind> ((\<lambda> (w__0 ::  InterruptID option) . 
   (case  w__0 of
     Some (pending_intid) =>
      if (((((GIC_InterruptID pending_intid  ::  32 Word.word)) = intid))) then
        write_reg GIC_Pending_ref None
      else return () 
   | _ => return () 
   ))))\<close> 
  for  "intid"  :: "(32)Word.word "


\<comment> \<open>\<open>val gic_write_ram : mword ty16 -> mword ty32 -> M unit\<close>\<close>

definition gic_write_ram  :: \<open>(16)Word.word \<Rightarrow>(32)Word.word \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> gic_write_ram (offset :: 16 bits) (data :: 32 bits) = (
   write_mem instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_plain (( 64 :: int)::ii)
     ((zero_extend ((concat_vec GIC_BASE offset  ::  32 Word.word)) (( 64 :: int)::ii)  ::  64 Word.word)) (( 4 :: int)::ii) data \<bind> ((\<lambda> success . 
   return () )))\<close> 
  for  "offset"  :: "(16)Word.word " 
  and  "data"  :: "(32)Word.word "


\<comment> \<open>\<open>val Init_Devices : unit -> M unit\<close>\<close>

definition Init_Devices  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> Init_Devices _ = ( write_reg GIC_Pending_ref None \<then> write_reg GIC_Active_ref None )\<close>


\<comment> \<open>\<open>val __HandlePendingInterrupt : unit -> M unit\<close>\<close>

definition HandlePendingInterrupt  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> HandlePendingInterrupt _ = (
   read_reg GIC_Pending_ref \<bind> ((\<lambda> (w__0 ::  InterruptID option) . 
   (case  w__0 of
     Some (intid) =>
      (let (_ :: unit) = (prerr_bits 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (''[Clock] GIC interrupt '') ((GIC_InterruptID intid  ::  32 Word.word))) in
      AArch64_TakePhysicalIRQException () )
   | None => return () 
   ))))\<close>


\<comment> \<open>\<open>val __SetThisInstrEnc : __InstrEnc -> M unit\<close>\<close>

definition SetThisInstrEnc  :: \<open> InstrEnc \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> SetThisInstrEnc enc = ( write_reg ThisInstrEnc_ref enc )\<close> 
  for  "enc"  :: " InstrEnc "


\<comment> \<open>\<open>val __FetchNextInstr : unit -> M (__InstrEnc * mword ty32)\<close>\<close>

definition FetchNextInstr  :: \<open> unit \<Rightarrow>((register_value),(InstrEnc*(32)Word.word),(exception))monad \<close>  where 
     \<open> FetchNextInstr _ = (
   CurrentInstrSet ()  \<bind> ((\<lambda> (w__0 :: InstrSet) . 
   (case  w__0 of
     InstrSet_A32 =>
      ((AArch32_CheckPCAlignment ()  \<then>
      AArch32_CheckIllegalState () ) \<then>
      (PC_read ()   :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__1 ::  64 Word.word) . 
      (AArch32_MemSingle_read ((subrange_vec_dec w__1 (( 31 :: int)::ii) (( 0 :: int)::ii)  ::  32 Word.word)) (( 4 :: int)::ii)
         AccType_IFETCH True
        :: ( 32 Word.word) M) \<bind> ((\<lambda> (w__2 ::  32 Word.word) . 
      return (A32, w__2)))))
   | InstrSet_T32 =>
      ((AArch32_CheckPCAlignment ()  \<then>
      AArch32_CheckIllegalState () ) \<then>
      (PC_read ()   :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__3 ::  64 Word.word) . 
      (AArch32_MemSingle_read ((subrange_vec_dec w__3 (( 31 :: int)::ii) (( 0 :: int)::ii)  ::  32 Word.word)) (( 2 :: int)::ii)
         AccType_IFETCH True
        :: ( 16 Word.word) M) \<bind> ((\<lambda> hw1 . 
      if ((((((((subrange_vec_dec hw1 (( 15 :: int)::ii) (( 13 :: int)::ii)  ::  3 Word.word)) = ( 0b111 ::  3 Word.word)))) \<and> (((((subrange_vec_dec hw1 (( 12 :: int)::ii) (( 11 :: int)::ii)  ::  2 Word.word)) \<noteq> ( 0b00 ::  2 Word.word)))))))
      then
        (PC_read ()   :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__4 ::  64 Word.word) . 
        (AArch32_MemSingle_read
           ((add_vec_int ((subrange_vec_dec w__4 (( 31 :: int)::ii) (( 0 :: int)::ii)  ::  32 Word.word)) (( 2 :: int)::ii)  ::  32 Word.word))
           (( 2 :: int)::ii) AccType_IFETCH True
          :: ( 16 Word.word) M) \<bind> ((\<lambda> hw2 . 
        return (T32, (concat_vec hw1 hw2  ::  32 Word.word))))))
      else return (T16, (zero_extend hw1 (( 32 :: int)::ii)  ::  32 Word.word))))))
   | InstrSet_A64 =>
      ((AArch64_CheckPCAlignment ()  \<then>
      AArch64_CheckIllegalState () ) \<then>
      (PC_read ()   :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__6 ::  64 Word.word) . 
      (AArch64_MemSingle_read w__6 (( 4 :: int)::ii) AccType_IFETCH True  :: ( 32 Word.word) M) \<bind> ((\<lambda> (w__7 ::
         32 Word.word) . 
      return (A64, w__7)))))
   ))))\<close>


\<comment> \<open>\<open>val __ExecuteInstr : __InstrEnc -> mword ty32 -> M unit\<close>\<close>

fun ExecuteInstr  :: \<open> InstrEnc \<Rightarrow>(32)Word.word \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> ExecuteInstr A64 opcode = (
      (read_reg PC_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__0 ::  64 Word.word) . 
      DecodeA64 ((Word.uint w__0)) opcode)))\<close> 
  for  "opcode"  :: "(32)Word.word "
|\<open> ExecuteInstr A32 opcode = (
      (read_reg PC_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__1 ::  64 Word.word) . 
      DecodeA32 ((Word.uint w__1)) opcode)))\<close> 
  for  "opcode"  :: "(32)Word.word "
|\<open> ExecuteInstr T32 opcode = (
      (read_reg PC_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__2 ::  64 Word.word) . 
      DecodeT32 ((Word.uint w__2)) opcode)))\<close> 
  for  "opcode"  :: "(32)Word.word "
|\<open> ExecuteInstr T16 opcode = (
      (read_reg PC_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__3 ::  64 Word.word) . 
      DecodeT16 ((Word.uint w__3)) ((subrange_vec_dec opcode (( 15 :: int)::ii) (( 0 :: int)::ii)  ::  16 Word.word)))))\<close> 
  for  "opcode"  :: "(32)Word.word "


definition ExclusiveMonitorsStatus  :: \<open> unit \<Rightarrow>(1)Word.word \<close>  where 
     \<open> ExclusiveMonitorsStatus _ = ( ( 0b0 ::  1 Word.word))\<close>


definition UndefinedFault  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> UndefinedFault _ = ( AArch64_UndefinedFault ()  )\<close>


\<comment> \<open>\<open>val Step_PC : unit -> M unit\<close>\<close>

definition Step_PC  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> Step_PC _ = (
   read_reg BranchTaken_ref \<bind> ((\<lambda> (w__0 :: bool) . 
   (if ((\<not> w__0)) then
      (NextInstrAddr (( 64 :: int)::ii)  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__1 ::  64 Word.word) . 
      (write_reg PC_ref w__1 \<then>
      UsingAArch32 () ) \<bind> ((\<lambda> (w__2 :: bool) . 
      if w__2 then
        (read_reg PC_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__3 ::  64 Word.word) . 
        assert_exp (((((subrange_vec_dec w__3 (( 63 :: int)::ii) (( 32 :: int)::ii)  ::  32 Word.word)) = ((Zeros (( 32 :: int)::ii)  ::  32 Word.word))))) (''src/step.sail:51.60-51.61'')))
      else return () ))))
    else return () ) \<then>
   SSAdvance () )))\<close>


\<comment> \<open>\<open>val Step_CPU : unit -> M unit\<close>\<close>

definition Step_CPU  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> Step_CPU _ = (
   (let (fetch_ok :: bool) = False in
   (read_reg PC_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (oldPC :: 64 bits) . 
   (let (opcode :: 32 bits) = ((Zeros (( 32 :: int)::ii)  ::  32 Word.word)) in
   read_reg ThisInstrEnc_ref \<bind> ((\<lambda> (enc :: InstrEnc) . 
   try_catch ((FetchNextInstr ()   :: ((InstrEnc *  32 Word.word)) M) \<bind> ((\<lambda> (w__0 ::
                (InstrEnc *  32 Word.word)) . 
              (let (tup__0, tup__1) = w__0 in
              (let (enc :: InstrEnc) = tup__0 in
              (let (opcode :: 32 bits) = tup__1 in
              (SetThisInstr opcode \<then>
              SetThisInstrEnc enc) \<then>
              ((let (fetch_ok :: bool) = True in
              (GetVerbosity ()   :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__1 ::  64 Word.word) . 
              (if (((((access_vec_dec w__1 (( 1 :: int)::ii))) = B1))) then
                 get_cycle_count ()  \<bind> ((\<lambda> (w__2 :: ii) . 
                 return ((prerr_endline
                            (((@)
                                (((@)
                                    (((@)
                                        (((@)
                                            (((@) (''[Sail] IFetch from PC='')
                                                ((string_of_bits oldPC)))) ('' in cycle='')))
                                        ((dec_str w__2)))) ('': ''))) ((string_of_bits opcode))))))))
               else return () ) \<then>
              return (enc, fetch_ok, opcode))))))))))) ((\<lambda>x .  
  (case  x of
        Error_ExceptionTaken (_) =>
  (ESR_read__1 ()  :: ( 64 Word.word) M) \<bind>
    ((\<lambda> (w__3 :: 64 Word.word) . 
     (FAR_read__1 ()  :: ( 64 Word.word) M) \<bind>
       ((\<lambda> (w__4 :: 64 Word.word) . 
        get_cycle_count ()  \<bind>
          ((\<lambda> (w__5 :: ii) . 
           return
             ((let (_ :: unit) =
                   (print_endline
                      (((@)
                          (((@)
                              (((@)
                                  (((@)
                                      (((@)
                                          (((@)
                                              (((@)
                                                  (((@)
                                                      (''Exception taken during IFetch from PC='')
                                                      ((string_of_bits oldPC))))
                                                  ('' ESR='')))
                                              ((string_of_bits w__3))))
                                          ('' FAR='')))
                                      ((string_of_bits w__4)))) ('' cycle='')))
                              ((dec_str w__5)))) ([(CHR 0xA)])))) in
              (enc, fetch_ok, opcode)))))))))
    | _ =>
  (let (_ :: unit) = (print_endline
                        ([(CHR ''E''), (CHR ''x''), (CHR ''i''), (CHR ''t''), (CHR ''i''), (CHR ''n''), (CHR ''g''), (CHR '' ''), (CHR ''d''), (CHR ''u''), (CHR ''e''), (CHR '' ''), (CHR ''t''), (CHR ''o''), (CHR '' ''), (CHR ''u''), (CHR ''n''), (CHR ''h''), (CHR ''a''), (CHR ''n''), (CHR ''d''), (CHR ''l''), (CHR ''e''), (CHR ''d''), (CHR '' ''), (CHR ''e''), (CHR ''x''), (CHR ''c''), (CHR ''e''), (CHR ''p''), (CHR ''t''), (CHR ''i''), (CHR ''o''), (CHR ''n''), (CHR '' ''), (CHR ''i''), (CHR ''n''), (CHR '' ''), (CHR ''I''), (CHR ''F''), (CHR ''e''), (CHR ''t''), (CHR ''c''), (CHR ''h''), (CHR 0xA)])) in
  exit0 ()  \<then> return (enc, fetch_ok, opcode))
  ))) \<bind> ((\<lambda> varstup .  (let ((enc :: InstrEnc), (fetch_ok :: bool), (opcode ::  32 Word.word)) = varstup in
   (if (((opcode = ( 0xFEE1DEAD ::  32 Word.word)))) then
      (let (_ :: unit) = (print_endline ([(CHR ''[''), (CHR ''S''), (CHR ''a''), (CHR ''i''), (CHR ''l''), (CHR '']''), (CHR '' ''), (CHR ''F''), (CHR ''i''), (CHR ''n''), (CHR ''i''), (CHR ''s''), (CHR ''h''), (CHR ''e''), (CHR ''d''), (CHR '' ''), (CHR ''S''), (CHR ''u''), (CHR ''c''), (CHR ''c''), (CHR ''e''), (CHR ''s''), (CHR ''s''), (CHR ''f''), (CHR ''u''), (CHR ''l''), (CHR ''l''), (CHR ''y''), (CHR ''!''), (CHR 0xA)])) in
      exit0 () )
    else return () ) \<then>
   (if fetch_ok then
     and_boolM (return (((opcode = ( 0xD69F03E0 ::  32 Word.word)))))
       (and_boolM
          (read_reg PSTATE_ref \<bind> ((\<lambda> (w__6 :: ProcState) .  return ((((ProcState_EL   w__6) = EL3))))))
          ((read_reg SCR_EL3_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__7 ::  64 Word.word) . 
           return (((((access_vec_dec w__7 (( 0 :: int)::ii))) = B0))))))) \<bind> ((\<lambda> (w__9 :: bool) . 
     ((if w__9 then
        (let (_ :: unit) =
          (print_endline
            (((@) (''UNIMPLEMENTED: EL2_Secure support (v8.4 feature) '')
                (((@) ((hex_str ((Word.uint opcode)))) ([(CHR 0xA)])))))) in
        exit0 () )
      else return () ) \<then>
     try_catch (write_reg BranchTaken_ref False \<then>
                try_catch ((ExecuteInstr enc opcode)) ((\<lambda>x .  
  (case  x of
        Error_See (msg) =>
  (GetVerbosity ()  :: ( 64 Word.word) M) \<bind>
    ((\<lambda> (w__10 :: 64 Word.word) . 
     (let (_ :: unit) =
          (
          if (((((access_vec_dec w__10 (( 1 :: int):: ii))) = B1))) then
            prerr_endline
              (((@) (((@) (''[Sail] SEE('') msg)) (''), retrying decode'')))
          else () ) in ExecuteInstr enc opcode)))
    | e => throw e
  )))) ((\<lambda>x .  (case  x of
       Error_Undefined (_) =>
 try_catch ((UndefinedFault () ))
   ((\<lambda>x .  (case  x of
                         _ =>
                   return
                     ((prerr_endline
                         (((@)
                             (((@)
                                 (((@)
                                     (''Exception during Undefined recovery at PC='')
                                     ((string_of_bits oldPC)))) ('' instr='')))
                             ((string_of_bits opcode))))))
                   )))
   | Error_See (msg) =>
 (let (_ :: unit) =
      (print_endline
         (((@)
             (((@)
                 ([(CHR ''U''), (CHR ''n''), (CHR ''e''), (CHR ''x''), (CHR ''p''), (CHR ''e''), (CHR ''c''), (CHR ''t''), (CHR ''e''), (CHR ''d''), (CHR '' ''), (CHR ''S''), (CHR ''E''), (CHR ''E''), (CHR '':''), (CHR '' ''), (CHR 0x27)])
                 msg))
             ([(CHR 0x27), (CHR '',''), (CHR '' ''), (CHR ''e''), (CHR ''x''), (CHR ''i''), (CHR ''t''), (CHR ''i''), (CHR ''n''), (CHR ''g''), (CHR ''.''), (CHR 0xA)])))) in
 exit0 () )
   | Error_ReservedEncoding (g__37211) =>
 try_catch ((UndefinedFault () ))
   ((\<lambda>x .  (case  x of
                         _ => return
                                ((prerr_endline
                                    (''Exception during ReservedEncoding recovery'')))
                   )))
   | Error_ExceptionTaken (_) =>
 (ESR_read__1 ()  :: ( 64 Word.word) M) \<bind>
   ((\<lambda> (w__11 :: 64 Word.word) . 
    (FAR_read__1 ()  :: ( 64 Word.word) M) \<bind>
      ((\<lambda> (w__12 :: 64 Word.word) . 
       get_cycle_count ()  \<bind>
         ((\<lambda> (w__13 :: ii) . 
          return
            ((prerr_endline
                (((@)
                    (((@)
                        (((@)
                            (((@)
                                (((@)
                                    (((@)
                                        (((@)
                                            (''Exception taken during Decode/Execute from PC='')
                                            ((string_of_bits oldPC))))
                                        ('' ESR='')))
                                    ((string_of_bits w__11)))) ('' FAR='')))
                            ((string_of_bits w__12)))) ('' cycle='')))
                    ((dec_str w__13))))))))))))
   | Error_ImplementationDefined (s) =>
 (let (_ :: unit) =
      (print_endline
         (((@) (''IMPLEMENTATION_DEFINED '') (((@) s ([(CHR 0xA)])))))) in
 exit0 () )
   | e => throw e
 )))) \<then>
     Step_PC () ))
   else return () )))))))))))\<close>


\<comment> \<open>\<open>val Init_Timers : unit -> M unit\<close>\<close>

definition Init_Timers  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> Init_Timers _ = (
   (read_reg CNTCR_ref  :: ( 32 Word.word) M) \<bind> ((\<lambda> (w__0 ::  32 Word.word) . 
   write_reg CNTCR_ref ((update_vec_dec w__0 (( 0 :: int)::ii) B1  ::  32 Word.word)))))\<close>


\<comment> \<open>\<open>val Step_Timers : unit -> M unit\<close>\<close>

definition Step_Timers  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> Step_Timers _ = (
   (GenericCounterTick ()  \<then>
   and_boolM ((GIC_InterruptPending () ))
     (read_reg PSTATE_ref \<bind> ((\<lambda> (w__1 :: ProcState) . 
      return ((((ProcState_I   w__1) = ( 0b0 ::  1 Word.word)))))))) \<bind> ((\<lambda> (w__2 :: bool) . 
   if w__2 then HandlePendingInterrupt () 
   else return () )))\<close>


\<comment> \<open>\<open>val Step_System : unit -> M unit\<close>\<close>

definition Step_System  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> Step_System _ = (
   (try_catch ((Step_Timers () )) ((\<lambda>x .  
  (case  x of
        _ =>
  (read_reg PC_ref :: ( 64 Word.word) M) \<bind>
    ((\<lambda> (w__0 :: 64 Word.word) . 
     get_cycle_count ()  \<bind>
       ((\<lambda> (w__1 :: ii) . 
        return
          ((prerr_endline
              (((@) (''Exception taken during Step_Timers.  PC='')
                  (((@) ((hex_str ((Word.uint w__0))))
                      (((@) ('' cycle='')
                          (((@) ((dec_str w__1)) ([(CHR 0xA)])))))))))))))))
  ))) \<then>
   read_reg PSTATE_ref) \<bind> ((\<lambda> (w__2 :: ProcState) . 
   (let prevEL = ((ProcState_EL   w__2)) in
   read_reg PSTATE_ref \<bind> ((\<lambda> (w__3 :: ProcState) . 
   (let prevI = ((ProcState_I   w__3)) in
   (read_reg CNTKCTL_EL1_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> prevCNTKCTL_EL1 . 
   (read_reg CNTHCTL_EL2_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> prevCNTHCTL_EL2 . 
   (try_catch ((Step_CPU () )) ((\<lambda>x .  
  (case  x of
        _ =>
  (read_reg PC_ref :: ( 64 Word.word) M) \<bind>
    ((\<lambda> (w__4 :: 64 Word.word) . 
     get_cycle_count ()  \<bind>
       ((\<lambda> (w__5 :: ii) . 
        return
          ((prerr_endline
              (((@) (''Exception taken during Step_CPU.  PC='')
                  (((@) ((hex_str ((Word.uint w__4))))
                      (((@) ('' cycle='')
                          (((@) ((dec_str w__5)) ([(CHR 0xA)])))))))))))))))
  ))) \<then>
   read_reg PSTATE_ref) \<bind> ((\<lambda> (w__6 :: ProcState) . 
   ((if (((((Word.uint prevEL)) \<noteq> ((Word.uint(ProcState_EL   w__6)))))) then
      get_cycle_count ()  \<bind> ((\<lambda> (w__7 :: ii) . 
      read_reg PSTATE_ref \<bind> ((\<lambda> (w__8 :: ProcState) . 
      return ((prerr_bits 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict
                 (((@) (''[Sail] '')
                     (((@) ((dec_str w__7)) ('' Exception level changed to: '')))))(ProcState_EL  
                 w__8)))))))
    else return () ) \<then>
   read_reg PSTATE_ref) \<bind> ((\<lambda> (w__9 :: ProcState) . 
   ((if (((prevI \<noteq>(ProcState_I   w__9)))) then
      read_reg PSTATE_ref \<bind> ((\<lambda> (w__10 :: ProcState) . 
      (let (_ :: unit) = (prerr_bits 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (''[Sail] PSTATE.I changed to: '')(ProcState_I   w__10)) in
      (read_reg PC_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__11 ::  64 Word.word) . 
      get_cycle_count ()  \<bind> ((\<lambda> (w__12 :: ii) . 
      return ((prerr_endline
                 (((@) (''   at PC='')
                     (((@) ((hex_str ((Word.uint w__11))))
                         (((@) ('' in cycle='') (((@) ((dec_str w__12)) ([(CHR 0xA)]))))))))))))))))))
    else return () ) \<then>
   (read_reg CNTKCTL_EL1_ref  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__13 ::  64 Word.word) . 
   ((if (((prevCNTKCTL_EL1 \<noteq> w__13))) then
      (read_reg CNTKCTL_EL1_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__14 ::  64 Word.word) . 
      return ((prerr_bits 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (''[Clock] CNTKCTL_EL1 changed to '') w__14))))
    else return () ) \<then>
   (read_reg CNTHCTL_EL2_ref  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__15 ::  64 Word.word) . 
   if (((prevCNTHCTL_EL2 \<noteq> w__15))) then
     (read_reg CNTHCTL_EL2_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__16 ::  64 Word.word) . 
     return ((prerr_bits 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (''[Clock] CNTHCTL_EL2 changed to '') w__16))))
   else return () )))))))))))))))))))\<close>


\<comment> \<open>\<open>val __InitSystem : unit -> M unit\<close>\<close>

definition InitSystem  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> InitSystem _ = ( ((write_reg DBGEN_ref LOW \<then> TakeReset True) \<then> Init_Timers () ) \<then> Init_Devices ()  )\<close>


definition EndCycle  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> EndCycle _ = (
   read_reg cycle_count_ref \<bind> ((\<lambda> (w__0 :: ii) . 
   write_reg cycle_count_ref ((w__0 + (( 1 :: int)::ii))))))\<close>


definition TopLevel  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> TopLevel _ = (
   try_catch (Step_System ()  \<then> EndCycle () ) ((\<lambda>x .  
  (case  x of
        Error_ExceptionTaken (_) =>
  (read_reg PC_ref :: ( 64 Word.word) M) \<bind>
    ((\<lambda> (w__0 :: 64 Word.word) . 
     get_cycle_count ()  \<bind>
       ((\<lambda> (w__1 :: ii) . 
        (let (_ :: unit) =
             (prerr_endline
                (((@) (''Exception taken during Step_System.  PC='')
                    (((@) ((hex_str ((Word.uint w__0))))
                        (((@) ('' cycle='')
                            (((@) ((dec_str w__1)) ([(CHR 0xA)])))))))))) in
        return () )))))
    | _ =>
  (let (_ :: unit) = (prerr_endline
                        ([(CHR ''E''), (CHR ''x''), (CHR ''i''), (CHR ''t''), (CHR ''i''), (CHR ''n''), (CHR ''g''), (CHR '' ''), (CHR ''d''), (CHR ''u''), (CHR ''e''), (CHR '' ''), (CHR ''t''), (CHR ''o''), (CHR '' ''), (CHR ''u''), (CHR ''n''), (CHR ''h''), (CHR ''a''), (CHR ''n''), (CHR ''d''), (CHR ''l''), (CHR ''e''), (CHR ''d''), (CHR '' ''), (CHR ''e''), (CHR ''x''), (CHR ''c''), (CHR ''e''), (CHR ''p''), (CHR ''t''), (CHR ''i''), (CHR ''o''), (CHR ''n''), (CHR 0xA)])) in
  exit0 () )
  ))))\<close>


definition CycleEnd  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> CycleEnd _ = ( EndCycle ()  )\<close>


definition SetConfig  :: \<open> string \<Rightarrow> int \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> SetConfig arg1 value_name = (
   if (((arg1 = (''cpu.has_arm_v8-1'')))) then ConfigureV81Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v8-2'')))) then ConfigureV82Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v8-3'')))) then ConfigureV83Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v8-4'')))) then ConfigureV84Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v8-5'')))) then ConfigureV85Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v8-6'')))) then ConfigureV86Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v8-7'')))) then ConfigureV87Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v8-8'')))) then ConfigureV88Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v9-0'')))) then ConfigureV90Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v9-1'')))) then ConfigureV91Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v9-2'')))) then ConfigureV92Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_arm_v9-3'')))) then ConfigureV93Features (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.CONFIG64'')))) then
     write_reg CFG_RMR_AA64_ref (vec_of_bits [integer_access value_name (( 0 :: int)::ii)]  ::  1 Word.word)
   else if (((arg1 = (''cpu.cpu0.RVBAR'')))) then
     write_reg CFG_RVBAR_ref ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
   else if (((arg1 = (''cpu.num_loregions'')))) then
     (read_reg LORID_EL1_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__0 ::  64 Word.word) . 
     write_reg
       LORID_EL1_ref
       ((set_slice (( 64 :: int)::ii) (( 8 :: int)::ii) w__0 (( 0 :: int)::ii)
           ((integer_subrange value_name (( 7 :: int)::ii) (( 0 :: int)::ii)  ::  8 Word.word))
          ::  64 Word.word))))
   else if (((arg1 = (''cpu.num_loregion_descriptors'')))) then
     (read_reg LORID_EL1_ref  :: ( 64 Word.word) M) \<bind> ((\<lambda> (w__1 ::  64 Word.word) . 
     write_reg
       LORID_EL1_ref
       ((set_slice (( 64 :: int)::ii) (( 8 :: int)::ii) w__1 (( 16 :: int)::ii)
           ((integer_subrange value_name (( 7 :: int)::ii) (( 0 :: int)::ii)  ::  8 Word.word))
          ::  64 Word.word))))
   else if (((arg1 = (''cpu.has_mops_option'')))) then
     write_reg mops_option_a_supported_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.mops_cpy_default_dir'')))) then
     write_reg mops_forward_copy_ref (((value_name = (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.has_pstate_pan'')))) then
     write_reg pan_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.has_16bit_vmids'')))) then
     write_reg vmid16_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.enable_crc32'')))) then
     write_reg crc32_implemented_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_dot_product'')))) then
     write_reg dot_product_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.has_fp16'')))) then write_reg fp16_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.has_aarch32_hpd'')))) then
     write_reg aa32_hpd_implemented_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.crypto_aes'')))) then write_reg crypto_aes_implemented_ref value_name
   else if (((arg1 = (''cpu.cpu0.crypto_sha1'')))) then
     write_reg crypto_sha1_implemented_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.crypto_sha256'')))) then
     write_reg crypto_sha256_implemented_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.crypto_sha512'')))) then
     write_reg crypto_sha512_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.crypto_sha3'')))) then
     write_reg crypto_sha3_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.crypto_sm3'')))) then
     write_reg crypto_sm3_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.crypto_sm4'')))) then
     write_reg crypto_sm4_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.BBM'')))) then write_reg block_bbm_implemented_ref value_name
   else if (((arg1 = (''cpu.cpu0.number-of-breakpoints'')))) then
     write_reg num_breakpoints_ref value_name
   else if (((arg1 = (''cpu.cpu0.number-of-watchpoints'')))) then
     write_reg num_watchpoints_ref value_name
   else if (((arg1 = (''cpu.cpu0.number-of-context-breakpoints'')))) then
     write_reg num_ctx_breakpoints_ref value_name
   else if (((arg1 = (''cpu.pmu-num_counters'')))) then write_reg num_event_counters_ref value_name
   else if (((arg1 = (''cpu.PA_SIZE'')))) then write_reg supported_pa_size_ref value_name
   else if (((arg1 = (''cpu.VA_SIZE'')))) then write_reg supported_va_size_ref value_name
   else if (((arg1 = (''ctiBase'')))) then
     write_reg
       CTIBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''counter_addr'')))) then
     write_reg
       CNTControlBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''cntReadBase'')))) then
     write_reg
       CNTReadBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''cntBaseN'')))) then
     write_reg
       CNTBaseN_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''cntEL0BaseN'')))) then
     write_reg
       CNTEL0BaseN_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''cntCTLBase'')))) then
     write_reg
       CNTCTLBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''ExtDebugBase'')))) then
     write_reg
       ExtDebugBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''cpu.PERIPHBASE'')))) then
     write_reg
       GICCPUInterfaceBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''gic_distributor.reg-base'')))) then
     write_reg
       GICDistBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''rdBase'')))) then
     write_reg
       RD_base_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''sgiBase'')))) then
     write_reg
       SGI_base_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''vlpiBase'')))) then
     write_reg
       VLPI_base_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''gic_distributor.ITS0-base'')))) then
     write_reg
       GICITSControlBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''pmuBase'')))) then
     write_reg
       PMUBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''dbg_rom_addr'')))) then
     write_reg
       DBG_ROM_ADDR_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''etmBase'')))) then
     write_reg
       ETEBase_ref
       ((integer_subrange value_name (((( 52 :: int)::ii) - (( 1 :: int)::ii))) (( 0 :: int)::ii)  ::  52 Word.word))
   else if (((arg1 = (''globalcounter.base_frequency'')))) then
     write_reg CNTbase_frequency_ref ((integer_subrange value_name (( 31 :: int)::ii) (( 0 :: int)::ii)  ::  32 Word.word))
   else if (((arg1 = (''cpu.ext_abort_normal_cacheable_read_is_sync'')))) then
     write_reg syncAbortOnReadNormCache_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_normal_noncacheable_read_is_sync'')))) then
     write_reg syncAbortOnReadNormNonCache_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_device_read_is_sync'')))) then
     write_reg syncAbortOnDeviceRead_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_so_read_is_sync'')))) then
     write_reg syncAbortOnSoRead_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_so_write_is_sync'')))) then
     write_reg syncAbortOnSoWrite_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_prefetch_is_sync'')))) then
     write_reg syncAbortOnPrefetch_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_ttw_cacheable_read_is_sync'')))) then
     write_reg syncAbortOnTTWCache_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_ttw_noncacheable_read_is_sync'')))) then
     write_reg syncAbortOnTTWNonCache_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_normal_cacheable_write_is_sync'')))) then
     write_reg syncAbortOnWriteNormCache_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_normal_noncacheable_write_is_sync'')))) then
     write_reg syncAbortOnWriteNormNonCache_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.ext_abort_device_write_is_sync'')))) then
     write_reg syncAbortOnDeviceWrite_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_mpam'')))) then write_reg mpam_implemented_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.mpam_has_hcr'')))) then write_reg mpam_has_hcr_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.mpam_max_partid'')))) then
     write_reg mpam_partid_max_ref ((integer_subrange value_name (( 15 :: int)::ii) (( 0 :: int)::ii)  ::  16 Word.word))
   else if (((arg1 = (''cpu.mpam_max_pmg'')))) then
     write_reg mpam_pmg_max_ref ((integer_subrange value_name (( 7 :: int)::ii) (( 0 :: int)::ii)  ::  8 Word.word))
   else if (((arg1 = (''cpu.mpam_max_vpmr'')))) then
     write_reg mpam_vpmr_max_ref ((integer_subrange value_name (( 2 :: int)::ii) (( 0 :: int)::ii)  ::  3 Word.word))
   else if (((arg1 = (''cpu.mpam_has_altsp'')))) then
     write_reg mpam_has_altsp_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_empam'')))) then
     write_reg empam_implemented_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.mpamidr_has_tidr'')))) then
     write_reg empam_tidr_implemented_ref ((value_name > (( 0 :: int)::ii)))
   else if (((arg1 = (''cpu.mpamidr_has_sdeflt'')))) then
     write_reg empam_sdeflt_implemented_ref ((value_name > (( 0 :: int)::ii)))
   else if (((arg1 = (''cpu.mpamidr_has_force_ns'')))) then
     write_reg empam_force_ns_implemented_ref ((value_name > (( 0 :: int)::ii)))
   else if (((arg1 = (''cpu.mpam_force_ns_rao'')))) then
     write_reg empam_force_ns_RAO_ref ((value_name > (( 0 :: int)::ii)))
   else if (((arg1 = (''cpu.mpam_frac'')))) then
     write_reg empam_frac_ref ((integer_subrange value_name (( 3 :: int)::ii) (( 0 :: int)::ii)  ::  4 Word.word))
   else if (((arg1 = (''cpu.CCSIDR-L1I_override'')))) then
     read_reg ICACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__2 :: ( 64 Word.word) list) . 
     write_reg
       ICACHE_CCSIDR_RESET_ref
       ((update_list_inc w__2 (( 0 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.CCSIDR-L1D_override'')))) then
     read_reg DCACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__3 :: ( 64 Word.word) list) . 
     write_reg
       DCACHE_CCSIDR_RESET_ref
       ((update_list_inc w__3 (( 0 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.CCSIDR-L2_override'')))) then
     read_reg DCACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__4 :: ( 64 Word.word) list) . 
     write_reg
       DCACHE_CCSIDR_RESET_ref
       ((update_list_inc w__4 (( 1 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.CCSIDR-L3_override'')))) then
     read_reg DCACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__5 :: ( 64 Word.word) list) . 
     write_reg
       DCACHE_CCSIDR_RESET_ref
       ((update_list_inc w__5 (( 2 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.CCSIDR-L4_override'')))) then
     read_reg DCACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__6 :: ( 64 Word.word) list) . 
     write_reg
       DCACHE_CCSIDR_RESET_ref
       ((update_list_inc w__6 (( 3 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.CCSIDR-L5_override'')))) then
     read_reg DCACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__7 :: ( 64 Word.word) list) . 
     write_reg
       DCACHE_CCSIDR_RESET_ref
       ((update_list_inc w__7 (( 4 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.CCSIDR-L6_override'')))) then
     read_reg DCACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__8 :: ( 64 Word.word) list) . 
     write_reg
       DCACHE_CCSIDR_RESET_ref
       ((update_list_inc w__8 (( 5 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.CCSIDR-L7_override'')))) then
     read_reg DCACHE_CCSIDR_RESET_ref \<bind> ((\<lambda> (w__9 :: ( 64 Word.word) list) . 
     write_reg
       DCACHE_CCSIDR_RESET_ref
       ((update_list_inc w__9 (( 6 :: int)::ii) ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
          :: ( 64 Word.word) list))))
   else if (((arg1 = (''cpu.cpu0.DCZID-log2-block-size'')))) then
     write_reg dczid_log2_block_size_ref value_name
   else if (((arg1 = (''cpu.GMID-log2-block-size'')))) then
     write_reg gmid_log2_block_size_ref value_name
   else if (((arg1 = (''exclusive_monitor.log2_granule_size'')))) then
     write_reg
       exclusive_granule_size_ref
       ((integer_subrange value_name (( 3 :: int)::ii) (( 0 :: int)::ii)  ::  4 Word.word))
   else if (((arg1 = (''cpu.unpred_tsize_aborts'')))) then
     write_reg unpred_tsize_aborts_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.CONFIG64'')))) then
     write_reg CFG_RMR_AA64_ref (vec_of_bits [integer_access value_name (( 0 :: int)::ii)]  ::  1 Word.word)
   else if (((arg1 = (''cpu.cpu0.RVBAR'')))) then
     write_reg CFG_RVBAR_ref ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
   else if (((arg1 = (''cpu.VAL_ignore_rvbar_in_aarch32'')))) then
     write_reg ignore_rvbar_in_aarch32_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_tlb'')))) then write_reg tlb_enabled_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.has_trickbox'')))) then
     write_reg trickbox_enabled_ref (((value_name = (( 1 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.MPIDR-override'')))) then
     write_reg CFG_MPIDR_ref ((integer_subrange value_name (( 31 :: int)::ii) (( 0 :: int)::ii)  ::  32 Word.word))
   else if (((arg1 = (''cpu.cpu0.semihosting-heap_base'')))) then
     write_reg HEAP_BASE_ref ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
   else if (((arg1 = (''cpu.cpu0.semihosting-heap_limit'')))) then
     write_reg HEAP_LIMIT_ref ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
   else if (((arg1 = (''cpu.cpu0.semihosting-stack_base'')))) then
     write_reg STACK_BASE_ref ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
   else if (((arg1 = (''cpu.cpu0.semihosting-stack_limit'')))) then
     write_reg STACK_LIMIT_ref ((integer_subrange value_name (( 63 :: int)::ii) (( 0 :: int)::ii)  ::  64 Word.word))
   else if (((arg1 = (''cpu.has_qarma3_pac'')))) then
     write_reg pacqarma3_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.has_const_pac'')))) then
     write_reg pac_frac_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.has_rme'')))) then write_reg rme_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.rme_l0pgtsz'')))) then
     write_reg rme_l0gptsz_ref ((integer_subrange value_name (( 3 :: int)::ii) (( 0 :: int)::ii)  ::  4 Word.word))
   else if (((arg1 = (''cpu.has_brbe'')))) then write_reg brbe_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.cpu0.number-of-branch-records'')))) then
     write_reg num_brb_records_ref (((( 16 :: int)::ii) * ((value_name div (( 16 :: int)::ii)))))
   else if (((arg1 = (''cpu.isb_is_branch'')))) then
     write_reg isb_is_branch_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''cpu.has_brbe_v9_3'')))) then
     write_reg brbev1p1_implemented_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''SVE.ScalableVectorExtension.has_sme_f64f64'')))) then
     write_reg has_sme_f64f64_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''SVE.ScalableVectorExtension.has_sme_priority_control'')))) then
     write_reg has_sme_priority_control_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''SVE.ScalableVectorExtension.has_sme_i16i64'')))) then
     write_reg has_sme_i16i64_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''SVE.ScalableVectorExtension.sme_veclens_implemented'')))) then
     write_reg
       max_implemented_smeveclen_ref
       ((decode_maxveclen ((Word.uint ((integer_subrange value_name (( 7 :: int)::ii) (( 0 :: int)::ii)  ::  8 Word.word))))))
   else if (((arg1 = (''SVE.ScalableVectorExtension.has_sve_extended_bf16'')))) then
     write_reg
       has_sve_extended_bf16_ref
       ((Word.uint ((integer_subrange value_name (( 1 :: int)::ii) (( 0 :: int)::ii)  ::  2 Word.word))))
   else if (((arg1 = (''SVE.ScalableVectorExtension.has_sme'')))) then
     write_reg has_sme_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else if (((arg1 = (''SVE.ScalableVectorExtension.sme_only'')))) then
     write_reg sme_only_ref (((value_name \<noteq> (( 0 :: int)::ii))))
   else return ()  )\<close> 
  for  "arg1"  :: " string " 
  and  "value_name"  :: " int "


definition ListConfig  :: \<open> unit \<Rightarrow> unit \<close>  where 
     \<open> ListConfig _ = ( ()  )\<close>


definition StartTrackingTransactionalReadsWrites  :: \<open> unit \<Rightarrow> unit \<close>  where 
     \<open> StartTrackingTransactionalReadsWrites _ = ( ()  )\<close>


\<comment> \<open>\<open>val initialize_registers : unit -> M unit\<close>\<close>

definition initialize_registers  :: \<open> unit \<Rightarrow>((register_value),(unit),(exception))monad \<close>  where 
     \<open> initialize_registers _ = (
   undefined_int instance_Sail2_values_Register_Value_Armv9_types_register_value_dict ()  \<bind> ((\<lambda> (w__0 :: ii) . 
   (write_reg SEE_ref w__0 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__1 ::  64 Word.word) . 
   (write_reg FPCR_ref w__1 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__2 ::  64 Word.word) . 
   (write_reg FPSR_ref w__2 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__3 ::  32 Word.word) . 
   (write_reg RVBAR_ref w__3 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__4 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__4  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__5 :: ( 64 Word.word) list) . 
   (write_reg ERRnFR_ref w__5 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 8 :: int)::ii)  :: ( 8 Word.word) M)) \<bind> ((\<lambda> (w__6 ::  8 Word.word) . 
   (write_reg claim_tags_ref w__6 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__7 ::  32 Word.word) . 
   (write_reg trcclaim_tags_ref w__7 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__8 ::  64 Word.word) . 
   (write_reg HCR_EL2_ref w__8 \<then>
   undefined_ProcState () ) \<bind> ((\<lambda> (w__9 :: ProcState) . 
   (write_reg PSTATE_ref w__9 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__10 ::  64 Word.word) . 
   (write_reg SCR_EL3_ref w__10 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__11 ::  32 Word.word) . 
   (write_reg SCR_ref w__11 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__12 ::  64 Word.word) . 
   (write_reg HCRX_EL2_ref w__12 \<then>
   undefined_int instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__13 :: ii) . 
   (write_reg cycle_count_ref w__13 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__14 ::  64 Word.word) . 
   (write_reg CLIDR_EL1_ref w__14 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__15 ::  64 Word.word) . 
   (undefined_vector (( 7 :: int)::ii) w__15  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__16 :: ( 64 Word.word) list) . 
   (write_reg DCACHE_CCSIDR_RESET_ref w__16 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__17 ::  64 Word.word) . 
   (undefined_vector (( 7 :: int)::ii) w__17  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__18 :: ( 64 Word.word) list) . 
   (write_reg ICACHE_CCSIDR_RESET_ref w__18 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__19 ::  64 Word.word) . 
   (undefined_vector (( 31 :: int)::ii) w__19  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__20 :: ( 64 Word.word) list) . 
   (write_reg R_ref w__20 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__21 ::  64 Word.word) . 
   (write_reg ESR_EL1_ref w__21 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__22 ::  64 Word.word) . 
   (write_reg ESR_EL2_ref w__22 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__23 ::  64 Word.word) . 
   (write_reg ESR_EL3_ref w__23 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__24 ::  64 Word.word) . 
   (write_reg FAR_EL1_ref w__24 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__25 ::  64 Word.word) . 
   (write_reg FAR_EL2_ref w__25 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__26 ::  64 Word.word) . 
   (write_reg FAR_EL3_ref w__26 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__27 ::  64 Word.word) . 
   (write_reg HPFAR_EL2_ref w__27 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__28 ::  64 Word.word) . 
   (write_reg MFAR_EL3_ref w__28 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__29 ::  64 Word.word) . 
   (write_reg BRBCR_EL1_ref w__29 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__30 ::  64 Word.word) . 
   (write_reg BRBCR_EL2_ref w__30 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__31 ::  64 Word.word) . 
   (write_reg BRBFCR_EL1_ref w__31 \<then>
   undefined_int instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__32 :: ii) . 
   (write_reg last_cycle_count_ref w__32 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__33 :: bool) . 
   (write_reg last_branch_valid_ref w__33 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__34 ::  64 Word.word) . 
   (write_reg MDCR_EL3_ref w__34 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__35 ::  64 Word.word) . 
   (write_reg MDCR_EL2_ref w__35 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__36 ::  64 Word.word) . 
   (write_reg PMCR_EL0_ref w__36 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__37 ::  64 Word.word) . 
   (undefined_vector (( 31 :: int)::ii) w__37  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__38 :: ( 64 Word.word) list) . 
   (write_reg PMEVTYPER_EL0_ref w__38 \<then>
   undefined_int instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__39 :: ii) . 
   undefined_vector (( 31 :: int)::ii) w__39 \<bind> ((\<lambda> (w__40 :: ii list) . 
   (write_reg PMUEventAccumulator_ref w__40 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__41 ::  64 Word.word) . 
   (write_reg ICC_PMR_EL1_ref w__41 \<then>
   undefined_TMState () ) \<bind> ((\<lambda> (w__42 :: TMState) . 
   (write_reg TSTATE_ref w__42 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__43 ::  64 Word.word) . 
   (write_reg BRBIDR0_EL1_ref w__43 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__44 ::  64 Word.word) . 
   (undefined_vector (( 64 :: int)::ii) w__44  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__45 :: ( 64 Word.word) list) . 
   (write_reg Records_INF_ref w__45 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__46 ::  64 Word.word) . 
   (undefined_vector (( 64 :: int)::ii) w__46  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__47 :: ( 64 Word.word) list) . 
   (write_reg Records_SRC_ref w__47 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__48 ::  64 Word.word) . 
   (undefined_vector (( 64 :: int)::ii) w__48  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__49 :: ( 64 Word.word) list) . 
   (write_reg Records_TGT_ref w__49 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__50 ::  64 Word.word) . 
   (write_reg TCR_EL1_ref w__50 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__51 ::  64 Word.word) . 
   (write_reg TCR_EL2_ref w__51 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__52 ::  64 Word.word) . 
   (write_reg TCR_EL3_ref w__52 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__53 ::  32 Word.word) . 
   (write_reg LR_mon_ref w__53 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__54 ::  32 Word.word) . 
   (write_reg SP_mon_ref w__54 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__55 ::  64 Word.word) . 
   (write_reg PC_ref w__55 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__56 :: bool) . 
   (write_reg BranchTaken_ref w__56 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__57 ::  64 Word.word) . 
   (write_reg OSECCR_EL1_ref w__57 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__58 ::  64 Word.word) . 
   (write_reg DLR_EL0_ref w__58 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__59 ::  64 Word.word) . 
   (write_reg DSPSR_EL0_ref w__59 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__60 ::  64 Word.word) . 
   (write_reg MDCCSR_EL0_ref w__60 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 29 :: int)::ii)  :: ( 29 Word.word) M)) \<bind> ((\<lambda> (w__61 ::  29 Word.word) . 
   (write_reg EDSCR_0_28_ref w__61 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 1 :: int)::ii)  :: ( 1 Word.word) M)) \<bind> ((\<lambda> (w__62 ::  1 Word.word) . 
   (write_reg EDSCR_31_31_ref w__62 \<then>
   undefined_signal () ) \<bind> ((\<lambda> (w__63 :: signal) . 
   (write_reg DBGEN_ref w__63 \<then>
   undefined_signal () ) \<bind> ((\<lambda> (w__64 :: signal) . 
   (write_reg SPIDEN_ref w__64 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__65 ::  64 Word.word) . 
   (write_reg OSDLR_EL1_ref w__65 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__66 ::  64 Word.word) . 
   (write_reg DBGPRCR_EL1_ref w__66 \<then>
   undefined_signal () ) \<bind> ((\<lambda> (w__67 :: signal) . 
   (write_reg RLPIDEN_ref w__67 \<then>
   undefined_signal () ) \<bind> ((\<lambda> (w__68 :: signal) . 
   (write_reg RTPIDEN_ref w__68 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__69 ::  64 Word.word) . 
   (write_reg ELR_EL1_ref w__69 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__70 ::  64 Word.word) . 
   (write_reg ELR_EL2_ref w__70 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__71 ::  64 Word.word) . 
   (write_reg ELR_EL3_ref w__71 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__72 ::  64 Word.word) . 
   (write_reg ZCR_EL1_ref w__72 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__73 ::  64 Word.word) . 
   (write_reg ZCR_EL2_ref w__73 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__74 ::  64 Word.word) . 
   (write_reg ZCR_EL3_ref w__74 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__75 ::  64 Word.word) . 
   (write_reg SMCR_EL1_ref w__75 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__76 ::  64 Word.word) . 
   (write_reg SMCR_EL2_ref w__76 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__77 ::  64 Word.word) . 
   (write_reg SMCR_EL3_ref w__77 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 256 :: int)::ii)  :: ( 256 Word.word) M)) \<bind> ((\<lambda> (w__78 ::  256 Word.word) . 
   (write_reg FFR_ref w__78 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__79 ::  64 Word.word) . 
   (write_reg CPACR_EL1_ref w__79 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__80 ::  64 Word.word) . 
   (write_reg CPTR_EL2_ref w__80 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__81 ::  64 Word.word) . 
   (write_reg CPTR_EL3_ref w__81 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__82 ::  32 Word.word) . 
   (write_reg NSACR_ref w__82 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 256 :: int)::ii)  :: ( 256 Word.word) M)) \<bind> ((\<lambda> (w__83 ::  256 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__83  :: ( ( 256 Word.word)list) M) \<bind> ((\<lambda> (w__84 :: ( 256 Word.word) list) . 
   (write_reg P_ref w__84 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__85 ::  64 Word.word) . 
   (write_reg SP_EL0_ref w__85 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__86 ::  64 Word.word) . 
   (write_reg SP_EL1_ref w__86 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__87 ::  64 Word.word) . 
   (write_reg SP_EL2_ref w__87 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__88 ::  64 Word.word) . 
   (write_reg SP_EL3_ref w__88 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 2048 :: int)::ii)  :: ( 2048 Word.word) M)) \<bind> ((\<lambda> (w__89 ::  2048 Word.word) . 
   (undefined_vector (( 32 :: int)::ii) w__89  :: ( ( 2048 Word.word)list) M) \<bind> ((\<lambda> (w__90 :: ( 2048 Word.word) list) . 
   (write_reg Z_ref w__90 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 2048 :: int)::ii)  :: ( 2048 Word.word) M)) \<bind> ((\<lambda> (w__91 ::  2048 Word.word) . 
   (undefined_vector (( 256 :: int)::ii) w__91  :: ( ( 2048 Word.word)list) M) \<bind> ((\<lambda> (w__92 :: ( 2048 Word.word) list) . 
   (write_reg ZA_ref w__92 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__93 ::  64 Word.word) . 
   (write_reg SCTLR_EL1_ref w__93 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__94 ::  64 Word.word) . 
   (write_reg SCTLR_EL2_ref w__94 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__95 ::  64 Word.word) . 
   (write_reg SCTLR_EL3_ref w__95 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__96 ::  32 Word.word) . 
   (write_reg SCTLR_S_ref w__96 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__97 ::  64 Word.word) . 
   (write_reg SPSR_EL1_ref w__97 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__98 ::  64 Word.word) . 
   (write_reg SPSR_EL2_ref w__98 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__99 ::  64 Word.word) . 
   (write_reg SPSR_EL3_ref w__99 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__100 ::  64 Word.word) . 
   (write_reg SPSR_abt_ref w__100 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__101 ::  64 Word.word) . 
   (write_reg SPSR_fiq_ref w__101 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__102 ::  64 Word.word) . 
   (write_reg SPSR_irq_ref w__102 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__103 ::  32 Word.word) . 
   (write_reg SPSR_mon_ref w__103 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__104 ::  64 Word.word) . 
   (write_reg SPSR_und_ref w__104 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__105 ::  64 Word.word) . 
   (write_reg VBAR_EL1_ref w__105 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__106 ::  64 Word.word) . 
   (write_reg VBAR_EL2_ref w__106 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__107 ::  64 Word.word) . 
   (write_reg VBAR_EL3_ref w__107 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__108 ::  32 Word.word) . 
   (write_reg VBAR_S_ref w__108 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__109 ::  64 Word.word) . 
   (write_reg ACCDATA_EL1_ref w__109 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__110 ::  64 Word.word) . 
   (write_reg HFGRTR_EL2_ref w__110 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__111 ::  64 Word.word) . 
   (write_reg ACTLR_EL1_ref w__111 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__112 ::  32 Word.word) . 
   (write_reg MVBAR_ref w__112 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__113 ::  32 Word.word) . 
   (write_reg DFSR_S_ref w__113 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__114 ::  64 Word.word) . 
   (write_reg IFSR32_EL2_ref w__114 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__115 ::  32 Word.word) . 
   (write_reg IFSR_S_ref w__115 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__116 ::  32 Word.word) . 
   (write_reg TTBCR_S_ref w__116 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__117 ::  64 Word.word) . 
   (write_reg MDSCR_EL1_ref w__117 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 13 :: int)::ii)  :: ( 13 Word.word) M)) \<bind> ((\<lambda> (w__118 ::  13 Word.word) . 
   (write_reg DBGDSCRint_16_28_ref w__118 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__119 ::  64 Word.word) . 
   (write_reg TFSRE0_EL1_ref w__119 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__120 ::  64 Word.word) . 
   (write_reg TFSR_EL1_ref w__120 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__121 ::  64 Word.word) . 
   (write_reg TFSR_EL2_ref w__121 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__122 ::  64 Word.word) . 
   (write_reg TFSR_EL3_ref w__122 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__123 ::  64 Word.word) . 
   (write_reg CONTEXTIDR_EL1_ref w__123 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__124 ::  64 Word.word) . 
   (write_reg CONTEXTIDR_EL2_ref w__124 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__125 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__125  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__126 :: ( 64 Word.word) list) . 
   (write_reg DBGBCR_EL1_ref w__126 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__127 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__127  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__128 :: ( 64 Word.word) list) . 
   (write_reg DBGBVR_EL1_ref w__128 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__129 ::  64 Word.word) . 
   (write_reg VTCR_EL2_ref w__129 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__130 ::  64 Word.word) . 
   (write_reg VTTBR_EL2_ref w__130 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__131 ::  64 Word.word) . 
   (write_reg OSLSR_EL1_ref w__131 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__132 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__132  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__133 :: ( 64 Word.word) list) . 
   (write_reg DBGWCR_EL1_ref w__133 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__134 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__134  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__135 :: ( 64 Word.word) list) . 
   (write_reg DBGWVR_EL1_ref w__135 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__136 ::  64 Word.word) . 
   (write_reg EDWAR_ref w__136 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__137 ::  64 Word.word) . 
   (write_reg SDER32_EL2_ref w__137 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__138 ::  64 Word.word) . 
   (write_reg MAIR_EL1_ref w__138 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__139 ::  64 Word.word) . 
   (write_reg MAIR_EL2_ref w__139 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__140 ::  64 Word.word) . 
   (write_reg MAIR_EL3_ref w__140 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__141 ::  64 Word.word) . 
   (write_reg MPAM3_EL3_ref w__141 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 63 :: int)::ii)  :: ( 63 Word.word) M)) \<bind> ((\<lambda> (w__142 ::  63 Word.word) . 
   (write_reg MPAM2_EL2_0_62_ref w__142 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__143 ::  64 Word.word) . 
   (write_reg MPAMIDR_EL1_ref w__143 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 63 :: int)::ii)  :: ( 63 Word.word) M)) \<bind> ((\<lambda> (w__144 ::  63 Word.word) . 
   (write_reg MPAM1_EL1_0_62_ref w__144 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__145 ::  64 Word.word) . 
   (write_reg MPAMHCR_EL2_ref w__145 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__146 ::  64 Word.word) . 
   (write_reg MPAMVPM0_EL2_ref w__146 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__147 ::  64 Word.word) . 
   (write_reg MPAMVPMV_EL2_ref w__147 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__148 ::  64 Word.word) . 
   (write_reg MPAMVPM1_EL2_ref w__148 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__149 ::  64 Word.word) . 
   (write_reg MPAMVPM2_EL2_ref w__149 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__150 ::  64 Word.word) . 
   (write_reg MPAMVPM3_EL2_ref w__150 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__151 ::  64 Word.word) . 
   (write_reg MPAMVPM4_EL2_ref w__151 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__152 ::  64 Word.word) . 
   (write_reg MPAMVPM5_EL2_ref w__152 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__153 ::  64 Word.word) . 
   (write_reg MPAMVPM6_EL2_ref w__153 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__154 ::  64 Word.word) . 
   (write_reg MPAMVPM7_EL2_ref w__154 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__155 ::  64 Word.word) . 
   (write_reg MPAM0_EL1_ref w__155 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__156 ::  64 Word.word) . 
   (write_reg MPAMSM_EL1_ref w__156 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__157 ::  64 Word.word) . 
   (write_reg GPCCR_EL3_ref w__157 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__158 ::  64 Word.word) . 
   (write_reg GPTBR_EL3_ref w__158 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__159 :: bool) . 
   (write_reg InGuardedPage_ref w__159 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__160 ::  64 Word.word) . 
   (write_reg TTBR0_EL1_ref w__160 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__161 ::  64 Word.word) . 
   (write_reg TTBR1_EL1_ref w__161 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__162 ::  64 Word.word) . 
   (write_reg TTBR0_EL2_ref w__162 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__163 ::  64 Word.word) . 
   (write_reg TTBR1_EL2_ref w__163 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__164 ::  64 Word.word) . 
   (write_reg TTBR0_EL3_ref w__164 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__165 ::  64 Word.word) . 
   (write_reg VSTCR_EL2_ref w__165 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__166 ::  64 Word.word) . 
   (write_reg VSTTBR_EL2_ref w__166 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__167 ::  64 Word.word) . 
   (write_reg VNCR_EL2_ref w__167 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__168 ::  64 Word.word) . 
   (write_reg ACTLR_EL2_ref w__168 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__169 ::  64 Word.word) . 
   (write_reg ACTLR_EL3_ref w__169 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__170 ::  64 Word.word) . 
   (write_reg AFSR0_EL1_ref w__170 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__171 ::  64 Word.word) . 
   (write_reg AFSR0_EL2_ref w__171 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__172 ::  64 Word.word) . 
   (write_reg AFSR0_EL3_ref w__172 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__173 ::  64 Word.word) . 
   (write_reg AFSR1_EL1_ref w__173 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__174 ::  64 Word.word) . 
   (write_reg AFSR1_EL2_ref w__174 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__175 ::  64 Word.word) . 
   (write_reg AFSR1_EL3_ref w__175 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__176 ::  64 Word.word) . 
   (write_reg AIDR_EL1_ref w__176 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__177 ::  64 Word.word) . 
   (write_reg AMAIR_EL1_ref w__177 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__178 ::  64 Word.word) . 
   (write_reg AMAIR_EL2_ref w__178 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__179 ::  64 Word.word) . 
   (write_reg AMAIR_EL3_ref w__179 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__180 ::  64 Word.word) . 
   (write_reg AMCFGR_EL0_ref w__180 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__181 ::  64 Word.word) . 
   (write_reg AMUSERENR_EL0_ref w__181 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__182 ::  64 Word.word) . 
   (write_reg AMCG1IDR_EL0_ref w__182 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__183 ::  64 Word.word) . 
   (write_reg AMCGCR_EL0_ref w__183 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__184 ::  64 Word.word) . 
   (write_reg AMCNTENCLR0_EL0_ref w__184 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__185 ::  64 Word.word) . 
   (write_reg HAFGRTR_EL2_ref w__185 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__186 ::  64 Word.word) . 
   (write_reg AMCNTENCLR1_EL0_ref w__186 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__187 ::  64 Word.word) . 
   (write_reg AMCNTENSET0_EL0_ref w__187 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__188 ::  64 Word.word) . 
   (write_reg AMCNTENSET1_EL0_ref w__188 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__189 ::  64 Word.word) . 
   (write_reg AMCR_EL0_ref w__189 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__190 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__190  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__191 :: ( 64 Word.word) list) . 
   (write_reg AMEVCNTR0_ref w__191 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__192 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__192  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__193 :: ( 64 Word.word) list) . 
   (write_reg AMEVCNTR1_EL0_ref w__193 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__194 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__194  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__195 :: ( 64 Word.word) list) . 
   (write_reg AMEVCNTVOFF0_EL2_ref w__195 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__196 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__196  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__197 :: ( 64 Word.word) list) . 
   (write_reg AMEVCNTVOFF1_EL2_ref w__197 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__198 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__198  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__199 :: ( 64 Word.word) list) . 
   (write_reg AMEVTYPER0_EL0_ref w__199 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__200 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__200  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__201 :: ( 64 Word.word) list) . 
   (write_reg AMEVTYPER1_EL0_ref w__201 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__202 ::  64 Word.word) . 
   (write_reg APDAKeyHi_EL1_ref w__202 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__203 ::  64 Word.word) . 
   (write_reg APDAKeyLo_EL1_ref w__203 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__204 ::  64 Word.word) . 
   (write_reg APDBKeyHi_EL1_ref w__204 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__205 ::  64 Word.word) . 
   (write_reg APDBKeyLo_EL1_ref w__205 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__206 ::  64 Word.word) . 
   (write_reg APGAKeyHi_EL1_ref w__206 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__207 ::  64 Word.word) . 
   (write_reg APGAKeyLo_EL1_ref w__207 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__208 ::  64 Word.word) . 
   (write_reg APIAKeyHi_EL1_ref w__208 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__209 ::  64 Word.word) . 
   (write_reg APIAKeyLo_EL1_ref w__209 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__210 ::  64 Word.word) . 
   (write_reg APIBKeyHi_EL1_ref w__210 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__211 ::  64 Word.word) . 
   (write_reg APIBKeyLo_EL1_ref w__211 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__212 ::  64 Word.word) . 
   (write_reg HDFGRTR_EL2_ref w__212 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__213 ::  64 Word.word) . 
   (write_reg BRBINFINJ_EL1_ref w__213 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__214 ::  64 Word.word) . 
   (undefined_vector (( 32 :: int)::ii) w__214  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__215 :: ( 64 Word.word) list) . 
   (write_reg BRBINF_EL1_ref w__215 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__216 ::  64 Word.word) . 
   (write_reg BRBSRCINJ_EL1_ref w__216 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__217 ::  64 Word.word) . 
   (undefined_vector (( 32 :: int)::ii) w__217  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__218 :: ( 64 Word.word) list) . 
   (write_reg BRBSRC_EL1_ref w__218 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__219 ::  64 Word.word) . 
   (write_reg BRBTGTINJ_EL1_ref w__219 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__220 ::  64 Word.word) . 
   (undefined_vector (( 32 :: int)::ii) w__220  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__221 :: ( 64 Word.word) list) . 
   (write_reg BRBTGT_EL1_ref w__221 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__222 ::  64 Word.word) . 
   (write_reg BRBTS_EL1_ref w__222 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__223 ::  64 Word.word) . 
   (write_reg CCSIDR2_EL1_ref w__223 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__224 ::  64 Word.word) . 
   (write_reg CCSIDR_EL1_ref w__224 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__225 ::  64 Word.word) . 
   (write_reg CNTFRQ_EL0_ref w__225 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__226 ::  64 Word.word) . 
   (write_reg CNTHCTL_EL2_ref w__226 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__227 ::  64 Word.word) . 
   (write_reg CNTKCTL_EL1_ref w__227 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__228 ::  64 Word.word) . 
   (write_reg CNTHPS_CTL_EL2_ref w__228 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__229 ::  64 Word.word) . 
   (write_reg CNTHPS_CVAL_EL2_ref w__229 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__230 ::  64 Word.word) . 
   (write_reg CNTHP_CTL_EL2_ref w__230 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__231 ::  64 Word.word) . 
   (write_reg CNTHP_CVAL_EL2_ref w__231 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__232 ::  64 Word.word) . 
   (write_reg CNTPOFF_EL2_ref w__232 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__233 ::  64 Word.word) . 
   (write_reg CNTP_CTL_EL0_ref w__233 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__234 ::  64 Word.word) . 
   (write_reg CNTP_CVAL_EL0_ref w__234 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 88 :: int)::ii)  :: ( 88 Word.word) M)) \<bind> ((\<lambda> (w__235 ::  88 Word.word) . 
   (write_reg PhysicalCount_ref w__235 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__236 ::  64 Word.word) . 
   (write_reg CNTHVS_CTL_EL2_ref w__236 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__237 ::  64 Word.word) . 
   (write_reg CNTHV_CTL_EL2_ref w__237 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__238 ::  64 Word.word) . 
   (write_reg CNTV_CTL_EL0_ref w__238 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__239 ::  64 Word.word) . 
   (write_reg CNTHVS_CVAL_EL2_ref w__239 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__240 ::  64 Word.word) . 
   (write_reg CNTHV_CVAL_EL2_ref w__240 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__241 ::  64 Word.word) . 
   (write_reg CNTV_CVAL_EL0_ref w__241 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__242 ::  64 Word.word) . 
   (write_reg CNTVOFF_EL2_ref w__242 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__243 ::  64 Word.word) . 
   (write_reg CNTPS_CTL_EL1_ref w__243 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__244 ::  64 Word.word) . 
   (write_reg CNTPS_CVAL_EL1_ref w__244 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__245 ::  64 Word.word) . 
   (write_reg CSSELR_EL1_ref w__245 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__246 ::  64 Word.word) . 
   (write_reg CTR_EL0_ref w__246 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__247 ::  64 Word.word) . 
   (write_reg DACR32_EL2_ref w__247 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__248 ::  64 Word.word) . 
   (write_reg DBGAUTHSTATUS_EL1_ref w__248 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__249 ::  64 Word.word) . 
   (write_reg DBGCLAIMCLR_EL1_ref w__249 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__250 ::  64 Word.word) . 
   (write_reg DBGCLAIMSET_EL1_ref w__250 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__251 ::  64 Word.word) . 
   (write_reg DBGDTRRX_EL0_ref w__251 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__252 ::  64 Word.word) . 
   (write_reg DBGDTR_EL0_ref w__252 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__253 ::  64 Word.word) . 
   (write_reg DBGVCR32_EL2_ref w__253 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__254 ::  64 Word.word) . 
   (write_reg DCZID_EL0_ref w__254 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__255 ::  64 Word.word) . 
   (write_reg ERRIDR_EL1_ref w__255 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__256 ::  64 Word.word) . 
   (write_reg ERRSELR_EL1_ref w__256 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__257 ::  64 Word.word) . 
   (write_reg ERXADDR_EL1_ref w__257 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__258 ::  64 Word.word) . 
   (write_reg ERXCTLR_EL1_ref w__258 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__259 ::  64 Word.word) . 
   (write_reg ERXFR_EL1_ref w__259 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__260 ::  64 Word.word) . 
   (write_reg ERXMISC0_EL1_ref w__260 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__261 ::  64 Word.word) . 
   (write_reg ERXMISC1_EL1_ref w__261 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__262 ::  64 Word.word) . 
   (write_reg ERXMISC2_EL1_ref w__262 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__263 ::  64 Word.word) . 
   (write_reg ERXMISC3_EL1_ref w__263 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__264 ::  64 Word.word) . 
   (write_reg ERXPFGCDN_EL1_ref w__264 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__265 ::  64 Word.word) . 
   (write_reg ERXPFGCTL_EL1_ref w__265 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__266 ::  64 Word.word) . 
   (write_reg ERXPFGF_EL1_ref w__266 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__267 ::  64 Word.word) . 
   (write_reg ERXSTATUS_EL1_ref w__267 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__268 ::  64 Word.word) . 
   (write_reg FPEXC32_EL2_ref w__268 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__269 ::  64 Word.word) . 
   (write_reg GCR_EL1_ref w__269 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__270 ::  64 Word.word) . 
   (write_reg GMID_EL1_ref w__270 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__271 ::  64 Word.word) . 
   (write_reg HACR_EL2_ref w__271 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__272 ::  64 Word.word) . 
   (write_reg HDFGWTR_EL2_ref w__272 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__273 ::  64 Word.word) . 
   (write_reg HFGITR_EL2_ref w__273 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__274 ::  64 Word.word) . 
   (write_reg HFGWTR_EL2_ref w__274 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__275 ::  64 Word.word) . 
   (write_reg HSTR_EL2_ref w__275 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__276 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__276  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__277 :: ( 64 Word.word) list) . 
   (write_reg ICC_AP0R_EL1_ref w__277 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__278 ::  64 Word.word) . 
   (write_reg ICC_SRE_EL1_NS_ref w__278 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__279 ::  64 Word.word) . 
   (write_reg ICC_SRE_EL1_S_ref w__279 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__280 ::  64 Word.word) . 
   (write_reg ICC_SRE_EL2_ref w__280 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__281 ::  64 Word.word) . 
   (write_reg ICC_SRE_EL3_ref w__281 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__282 ::  64 Word.word) . 
   (write_reg ICH_HCR_EL2_ref w__282 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__283 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__283  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__284 :: ( 64 Word.word) list) . 
   (write_reg ICV_AP0R_EL1_ref w__284 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__285 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__285  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__286 :: ( 64 Word.word) list) . 
   (write_reg ICC_AP1R_EL1_NS_ref w__286 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__287 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__287  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__288 :: ( 64 Word.word) list) . 
   (write_reg ICC_AP1R_EL1_S_ref w__288 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__289 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__289  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__290 :: ( 64 Word.word) list) . 
   (write_reg ICV_AP1R_EL1_ref w__290 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__291 ::  64 Word.word) . 
   (write_reg ICC_BPR0_EL1_ref w__291 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__292 ::  64 Word.word) . 
   (write_reg ICV_BPR0_EL1_ref w__292 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__293 ::  64 Word.word) . 
   (write_reg ICC_CTLR_EL1_NS_ref w__293 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__294 ::  64 Word.word) . 
   (write_reg ICC_CTLR_EL1_S_ref w__294 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__295 ::  64 Word.word) . 
   (write_reg ICV_CTLR_EL1_ref w__295 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__296 ::  64 Word.word) . 
   (write_reg ICC_CTLR_EL3_ref w__296 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__297 ::  64 Word.word) . 
   (write_reg ICC_HPPIR0_EL1_ref w__297 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__298 ::  64 Word.word) . 
   (write_reg ICV_HPPIR0_EL1_ref w__298 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__299 ::  64 Word.word) . 
   (write_reg ICC_HPPIR1_EL1_ref w__299 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__300 ::  64 Word.word) . 
   (write_reg ICV_HPPIR1_EL1_ref w__300 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__301 ::  64 Word.word) . 
   (write_reg ICC_IAR0_EL1_ref w__301 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__302 ::  64 Word.word) . 
   (write_reg ICV_IAR0_EL1_ref w__302 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__303 ::  64 Word.word) . 
   (write_reg ICC_IAR1_EL1_ref w__303 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__304 ::  64 Word.word) . 
   (write_reg ICV_IAR1_EL1_ref w__304 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__305 ::  64 Word.word) . 
   (write_reg ICC_IGRPEN0_EL1_ref w__305 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__306 ::  64 Word.word) . 
   (write_reg ICV_IGRPEN0_EL1_ref w__306 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__307 ::  64 Word.word) . 
   (write_reg ICC_IGRPEN1_EL1_NS_ref w__307 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__308 ::  64 Word.word) . 
   (write_reg ICC_IGRPEN1_EL1_S_ref w__308 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__309 ::  64 Word.word) . 
   (write_reg ICV_IGRPEN1_EL1_ref w__309 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__310 ::  64 Word.word) . 
   (write_reg ICC_IGRPEN1_EL3_ref w__310 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__311 ::  64 Word.word) . 
   (write_reg ICV_PMR_EL1_ref w__311 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__312 ::  64 Word.word) . 
   (write_reg ICC_RPR_EL1_ref w__312 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__313 ::  64 Word.word) . 
   (write_reg ICV_RPR_EL1_ref w__313 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__314 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__314  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__315 :: ( 64 Word.word) list) . 
   (write_reg ICH_AP0R_EL2_ref w__315 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__316 ::  64 Word.word) . 
   (undefined_vector (( 4 :: int)::ii) w__316  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__317 :: ( 64 Word.word) list) . 
   (write_reg ICH_AP1R_EL2_ref w__317 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__318 ::  64 Word.word) . 
   (write_reg ICH_EISR_EL2_ref w__318 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__319 ::  64 Word.word) . 
   (write_reg ICH_ELRSR_EL2_ref w__319 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__320 ::  64 Word.word) . 
   (undefined_vector (( 16 :: int)::ii) w__320  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__321 :: ( 64 Word.word) list) . 
   (write_reg ICH_LR_EL2_ref w__321 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__322 ::  64 Word.word) . 
   (write_reg ICH_MISR_EL2_ref w__322 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__323 ::  64 Word.word) . 
   (write_reg ICH_VMCR_EL2_ref w__323 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__324 ::  64 Word.word) . 
   (write_reg ICH_VTR_EL2_ref w__324 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__325 ::  64 Word.word) . 
   (write_reg ICC_BPR1_EL1_NS_ref w__325 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__326 ::  64 Word.word) . 
   (write_reg ICC_BPR1_EL1_S_ref w__326 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__327 ::  64 Word.word) . 
   (write_reg ICV_BPR1_EL1_ref w__327 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__328 ::  64 Word.word) . 
   (write_reg ICC_NMIAR1_EL1_ref w__328 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__329 ::  64 Word.word) . 
   (write_reg ICV_NMIAR1_EL1_ref w__329 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__330 ::  64 Word.word) . 
   (write_reg ID_AA64AFR0_EL1_ref w__330 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__331 ::  64 Word.word) . 
   (write_reg ID_AA64AFR1_EL1_ref w__331 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__332 ::  64 Word.word) . 
   (write_reg ID_AA64DFR0_EL1_ref w__332 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__333 ::  64 Word.word) . 
   (write_reg ID_AA64DFR1_EL1_ref w__333 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__334 ::  64 Word.word) . 
   (write_reg ID_AA64ISAR0_EL1_ref w__334 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__335 ::  64 Word.word) . 
   (write_reg ID_AA64ISAR1_EL1_ref w__335 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__336 ::  64 Word.word) . 
   (write_reg ID_AA64ISAR2_EL1_ref w__336 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__337 ::  64 Word.word) . 
   (write_reg ID_AA64MMFR0_EL1_ref w__337 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__338 ::  64 Word.word) . 
   (write_reg ID_AA64MMFR1_EL1_ref w__338 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__339 ::  64 Word.word) . 
   (write_reg ID_AA64MMFR2_EL1_ref w__339 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__340 ::  64 Word.word) . 
   (write_reg ID_AA64PFR0_EL1_ref w__340 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__341 ::  64 Word.word) . 
   (write_reg ID_AA64PFR1_EL1_ref w__341 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__342 ::  64 Word.word) . 
   (write_reg ID_AA64SMFR0_EL1_ref w__342 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__343 ::  64 Word.word) . 
   (write_reg ID_AA64ZFR0_EL1_ref w__343 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__344 ::  64 Word.word) . 
   (write_reg ID_AFR0_EL1_ref w__344 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__345 ::  64 Word.word) . 
   (write_reg ID_DFR0_EL1_ref w__345 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__346 ::  64 Word.word) . 
   (write_reg ID_DFR1_EL1_ref w__346 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__347 ::  64 Word.word) . 
   (write_reg ID_ISAR0_EL1_ref w__347 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__348 ::  64 Word.word) . 
   (write_reg ID_ISAR1_EL1_ref w__348 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__349 ::  64 Word.word) . 
   (write_reg ID_ISAR2_EL1_ref w__349 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__350 ::  64 Word.word) . 
   (write_reg ID_ISAR3_EL1_ref w__350 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__351 ::  64 Word.word) . 
   (write_reg ID_ISAR4_EL1_ref w__351 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__352 ::  64 Word.word) . 
   (write_reg ID_ISAR5_EL1_ref w__352 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__353 ::  64 Word.word) . 
   (write_reg ID_ISAR6_EL1_ref w__353 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__354 ::  64 Word.word) . 
   (write_reg ID_MMFR0_EL1_ref w__354 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__355 ::  64 Word.word) . 
   (write_reg ID_MMFR1_EL1_ref w__355 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__356 ::  64 Word.word) . 
   (write_reg ID_MMFR2_EL1_ref w__356 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__357 ::  64 Word.word) . 
   (write_reg ID_MMFR3_EL1_ref w__357 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__358 ::  64 Word.word) . 
   (write_reg ID_MMFR4_EL1_ref w__358 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__359 ::  64 Word.word) . 
   (write_reg ID_MMFR5_EL1_ref w__359 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__360 ::  64 Word.word) . 
   (write_reg ID_PFR0_EL1_ref w__360 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__361 ::  64 Word.word) . 
   (write_reg ID_PFR1_EL1_ref w__361 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__362 ::  64 Word.word) . 
   (write_reg ID_PFR2_EL1_ref w__362 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__363 ::  64 Word.word) . 
   (write_reg ISR_EL1_ref w__363 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__364 ::  64 Word.word) . 
   (write_reg LORC_EL1_ref w__364 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__365 ::  64 Word.word) . 
   (write_reg LOREA_EL1_ref w__365 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__366 ::  64 Word.word) . 
   (write_reg LORID_EL1_ref w__366 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__367 ::  64 Word.word) . 
   (write_reg LORN_EL1_ref w__367 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__368 ::  64 Word.word) . 
   (write_reg LORSA_EL1_ref w__368 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__369 ::  64 Word.word) . 
   (write_reg MDCCINT_EL1_ref w__369 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__370 ::  64 Word.word) . 
   (write_reg MDRAR_EL1_ref w__370 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__371 ::  64 Word.word) . 
   (write_reg MIDR_EL1_ref w__371 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__372 ::  64 Word.word) . 
   (write_reg VPIDR_EL2_ref w__372 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__373 ::  64 Word.word) . 
   (write_reg MVFR0_EL1_ref w__373 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__374 ::  64 Word.word) . 
   (write_reg MVFR1_EL1_ref w__374 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__375 ::  64 Word.word) . 
   (write_reg MVFR2_EL1_ref w__375 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__376 ::  64 Word.word) . 
   (write_reg OSDTRRX_EL1_ref w__376 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__377 ::  64 Word.word) . 
   (write_reg OSDTRTX_EL1_ref w__377 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__378 ::  64 Word.word) . 
   (write_reg PAR_EL1_ref w__378 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__379 ::  64 Word.word) . 
   (write_reg PMBIDR_EL1_ref w__379 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__380 ::  64 Word.word) . 
   (write_reg PMBLIMITR_EL1_ref w__380 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__381 ::  64 Word.word) . 
   (write_reg PMBPTR_EL1_ref w__381 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__382 ::  64 Word.word) . 
   (write_reg PMBSR_EL1_ref w__382 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__383 ::  64 Word.word) . 
   (write_reg PMCCFILTR_EL0_ref w__383 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__384 ::  64 Word.word) . 
   (write_reg PMUSERENR_EL0_ref w__384 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__385 ::  64 Word.word) . 
   (write_reg PMCCNTR_EL0_ref w__385 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__386 ::  64 Word.word) . 
   (write_reg PMCEID0_EL0_ref w__386 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__387 ::  64 Word.word) . 
   (write_reg PMCEID1_EL0_ref w__387 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__388 ::  64 Word.word) . 
   (write_reg PMCNTENCLR_EL0_ref w__388 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__389 ::  64 Word.word) . 
   (write_reg PMCNTENSET_EL0_ref w__389 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__390 ::  64 Word.word) . 
   (undefined_vector (( 31 :: int)::ii) w__390  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__391 :: ( 64 Word.word) list) . 
   (write_reg PMEVCNTR_EL0_ref w__391 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__392 ::  64 Word.word) . 
   (write_reg PMINTENCLR_EL1_ref w__392 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__393 ::  64 Word.word) . 
   (write_reg PMINTENSET_EL1_ref w__393 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__394 ::  64 Word.word) . 
   (write_reg PMMIR_EL1_ref w__394 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__395 ::  64 Word.word) . 
   (write_reg PMOVSCLR_EL0_ref w__395 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__396 ::  64 Word.word) . 
   (write_reg PMOVSSET_EL0_ref w__396 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__397 ::  64 Word.word) . 
   (write_reg PMSCR_EL1_ref w__397 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__398 ::  64 Word.word) . 
   (write_reg PMSCR_EL2_ref w__398 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__399 ::  64 Word.word) . 
   (write_reg PMSELR_EL0_ref w__399 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__400 ::  64 Word.word) . 
   (write_reg PMSEVFR_EL1_ref w__400 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__401 ::  64 Word.word) . 
   (write_reg PMSFCR_EL1_ref w__401 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__402 ::  64 Word.word) . 
   (write_reg PMSICR_EL1_ref w__402 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__403 ::  64 Word.word) . 
   (write_reg PMSIDR_EL1_ref w__403 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__404 ::  64 Word.word) . 
   (write_reg PMSIRR_EL1_ref w__404 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__405 ::  64 Word.word) . 
   (write_reg PMSLATFR_EL1_ref w__405 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__406 ::  64 Word.word) . 
   (write_reg PMSNEVFR_EL1_ref w__406 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__407 ::  64 Word.word) . 
   (write_reg PMXEVCNTR_EL0_ref w__407 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__408 ::  64 Word.word) . 
   (write_reg PMXEVTYPER_EL0_ref w__408 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__409 ::  64 Word.word) . 
   (write_reg REVIDR_EL1_ref w__409 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__410 ::  64 Word.word) . 
   (write_reg RGSR_EL1_ref w__410 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__411 ::  64 Word.word) . 
   (write_reg RMR_EL1_ref w__411 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__412 ::  64 Word.word) . 
   (write_reg RMR_EL2_ref w__412 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__413 ::  64 Word.word) . 
   (write_reg RMR_EL3_ref w__413 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__414 ::  64 Word.word) . 
   (write_reg RNDRRS_ref w__414 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__415 ::  64 Word.word) . 
   (write_reg RNDR_ref w__415 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__416 ::  64 Word.word) . 
   (write_reg RVBAR_EL1_ref w__416 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__417 ::  64 Word.word) . 
   (write_reg RVBAR_EL2_ref w__417 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__418 ::  64 Word.word) . 
   (write_reg RVBAR_EL3_ref w__418 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__419 ::  64 Word.word) . 
   (write_reg SCXTNUM_EL0_ref w__419 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__420 ::  64 Word.word) . 
   (write_reg SCXTNUM_EL1_ref w__420 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__421 ::  64 Word.word) . 
   (write_reg SCXTNUM_EL2_ref w__421 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__422 ::  64 Word.word) . 
   (write_reg SCXTNUM_EL3_ref w__422 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__423 ::  64 Word.word) . 
   (write_reg SMIDR_EL1_ref w__423 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__424 ::  64 Word.word) . 
   (write_reg SMPRIMAP_EL2_ref w__424 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__425 ::  64 Word.word) . 
   (write_reg SMPRI_EL1_ref w__425 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__426 ::  64 Word.word) . 
   (write_reg TPIDR2_EL0_ref w__426 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__427 ::  64 Word.word) . 
   (write_reg TPIDRRO_EL0_ref w__427 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__428 ::  64 Word.word) . 
   (write_reg TPIDR_EL0_ref w__428 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__429 ::  64 Word.word) . 
   (write_reg TPIDR_EL1_ref w__429 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__430 ::  64 Word.word) . 
   (write_reg TPIDR_EL2_ref w__430 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__431 ::  64 Word.word) . 
   (write_reg TPIDR_EL3_ref w__431 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__432 ::  64 Word.word) . 
   (write_reg TRFCR_EL1_ref w__432 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__433 ::  64 Word.word) . 
   (write_reg TRFCR_EL2_ref w__433 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__434 ::  64 Word.word) . 
   (write_reg DISR_EL1_ref w__434 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__435 ::  64 Word.word) . 
   (write_reg VDISR_EL2_ref w__435 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__436 ::  64 Word.word) . 
   (write_reg MPIDR_EL1_ref w__436 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__437 ::  64 Word.word) . 
   (write_reg VMPIDR_EL2_ref w__437 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__438 ::  64 Word.word) . 
   (write_reg VSESR_EL2_ref w__438 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__439 ::  64 Word.word) . 
   (write_reg DBGDTRTX_EL0_ref w__439 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__440 ::  64 Word.word) . 
   (write_reg ICC_ASGI1R_EL1_ref w__440 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__441 ::  64 Word.word) . 
   (write_reg ICC_DIR_EL1_ref w__441 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__442 ::  64 Word.word) . 
   (write_reg ICV_DIR_EL1_ref w__442 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__443 ::  64 Word.word) . 
   (write_reg ICC_SGI0R_EL1_ref w__443 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__444 ::  64 Word.word) . 
   (write_reg ICC_SGI1R_EL1_ref w__444 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__445 ::  64 Word.word) . 
   (write_reg ICC_EOIR0_EL1_ref w__445 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__446 ::  64 Word.word) . 
   (write_reg ICV_EOIR0_EL1_ref w__446 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__447 ::  64 Word.word) . 
   (write_reg ICC_EOIR1_EL1_ref w__447 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__448 ::  64 Word.word) . 
   (write_reg ICV_EOIR1_EL1_ref w__448 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__449 ::  64 Word.word) . 
   (write_reg OSLAR_EL1_ref w__449 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__450 ::  64 Word.word) . 
   (write_reg PMSWINC_EL0_ref w__450 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__451 ::  32 Word.word) . 
   (write_reg EDPRSR_ref w__451 \<then>
   undefined_int instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__452 :: ii) . 
   (write_reg clock_divider_ref w__452 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__453 ::  32 Word.word) . 
   (write_reg MAIR0_S_ref w__453 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__454 ::  32 Word.word) . 
   (write_reg NMRR_S_ref w__454 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__455 ::  32 Word.word) . 
   (write_reg TTBCR2_S_ref w__455 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__456 ::  32 Word.word) . 
   (write_reg CONTEXTIDR_S_ref w__456 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__457 ::  64 Word.word) . 
   (write_reg TTBR0_S_ref w__457 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__458 ::  64 Word.word) . 
   (write_reg TTBR1_S_ref w__458 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__459 ::  32 Word.word) . 
   (write_reg DACR_S_ref w__459 \<then>
   undefined_signal () ) \<bind> ((\<lambda> (w__460 :: signal) . 
   (write_reg CP15SDISABLE_ref w__460 \<then>
   undefined_signal () ) \<bind> ((\<lambda> (w__461 :: signal) . 
   (write_reg CP15SDISABLE2_ref w__461 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__462 ::  32 Word.word) . 
   (write_reg ACTLR2_S_ref w__462 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__463 ::  32 Word.word) . 
   (write_reg ACTLR_S_ref w__463 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__464 ::  32 Word.word) . 
   (write_reg ADFSR_S_ref w__464 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__465 ::  32 Word.word) . 
   (write_reg AIFSR_S_ref w__465 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__466 ::  32 Word.word) . 
   (write_reg AMAIR0_S_ref w__466 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__467 ::  32 Word.word) . 
   (write_reg AMAIR1_S_ref w__467 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__468 ::  32 Word.word) . 
   (write_reg CNTP_CTL_S_ref w__468 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__469 ::  64 Word.word) . 
   (write_reg CNTP_CVAL_S_ref w__469 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__470 ::  32 Word.word) . 
   (write_reg CSSELR_S_ref w__470 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__471 ::  32 Word.word) . 
   (write_reg SDCR_ref w__471 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__472 ::  32 Word.word) . 
   (write_reg DBGDEVID1_ref w__472 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__473 ::  32 Word.word) . 
   (write_reg DBGDEVID2_ref w__473 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__474 ::  32 Word.word) . 
   (write_reg DBGDEVID_ref w__474 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__475 ::  32 Word.word) . 
   (write_reg DBGDIDR_ref w__475 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__476 ::  64 Word.word) . 
   (write_reg DBGDSAR_ref w__476 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__477 ::  32 Word.word) . 
   (write_reg DBGWFAR_ref w__477 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__478 ::  32 Word.word) . 
   (write_reg FCSEIDR_ref w__478 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__479 ::  32 Word.word) . 
   (write_reg ICC_MSRE_ref w__479 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__480 ::  32 Word.word) . 
   (write_reg ICC_MCTLR_ref w__480 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__481 ::  32 Word.word) . 
   (write_reg ICC_MGRPEN1_ref w__481 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__482 ::  32 Word.word) . 
   (write_reg JIDR_ref w__482 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__483 ::  32 Word.word) . 
   (write_reg JMCR_ref w__483 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__484 ::  32 Word.word) . 
   (write_reg JOSCR_ref w__484 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__485 ::  64 Word.word) . 
   (write_reg PAR_S_ref w__485 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__486 ::  32 Word.word) . 
   (write_reg PMMIR_ref w__486 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__487 ::  32 Word.word) . 
   (write_reg TCMTR_ref w__487 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__488 ::  32 Word.word) . 
   (write_reg TLBTR_ref w__488 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__489 ::  32 Word.word) . 
   (write_reg TPIDRPRW_S_ref w__489 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__490 ::  32 Word.word) . 
   (write_reg TPIDRURO_S_ref w__490 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__491 ::  32 Word.word) . 
   (write_reg TPIDRURW_S_ref w__491 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__492 ::  32 Word.word) . 
   (write_reg DBGOSLAR_ref w__492 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__493 :: bool) . 
   (write_reg IsWFIsleep_ref w__493 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__494 :: bool) . 
   (write_reg IsWFEsleep_ref w__494 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__495 ::  32 Word.word) . 
   (write_reg ConfigReg_ref w__495 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__496 :: bool) . 
   (write_reg ShouldAdvanceIT_ref w__496 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__497 :: bool) . 
   (write_reg ShouldAdvanceSS_ref w__497 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 1 :: int)::ii)  :: ( 1 Word.word) M)) \<bind> ((\<lambda> (w__498 ::  1 Word.word) . 
   (write_reg EventRegister_ref w__498 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__499 ::  64 Word.word) . 
   (undefined_vector (( 5 :: int)::ii) w__499  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__500 :: ( 64 Word.word) list) . 
   (write_reg RC_ref w__500 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 2 :: int)::ii)  :: ( 2 Word.word) M)) \<bind> ((\<lambda> (w__501 ::  2 Word.word) . 
   (write_reg BTypeNext_ref w__501 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__502 :: bool) . 
   (write_reg BTypeCompatible_ref w__502 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__503 ::  64 Word.word) . 
   (undefined_vector (( 32 :: int)::ii) w__503  :: ( ( 64 Word.word)list) M) \<bind> ((\<lambda> (w__504 :: ( 64 Word.word) list) . 
   (write_reg Dclone_ref w__504 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__505 ::  32 Word.word) . 
   (write_reg DTRRX_ref w__505 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__506 ::  32 Word.word) . 
   (write_reg DTRTX_ref w__506 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__507 :: bool) . 
   (write_reg InstructionStep_ref w__507 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__508 ::  52 Word.word) . 
   (write_reg CNTReadBase_ref w__508 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__509 ::  52 Word.word) . 
   (write_reg CNTBaseN_ref w__509 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__510 ::  52 Word.word) . 
   (write_reg CNTEL0BaseN_ref w__510 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__511 ::  52 Word.word) . 
   (write_reg CNTCTLBase_ref w__511 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__512 ::  52 Word.word) . 
   (write_reg RD_base_ref w__512 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__513 ::  52 Word.word) . 
   (write_reg SGI_base_ref w__513 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__514 ::  52 Word.word) . 
   (write_reg VLPI_base_ref w__514 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 52 :: int)::ii)  :: ( 52 Word.word) M)) \<bind> ((\<lambda> (w__515 ::  52 Word.word) . 
   (write_reg ETEBase_ref w__515 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__516 ::  32 Word.word) . 
   (write_reg ThisInstr_ref w__516 \<then>
   undefined___InstrEnc () ) \<bind> ((\<lambda> (w__517 :: InstrEnc) . 
   (write_reg ThisInstrEnc_ref w__517 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__518 :: bool) . 
   (write_reg ExclusiveMonitorSet_ref w__518 \<then>
   undefined_bool instance_Sail2_values_Register_Value_Armv9_types_register_value_dict () ) \<bind> ((\<lambda> (w__519 :: bool) . 
   (write_reg highest_el_aarch32_ref w__519 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__520 ::  32 Word.word) . 
   (write_reg CNTCR_ref w__520 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__521 ::  32 Word.word) . 
   (write_reg CNTSCR_ref w__521 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__522 ::  32 Word.word) . 
   (write_reg CTILSR_ref w__522 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__523 ::  32 Word.word) . 
   (write_reg EDLSR_ref w__523 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__524 ::  32 Word.word) . 
   (write_reg PMLSR_ref w__524 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__525 ::  32 Word.word) . 
   (write_reg EDESR_ref w__525 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__526 ::  32 Word.word) . 
   (write_reg EDECR_ref w__526 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__527 ::  32 Word.word) . 
   (write_reg CTIDEVCTL_ref w__527 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__528 ::  32 Word.word) . 
   (write_reg EDVIDSR_ref w__528 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__529 ::  64 Word.word) . 
   (write_reg PMPCSR_ref w__529 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__530 ::  32 Word.word) . 
   (write_reg PMVIDSR_ref w__530 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__531 ::  64 Word.word) . 
   (write_reg CNTHV_TVAL_EL2_ref w__531 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__532 ::  64 Word.word) . 
   (write_reg CNTHPS_TVAL_EL2_ref w__532 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__533 ::  64 Word.word) . 
   (write_reg CNTP_TVAL_EL0_ref w__533 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__534 ::  64 Word.word) . 
   (write_reg CNTPS_TVAL_EL1_ref w__534 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__535 ::  64 Word.word) . 
   (write_reg CNTV_TVAL_EL0_ref w__535 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__536 ::  64 Word.word) . 
   (write_reg CNTHVS_TVAL_EL2_ref w__536 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__537 ::  64 Word.word) . 
   (write_reg CNTHP_TVAL_EL2_ref w__537 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__538 ::  64 Word.word) . 
   (write_reg GICR_PROPBASER_ref w__538 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__539 ::  64 Word.word) . 
   (write_reg GICR_CLRLPIR_ref w__539 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__540 ::  64 Word.word) . 
   (write_reg EDHSR_ref w__540 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__541 ::  64 Word.word) . 
   (write_reg GICR_INVLPIR_ref w__541 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__542 ::  64 Word.word) . 
   (write_reg EDDFR_ref w__542 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__543 ::  64 Word.word) . 
   (write_reg EDPCSR_ref w__543 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__544 ::  64 Word.word) . 
   (write_reg GITS_TYPER_ref w__544 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__545 ::  64 Word.word) . 
   (write_reg GICR_PENDBASER_ref w__545 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__546 ::  64 Word.word) . 
   (write_reg GICR_VPROPBASER_ref w__546 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__547 ::  64 Word.word) . 
   (write_reg GICR_VPENDBASER_ref w__547 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__548 ::  64 Word.word) . 
   (write_reg GICR_SETLPIR_ref w__548 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__549 ::  64 Word.word) . 
   (write_reg GITS_SGIR_ref w__549 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__550 ::  64 Word.word) . 
   (write_reg EDPFR_ref w__550 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__551 ::  64 Word.word) . 
   (write_reg GITS_CREADR_ref w__551 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__552 ::  64 Word.word) . 
   (write_reg GITS_CWRITER_ref w__552 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__553 ::  64 Word.word) . 
   (write_reg EDAA32PFR_ref w__553 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__554 ::  64 Word.word) . 
   (write_reg GITS_CBASER_ref w__554 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 64 :: int)::ii)  :: ( 64 Word.word) M)) \<bind> ((\<lambda> (w__555 ::  64 Word.word) . 
   (write_reg GICR_INVALLR_ref w__555 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__556 ::  32 Word.word) . 
   (write_reg FPSID_ref w__556 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__557 ::  32 Word.word) . 
   (write_reg GICD_CTLR_ref w__557 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__558 ::  32 Word.word) . 
   (write_reg CTIITCTRL_ref w__558 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__559 ::  32 Word.word) . 
   (write_reg GICR_IIDR_ref w__559 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__560 ::  32 Word.word) . 
   (write_reg CTIPIDR1_ref w__560 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__561 ::  32 Word.word) . 
   (write_reg GICV_IAR_ref w__561 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__562 ::  32 Word.word) . 
   (write_reg EDCIDR3_ref w__562 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__563 ::  32 Word.word) . 
   (write_reg GICM_SETSPI_NSR_ref w__563 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__564 ::  32 Word.word) . 
   (write_reg GICR_WAKER_ref w__564 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__565 ::  32 Word.word) . 
   (write_reg GITS_PARTIDR_ref w__565 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__566 ::  32 Word.word) . 
   (write_reg CTIPIDR0_ref w__566 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__567 ::  32 Word.word) . 
   (write_reg GICM_SETSPI_SR_ref w__567 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__568 ::  32 Word.word) . 
   (write_reg CNTFID0_ref w__568 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__569 ::  32 Word.word) . 
   (write_reg GICR_SYNCR_ref w__569 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__570 ::  32 Word.word) . 
   (write_reg GICV_DIR_ref w__570 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__571 ::  32 Word.word) . 
   (write_reg PMCFGR_ref w__571 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__572 ::  32 Word.word) . 
   (write_reg CTIDEVID2_ref w__572 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__573 ::  32 Word.word) . 
   (write_reg EDPIDR3_ref w__573 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__574 ::  32 Word.word) . 
   (write_reg GICR_PARTIDR_ref w__574 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__575 ::  32 Word.word) . 
   (write_reg CTILAR_ref w__575 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__576 ::  32 Word.word) . 
   (write_reg GICC_STATUSR_ref w__576 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__577 ::  32 Word.word) . 
   (write_reg GICM_IIDR_ref w__577 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__578 ::  32 Word.word) . 
   (write_reg PMPIDR4_ref w__578 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__579 ::  32 Word.word) . 
   (write_reg EDDEVID1_ref w__579 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__580 ::  32 Word.word) . 
   (write_reg GICV_AEOIR_ref w__580 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__581 ::  32 Word.word) . 
   (write_reg GICC_PMR_ref w__581 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__582 ::  32 Word.word) . 
   (write_reg CTIDEVARCH_ref w__582 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__583 ::  32 Word.word) . 
   (write_reg GICD_STATUSR_ref w__583 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__584 ::  32 Word.word) . 
   (write_reg GICR_MPAMIDR_ref w__584 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__585 ::  32 Word.word) . 
   (write_reg CTICIDR3_ref w__585 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__586 ::  32 Word.word) . 
   (write_reg PMITCTRL_ref w__586 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__587 ::  32 Word.word) . 
   (write_reg PMPIDR3_ref w__587 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__588 ::  32 Word.word) . 
   (write_reg GICV_RPR_ref w__588 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__589 ::  32 Word.word) . 
   (write_reg GICV_AHPPIR_ref w__589 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__590 ::  32 Word.word) . 
   (write_reg GICR_CTLR_ref w__590 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__591 ::  32 Word.word) . 
   (write_reg GICV_BPR_ref w__591 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__592 ::  32 Word.word) . 
   (write_reg GICV_EOIR_ref w__592 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__593 ::  32 Word.word) . 
   (write_reg PMAUTHSTATUS_ref w__593 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__594 ::  32 Word.word) . 
   (write_reg CNTEL0ACR_ref w__594 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__595 ::  32 Word.word) . 
   (write_reg GICD_TYPER_ref w__595 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__596 ::  32 Word.word) . 
   (write_reg CTICIDR0_ref w__596 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__597 ::  32 Word.word) . 
   (write_reg GICC_HPPIR_ref w__597 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__598 ::  32 Word.word) . 
   (write_reg GICD_CLRSPI_NSR_ref w__598 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__599 ::  32 Word.word) . 
   (write_reg GICD_CLRSPI_SR_ref w__599 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__600 ::  32 Word.word) . 
   (write_reg GITS_STATUSR_ref w__600 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__601 ::  32 Word.word) . 
   (write_reg GICH_VTR_ref w__601 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__602 ::  32 Word.word) . 
   (write_reg CTIPIDR3_ref w__602 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__603 ::  32 Word.word) . 
   (write_reg GICV_ABPR_ref w__603 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__604 ::  32 Word.word) . 
   (write_reg EDPIDR4_ref w__604 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__605 ::  32 Word.word) . 
   (write_reg CTICONTROL_ref w__605 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__606 ::  32 Word.word) . 
   (write_reg PMCIDR2_ref w__606 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__607 ::  32 Word.word) . 
   (write_reg GICR_INMIR0_ref w__607 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__608 ::  32 Word.word) . 
   (write_reg GICV_CTLR_ref w__608 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__609 ::  32 Word.word) . 
   (write_reg GICC_IAR_ref w__609 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__610 ::  32 Word.word) . 
   (write_reg EDPRCR_ref w__610 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__611 ::  32 Word.word) . 
   (write_reg GICR_ISENABLER0_ref w__611 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__612 ::  32 Word.word) . 
   (write_reg CTICIDR2_ref w__612 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__613 ::  32 Word.word) . 
   (write_reg GICR_VSGIPENDR_ref w__613 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__614 ::  32 Word.word) . 
   (write_reg EDRCR_ref w__614 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__615 ::  32 Word.word) . 
   (write_reg GICV_PMR_ref w__615 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__616 ::  32 Word.word) . 
   (write_reg PMCIDR1_ref w__616 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__617 ::  32 Word.word) . 
   (write_reg PMDEVTYPE_ref w__617 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__618 ::  32 Word.word) . 
   (write_reg PMLAR_ref w__618 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__619 ::  32 Word.word) . 
   (write_reg GICH_ELRSR_ref w__619 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__620 ::  32 Word.word) . 
   (write_reg EDDEVID_ref w__620 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__621 ::  32 Word.word) . 
   (write_reg GICC_DIR_ref w__621 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__622 ::  32 Word.word) . 
   (write_reg PMCIDR0_ref w__622 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__623 ::  32 Word.word) . 
   (write_reg EDCIDR0_ref w__623 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__624 ::  32 Word.word) . 
   (write_reg GITS_MPAMIDR_ref w__624 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__625 ::  32 Word.word) . 
   (write_reg GICD_SGIR_ref w__625 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__626 ::  32 Word.word) . 
   (write_reg GICV_HPPIR_ref w__626 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__627 ::  32 Word.word) . 
   (write_reg CTIPIDR2_ref w__627 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__628 ::  32 Word.word) . 
   (write_reg CTICIDR1_ref w__628 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__629 ::  32 Word.word) . 
   (write_reg GICH_MISR_ref w__629 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__630 ::  32 Word.word) . 
   (write_reg CTIDEVTYPE_ref w__630 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__631 ::  32 Word.word) . 
   (write_reg EDDEVID2_ref w__631 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__632 ::  32 Word.word) . 
   (write_reg PMPIDR1_ref w__632 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__633 ::  32 Word.word) . 
   (write_reg GITS_CTLR_ref w__633 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__634 ::  32 Word.word) . 
   (write_reg GICH_VMCR_ref w__634 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__635 ::  32 Word.word) . 
   (write_reg GICC_AEOIR_ref w__635 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__636 ::  32 Word.word) . 
   (write_reg GICC_AHPPIR_ref w__636 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__637 ::  32 Word.word) . 
   (write_reg PMDEVID_ref w__637 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__638 ::  32 Word.word) . 
   (write_reg GICC_ABPR_ref w__638 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__639 ::  32 Word.word) . 
   (write_reg CTIDEVID1_ref w__639 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__640 ::  32 Word.word) . 
   (write_reg GITS_MPIDR_ref w__640 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__641 ::  32 Word.word) . 
   (write_reg GICC_AIAR_ref w__641 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__642 ::  32 Word.word) . 
   (write_reg EDCIDR2_ref w__642 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__643 ::  32 Word.word) . 
   (write_reg GICD_SETSPI_NSR_ref w__643 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__644 ::  32 Word.word) . 
   (write_reg CNTID_ref w__644 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__645 ::  32 Word.word) . 
   (write_reg GITS_IIDR_ref w__645 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__646 ::  32 Word.word) . 
   (write_reg CTIAUTHSTATUS_ref w__646 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__647 ::  32 Word.word) . 
   (write_reg GICH_HCR_ref w__647 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__648 ::  32 Word.word) . 
   (write_reg GICC_RPR_ref w__648 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__649 ::  32 Word.word) . 
   (write_reg GICC_BPR_ref w__649 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__650 ::  32 Word.word) . 
   (write_reg PMPIDR2_ref w__650 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__651 ::  32 Word.word) . 
   (write_reg CTIDEVID_ref w__651 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__652 ::  32 Word.word) . 
   (write_reg GICD_SETSPI_SR_ref w__652 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__653 ::  32 Word.word) . 
   (write_reg GICR_STATUSR_ref w__653 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__654 ::  32 Word.word) . 
   (write_reg GICC_EOIR_ref w__654 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__655 ::  32 Word.word) . 
   (write_reg EDLAR_ref w__655 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__656 ::  32 Word.word) . 
   (write_reg EDPIDR0_ref w__656 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__657 ::  32 Word.word) . 
   (write_reg EDPIDR2_ref w__657 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__658 ::  32 Word.word) . 
   (write_reg CNTNSAR_ref w__658 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__659 ::  32 Word.word) . 
   (write_reg EDITCTRL_ref w__659 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__660 ::  32 Word.word) . 
   (write_reg GICD_IIDR_ref w__660 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__661 ::  32 Word.word) . 
   (write_reg EDCIDR1_ref w__661 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__662 ::  32 Word.word) . 
   (write_reg GICR_VSGIR_ref w__662 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__663 ::  32 Word.word) . 
   (write_reg EDDEVTYPE_ref w__663 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__664 ::  32 Word.word) . 
   (write_reg GICM_TYPER_ref w__664 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__665 ::  32 Word.word) . 
   (write_reg GICD_TYPER2_ref w__665 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__666 ::  32 Word.word) . 
   (write_reg GICH_EISR_ref w__666 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__667 ::  32 Word.word) . 
   (write_reg GICC_CTLR_ref w__667 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__668 ::  32 Word.word) . 
   (write_reg CNTSR_ref w__668 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__669 ::  32 Word.word) . 
   (write_reg GICM_CLRSPI_NSR_ref w__669 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__670 ::  32 Word.word) . 
   (write_reg GICV_STATUSR_ref w__670 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__671 ::  32 Word.word) . 
   (write_reg GICV_AIAR_ref w__671 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__672 ::  32 Word.word) . 
   (write_reg CTIPIDR4_ref w__672 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__673 ::  32 Word.word) . 
   (write_reg EDPIDR1_ref w__673 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__674 ::  32 Word.word) . 
   (write_reg PMPIDR0_ref w__674 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__675 ::  32 Word.word) . 
   (write_reg PMCIDR3_ref w__675 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__676 ::  32 Word.word) . 
   (write_reg GICM_CLRSPI_SR_ref w__676 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__677 ::  32 Word.word) . 
   (write_reg AMIIDR_ref w__677 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__678 ::  32 Word.word) . 
   (write_reg AMPIDR0_ref w__678 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__679 ::  32 Word.word) . 
   (write_reg AMPIDR2_ref w__679 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__680 ::  32 Word.word) . 
   (write_reg AMCIDR2_ref w__680 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__681 ::  32 Word.word) . 
   (write_reg AMCIDR3_ref w__681 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__682 ::  32 Word.word) . 
   (write_reg AMPIDR4_ref w__682 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__683 ::  32 Word.word) . 
   (write_reg AMPIDR3_ref w__683 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__684 ::  32 Word.word) . 
   (write_reg AMDEVARCH_ref w__684 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__685 ::  32 Word.word) . 
   (write_reg AMCIDR0_ref w__685 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__686 ::  32 Word.word) . 
   (write_reg AMPIDR1_ref w__686 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__687 ::  32 Word.word) . 
   (write_reg AMCIDR1_ref w__687 \<then>
   (undefined_bitvector 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Register_Value_Armv9_types_register_value_dict (( 32 :: int)::ii)  :: ( 32 Word.word) M)) \<bind> ((\<lambda> (w__688 ::  32 Word.word) . 
   (write_reg AMDEVTYPE_ref w__688 \<then>
   undefined_InterruptID () ) \<bind> ((\<lambda> (w__689 :: InterruptID) . 
   undefined_option w__689 \<bind> ((\<lambda> (w__690 ::  InterruptID option) . 
   (write_reg GIC_Pending_ref w__690 \<then>
   undefined_InterruptID () ) \<bind> ((\<lambda> (w__691 :: InterruptID) . 
   undefined_option w__691 \<bind> ((\<lambda> (w__692 ::  InterruptID option) .  write_reg GIC_Active_ref w__692)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))\<close>



end
