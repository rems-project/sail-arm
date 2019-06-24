termination_measure BigEndianReverse(x) = 'width
termination_measure Reduce(op,input,esize) = 'N

/* This is a cheat - it's a plain upper bound to break the cycle */
termination_measure TakeUnmaskedPhysicalSErrorInterrupts(_) = 10
termination_measure TakePendingInterrupts(_) = 10
termination_measure AArch32_TakePhysicalFIQException() = 10
termination_measure AArch64_TakePhysicalFIQException() = 10
termination_measure AArch64_TakeException(_,_,_,_) = 10
termination_measure AArch32_TakePhysicalIRQException() = 10
termination_measure AArch64_TakePhysicalIRQException() = 10
termination_measure AArch32_TakePhysicalSErrorException(_,_,_,_,_) = 10
termination_measure AArch64_TakePhysicalSErrorException(_,_) = 10
termination_measure AArch32_TakeVirtualFIQException() = 10
termination_measure AArch64_TakeVirtualFIQException() = 10
termination_measure AArch32_TakeVirtualIRQException() = 10
termination_measure AArch64_TakeVirtualIRQException() = 10
termination_measure AArch32_TakeVirtualSErrorException(_,_,_,_) = 10
termination_measure AArch64_TakeVirtualSErrorException(_,_) = 10

/* Again, just a limit.  The secondstage parameters actually break the loop. */
termination_measure AArch64_SecondStageTranslate(_,_,_,_,_,_,_,_) = 8
termination_measure AArch64_CheckAndUpdateDescriptor(_,_,_,_,_,_,_,_) = 8
termination_measure AArch64_SecondStageWalk(_,_,_,_,_,_) = 8
termination_measure AArch64_TranslationTableWalk(_,_,_,_,_,_,_,_) = 8

/* Similarly */
termination_measure AArch32_SecondStageTranslate(_,_,_,_,_,_,_) = 6
termination_measure AArch32_TranslationTableWalk(_,_,_,_,_,_,_) = 6
termination_measure AArch32_SecondStageWalk(_,_,_,_,_) = 6

termination_measure AArch64_TranslationTableWalk until 4 - level
termination_measure AArch32_TranslationTableWalk until 4 - level

termination_measure _ChooseRandomNonExcludedTag while 16 - UInt(tag)

termination_measure __Reset repeat 1, repeat 1, repeat 1, repeat 1,
                            repeat 1, repeat 1, repeat 1, repeat 1,
                            repeat 1, repeat 1, repeat 1, repeat 1,
                            repeat 1, repeat 1, repeat 1, repeat 1

termination_measure ChooseNonExcludedTag
  while UInt(offset),
  while 16  /* TODO: this is just a limit, not a measure - looks quite awkward */

termination_measure semihost
  while pow2(64) /* printing a zero-terminating string!! */

termination_measure FPRoundBase
  while RoundUp(Real(1) / mantissa), /* should be a base-2 log */
  while RoundUp(mantissa)

termination_measure RecipSqrtEstimate
  while pow2(28) - b

termination_measure FPRSqrtEstimate
  while 64 + exp

termination_measure __ListConfig
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, // 8
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, // 16
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1,
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, // 32
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1,
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1,
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1,
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, // 64
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1,
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, // 96
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1,
  repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1, repeat 1,
  repeat 1

termination_measure __EndCycle
  repeat 1, repeat 1, repeat 1, repeat 1

/* This is an infinite loop, just want enough that it could do something */
termination_measure main
  while 100
