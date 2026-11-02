module
public import Structure.PA17_TM_RatArithmetic_Sub_016c
public import Common.ROOT_TM_GCD_Codec_034

@[expose] public section
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
open PA17TMDivisionCompose006

def branchInitial (pairs : List Pair) : MachineState 147 := lift (by decide : 27 ≤ 36) 0 (subInitial pairs)

def branchFinal (pairs : List Pair) : MachineState 147 :=
  if borrow pairs then lift (by decide : 36 ≤ 36) 3 (zeroFinal pairs)
  else lift (by decide : 5 ≤ 36) 1 (rewindFinal pairs)

def branchTrace (pairs : List Pair) : List (MachineState 147) :=
  subSegment pairs ++ rewindSegment (borrow pairs) pairs ++
    if borrow pairs then zeroSegment pairs else []

/-- The branch in this trace is justified by the physical old HALT label,
with a charged write-self transition at every fixed port. -/
theorem branch_runsFrom (pairs : List Pair) :
    PSTRTMSeq005.RunsFrom branchMachine (branchInitial pairs) (branchTrace pairs) (branchFinal pairs) := by
  have hbase := segment_append branchMachine _ _ _ _ _ _ (sub_segment pairs)
    (rewind_segment (borrow pairs) pairs) (sub_transfer pairs)
  cases hb : borrow pairs with
  | false =>
    have hbase' : Segment branchMachine (branchInitial pairs)
        (subSegment pairs ++ rewindSegment false pairs)
        (lift (by decide : 5 ≤ 36) 1 (rewindFinal pairs)) := by
      simpa [branchInitial,hb,rewindPhase] using hbase
    have hr := segment_runsFrom branchMachine _ _ _ hbase' (rewind_ge_halt pairs)
    simpa [branchTrace,branchFinal,hb] using hr
  | true =>
    have hbase' : Segment branchMachine (branchInitial pairs)
        (subSegment pairs ++ rewindSegment true pairs)
        (lift (by decide : 5 ≤ 36) 2 (rewindFinal pairs)) := by
      simpa [branchInitial,hb,rewindPhase] using hbase
    have hall := segment_append branchMachine _ _ _ _ _ _ hbase' (zero_segment pairs) (rewind_zero_transfer pairs)
    have hr := segment_runsFrom branchMachine _ _ _ hall (zero_final_halt pairs)
    simpa [branchTrace,branchFinal,hb] using hr

theorem branch_initial_tape (pairs : List Pair) :
    branchInitial pairs = (⟨0,Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns pairs)⟩ : MachineState 147) := by
  change (⟨0,Turing.Tape.mk₂ [false] (PSTRTMBinaryAdd024.operandColumns pairs ++ [false,false])⟩ : MachineState 147) = _
  rw [ROOTTMGCDCodec034.empty_counter_tape]

theorem branch_final_tape (pairs : List Pair) :
    (branchFinal pairs).Tape = Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns (saturatedPairs pairs)) := by
  have ht : (branchFinal pairs).Tape = Turing.Tape.mk₂ [false]
      (PSTRTMBinaryAdd024.operandColumns (saturatedPairs pairs) ++ [false,false]) := by
    cases hb : borrow pairs with
    | false =>
      simp [branchFinal,saturatedPairs,hb,lift,blockCfg,padCfg,rewindFinal,PSTRTMColumnRewind067.state]
    | true =>
      have hm := ROOTTMGCDMap004.residentMap_final_tape zeroPair [] (afterSub pairs) []
      simpa [branchFinal,saturatedPairs,hb,lift,blockCfg,padCfg,zeroFinal] using hm
  rw [ht,ROOTTMGCDCodec034.empty_counter_tape]

theorem branchTrace_length_le (pairs : List Pair) : (branchTrace pairs).length ≤ 27*pairs.length+12 := by
  have hs : (subSegment pairs).length = 9*pairs.length+3 := by
    simp only [subSegment,List.length_map,PA17TMDivisionSub001.sub_length]
  have hr (b : Bool) : (rewindSegment b pairs).length = 4*pairs.length+3 := by
    simp only [rewindSegment,List.length_map,PSTRTMColumnRewind067.full_length,List.length_reverse,afterSub,
      PA17TMDivisionSub001.subPairs_length]
  have hz : (zeroSegment pairs).length = 14*pairs.length+6 := by
    simp only [zeroSegment,List.length_map,ROOTTMGCDMap004.residentMap_length,afterSub,
      PA17TMDivisionSub001.subPairs_length]
  simp only [branchTrace,List.length_append,hs,hr]
  cases hb : borrow pairs <;> simp [hz] <;> omega

theorem branchTrace_quadratic (pairs : List Pair) : (branchTrace pairs).length ≤ 64*(pairs.length+1)^2 := by
  have hb := branchTrace_length_le pairs
  nlinarith

theorem isolatedOutput_length_le (pairs : List Pair) :
    (PA17TMDivisionCodec003.isolatedOutputTrace pairs).length ≤ 256*(pairs.length+1)^2 := by
  have hc := ROOTTMGCDCodec034.codecTrace_length_le pairs
  simpa only [ROOTTMGCDCodec034.codecTrace,List.length_map] using hc

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
