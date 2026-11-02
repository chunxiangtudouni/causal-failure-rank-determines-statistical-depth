module
public import Structure.PA17_TM_RatArithmetic_Sub_016b

@[expose] public section
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
open PA17TMDivisionCompose006
variable {states : Nat}

theorem phase_segment (h : states ≤ 36) (phase : Fin 4) (machine : Machine states)
    (hf : family phase = padMachine h machine)
    (first last : MachineState states) (trace : List (MachineState states))
    (run : PSTRTMSeq005.RunsFrom machine first trace last) :
    Segment branchMachine (lift h phase first) (trace.map (lift h phase)) (lift h phase last) := by
  have hp := pad_runsFrom h machine first last trace run
  rw [← hf] at hp
  have hb := block_segment family ports phase _ _ _ hp
  unfold lift branchMachine
  simpa only [List.map_map,Function.comp_def] using hb

theorem phase_transfer (h : states ≤ 36) (phase nextPhase : Fin 4) (machine : Machine states)
    (hf : family phase = padMachine h machine) (last : MachineState states)
    (halt : Turing.TM0.step machine last = none) (nextLabel : Fin 37)
    (port : ports phase (padLabel h last.q) = some (nextPhase,nextLabel)) :
    Turing.TM0.step branchMachine (lift h phase last) =
      some (blockCfg nextPhase ⟨nextLabel,last.Tape⟩) := by
  have hp : Turing.TM0.step (family phase) (padCfg h last) = none := by
    rw [hf,pad_step,halt,Option.map_none]
  exact block_transfer family ports phase (padCfg h last) (nextPhase,nextLabel) hp port

theorem phase_halt (h : states ≤ 36) (phase : Fin 4) (machine : Machine states)
    (hf : family phase = padMachine h machine) (last : MachineState states)
    (halt : Turing.TM0.step machine last = none) (port : ports phase (padLabel h last.q) = none) :
    Turing.TM0.step branchMachine (lift h phase last) = none := by
  have hp : Turing.TM0.step (family phase) (padCfg h last) = none := by
    rw [hf,pad_step,halt,Option.map_none]
  exact block_halt family ports phase (padCfg h last) hp port

def subInitial (pairs : List Pair) : MachineState 27 :=
  PA17TMDivisionSub001.state (PA17TMDivisionSub001.readA false) [false]
    (PSTRTMBinaryAdd024.operandColumns pairs ++ [false,false])

def subFinal (pairs : List Pair) : MachineState 27 :=
  PA17TMDivisionSub001.state (PA17TMDivisionSub001.haltLabel (borrow pairs))
    (PSTRTMCompareCode054.leftColumns (afterSub pairs).reverse ++ [false]) [false,false]

def subSegment (pairs : List Pair) : List (MachineState 147) :=
  (PA17TMDivisionSub001.subTrace false [false] [] pairs []).map (lift (by decide : 27 ≤ 36) 0)

def rewindInitial (pairs : List Pair) : MachineState 5 :=
  PSTRTMColumnRewind067.state 0
    (PSTRTMCompareCode054.leftColumns (afterSub pairs).reverse ++ [false]) [false,false]

def rewindFinal (pairs : List Pair) : MachineState 5 :=
  PSTRTMColumnRewind067.state 5 [false]
    (PSTRTMBinaryAdd024.operandColumns (afterSub pairs) ++ [false,false])

def rewindSegment (b : Bool) (pairs : List Pair) : List (MachineState 147) :=
  (PSTRTMColumnRewind067.fullTrace [] (afterSub pairs).reverse [false,false]).map
    (lift (by decide : 5 ≤ 36) (rewindPhase b))

def zeroInitial (pairs : List Pair) : MachineState 36 :=
  ROOTTMGCDMap004.residentMapInitial [] (afterSub pairs) []

def zeroFinal (pairs : List Pair) : MachineState 36 :=
  ROOTTMGCDMap004.residentMapFinal zeroPair [] (afterSub pairs) []

def zeroSegment (pairs : List Pair) : List (MachineState 147) :=
  (ROOTTMGCDMap004.residentMapTrace zeroPair [] (afterSub pairs) []).map (lift (by decide : 36 ≤ 36) 3)

theorem sub_run (pairs : List Pair) :
    PSTRTMSeq005.RunsFrom PA17TMDivisionSub001.subMachine (subInitial pairs)
      (PA17TMDivisionSub001.subTrace false [false] [] pairs []) (subFinal pairs) :=
  PA17TMDivisionSub001.sub_runsFrom false [false] pairs []

theorem rewind_run (pairs : List Pair) :
    PSTRTMSeq005.RunsFrom PSTRTMColumnRewind067.rewindMachine (rewindInitial pairs)
      (PSTRTMColumnRewind067.fullTrace [] (afterSub pairs).reverse [false,false]) (rewindFinal pairs) :=
  PSTRTMColumnRewind067.rewind_runsFrom [] (afterSub pairs) [false,false]

theorem zero_run (pairs : List Pair) :
    PSTRTMSeq005.RunsFrom (ROOTTMGCDMap004.residentMapMachine zeroPair) (zeroInitial pairs)
      (ROOTTMGCDMap004.residentMapTrace zeroPair [] (afterSub pairs) []) (zeroFinal pairs) :=
  ROOTTMGCDMap004.residentMap_runsFrom zeroPair [] (afterSub pairs) []

theorem sub_segment (pairs : List Pair) :
    Segment branchMachine (lift (by decide : 27 ≤ 36) 0 (subInitial pairs)) (subSegment pairs)
      (lift (by decide : 27 ≤ 36) 0 (subFinal pairs)) :=
  phase_segment (by decide : 27 ≤ 36) 0 PA17TMDivisionSub001.subMachine family_sub _ _ _ (sub_run pairs)

theorem rewind_segment (b : Bool) (pairs : List Pair) :
    Segment branchMachine (lift (by decide : 5 ≤ 36) (rewindPhase b) (rewindInitial pairs))
      (rewindSegment b pairs) (lift (by decide : 5 ≤ 36) (rewindPhase b) (rewindFinal pairs)) :=
  phase_segment (by decide : 5 ≤ 36) (rewindPhase b) PSTRTMColumnRewind067.rewindMachine
    (family_rewind b) _ _ _ (rewind_run pairs)

theorem zero_segment (pairs : List Pair) :
    Segment branchMachine (lift (by decide : 36 ≤ 36) 3 (zeroInitial pairs))
      (zeroSegment pairs) (lift (by decide : 36 ≤ 36) 3 (zeroFinal pairs)) :=
  phase_segment (by decide : 36 ≤ 36) 3 (ROOTTMGCDMap004.residentMapMachine zeroPair)
    family_zero _ _ _ (zero_run pairs)

theorem sub_transfer (pairs : List Pair) :
    Turing.TM0.step branchMachine (lift (by decide : 27 ≤ 36) 0 (subFinal pairs)) =
      some (lift (by decide : 5 ≤ 36) (rewindPhase (borrow pairs)) (rewindInitial pairs)) :=
  phase_transfer (by decide : 27 ≤ 36) 0 (rewindPhase (borrow pairs)) PA17TMDivisionSub001.subMachine
    family_sub (subFinal pairs) (sub_run pairs).2.2.2 0 (borrow_port (borrow pairs))

theorem rewind_zero_transfer (pairs : List Pair) :
    Turing.TM0.step branchMachine (lift (by decide : 5 ≤ 36) 2 (rewindFinal pairs)) =
      some (lift (by decide : 36 ≤ 36) 3 (zeroInitial pairs)) :=
  phase_transfer (by decide : 5 ≤ 36) 2 3 PSTRTMColumnRewind067.rewindMachine
    (family_rewind true) (rewindFinal pairs) (rewind_run pairs).2.2.2 0 rewind_borrow_port

theorem rewind_ge_halt (pairs : List Pair) :
    Turing.TM0.step branchMachine (lift (by decide : 5 ≤ 36) 1 (rewindFinal pairs)) = none :=
  phase_halt (by decide : 5 ≤ 36) 1 PSTRTMColumnRewind067.rewindMachine
    (family_rewind false) (rewindFinal pairs) (rewind_run pairs).2.2.2 rewind_nonborrow_halt_port

theorem zero_final_halt (pairs : List Pair) :
    Turing.TM0.step branchMachine (lift (by decide : 36 ≤ 36) 3 (zeroFinal pairs)) = none := by
  apply phase_halt (by decide : 36 ≤ 36) 3 (ROOTTMGCDMap004.residentMapMachine zeroPair)
    family_zero (zeroFinal pairs) (zero_run pairs).2.2.2
  exact zero_halt_port

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
