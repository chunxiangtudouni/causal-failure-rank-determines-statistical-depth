module
public import Structure.PA17_TM_RatArithmetic_Outer_025d

/-! Original-input/actual-memory bridge for a proved allocation body.
This is still a conditional composition theorem until the concrete023 body
discharges bodyRun. No original target is counted closed by this premise. -/
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014

def bankAt (x y : Rat) (n : Nat) : List Bool :=
  originalBank x y (List.replicate n false++[true])

/-- The body machine is chosen before all original x,y. Its real run
contracts must be proved, not supplied as tape or callee-answer fields. -/
theorem raw_allocation_from_body {states : Nat} (body : Machine states) (k : Nat)
    (bodyRun : ∀ (x y : Rat) (h n : Nat), ∃ trace,
      PSTRTMSeq005.RunsFrom body
        ⟨0,(popNxFound h (sign x) (bankAt x y n)).Tape⟩ trace
        ⟨Fin.last states,(popNxInitial h (sign x) (bankAt x y (n+k*fieldWidth x y))).Tape⟩ ∧
      trace.length≤passFee k (fieldWidth x y) n)
    (x y : Rat) :
    ∃ trace, Runs (rawLoopMachine body) (encode [.rational x,.rational y]) trace
      (rawLoopSavedFinal body (mNx x y) (sign x) (bankAt x y (k*(fieldWidth x y)^2))) ∧
      trace.length≤(16*k+512)*(fieldWidth x y+1)^4 := by
  let w := fieldWidth x y
  let rawTape := Tape.mk₂ (false::ROOTTMGCDCounter011.ones w)
    (prefixRight (sign x) (originalBank x y [true]))
  obtain ⟨rawTrace,rawRun,rawTime⟩ := raw_width_runs x y
  have rawFrom : PSTRTMSeq005.RunsFrom widthMachine
      (TM0.init (encode [.rational x,.rational y])) rawTrace (widthFinal (mNx x y) rawTape) :=
    ⟨rawRun.1,rawRun.2.1,rawRun.2.2.1,rawRun.2.2.2.1⟩
  have rawPad := pad_runsFrom
    (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) widthMachine _ _ _ rawFrom
  have rawFamily : rawLoopFamily body (0 : Fin 33)=
      padMachine (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) widthMachine := by
    simp [rawLoopFamily]
  rw [←rawFamily] at rawPad
  have rawSegment := block_segment (rawLoopFamily body) (rawLoopPorts states) (0 : Fin 33) _ _ _ rawPad
  obtain ⟨loopTrace,loopRun,loopTime⟩ := loop_runsFrom body (sign x) (bankAt x y) (k*w)
    (passFee k w) (bodyRun x y) w 0
  have loopLift := rawLoop_saved_runsFrom body (mNx x y) _ _ _ loopRun
  have join : blockCfg (savedPhase (mNx x y))
      (padCfg (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states)
        (loopInitial body w (sign x) (bankAt x y 0))) = rawLoopSavedEntry body (mNx x y) rawTape := by
    simp [loopInitial,rawLoopSavedEntry,popNxInitial,bankAt,rawTape,padCfg,padLabel,blockCfg,label,
      ROOTTMGCDPop016.state]
  have transfer := rawLoop_actual_transfer body (mNx x y) rawTape rawFrom.2.2.2
  rw [←join] at transfer
  let rawGlobal : List (MachineState (totalStates 32 (rawLoopCapacity states))) :=
    (rawTrace.map (padCfg (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states))).map
      (blockCfg (0 : Fin 33))
  let loopGlobal : List (MachineState (totalStates 32 (rawLoopCapacity states))) :=
    (loopTrace.map (padCfg
      (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states))).map
      (blockCfg (savedPhase (mNx x y)))
  have tailSegment : Segment (rawLoopMachine body) _ loopGlobal _ :=
    ⟨loopLift.1,loopLift.2.1,loopLift.2.2.1⟩
  have fullSegment := segment_append (rawLoopMachine body) _ _ _ _ rawGlobal loopGlobal
    rawSegment tailSegment transfer
  have index : 0+(k*w)*w=k*w^2 := by ring
  have fullRun : Runs (rawLoopMachine body) (encode [.rational x,.rational y]) (rawGlobal++loopGlobal)
      (rawLoopSavedFinal body (mNx x y) (sign x) (bankAt x y (k*w^2))) := by
    apply PSTRTMTrace002.runs_of_chain
    · simpa [TM0.init,padCfg,padLabel,blockCfg,label] using fullSegment.1
    · exact fullSegment.2.1
    · simpa only [rawLoopSavedFinal,index] using fullSegment.2.2
    · simpa only [rawLoopSavedFinal,index] using loopLift.2.2.2
  have loopBound := allocation_loopCost_le k w
  have square : (w+1)^2≤(w+1)^4 :=
    Nat.pow_le_pow_right (by omega : 1≤w+1) (by decide : 2≤4)
  have length : (rawGlobal++loopGlobal).length=rawTrace.length+loopTrace.length := by
    simp only [rawGlobal,loopGlobal,List.length_append,List.length_map]
  refine ⟨rawGlobal++loopGlobal,fullRun,?_⟩
  rw [length]
  have rawTime' : rawTrace.length≤256*(w+1)^2 := rawTime
  calc
    _ ≤ 256*(w+1)^4+(16*k+256)*(w+1)^4 :=
      Nat.add_le_add (rawTime'.trans (Nat.mul_le_mul_left 256 square)) (loopTime.trans loopBound)
    _ = (16*k+512)*(w+1)^4 := by ring

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025
