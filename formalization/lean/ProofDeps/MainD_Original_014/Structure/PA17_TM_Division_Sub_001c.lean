module
public import Structure.PA17_TM_Division_Sub_001b
public import Common.PSTR_TM_ColumnRewind_067

/-! Same-tape subtraction followed by a real marker-driven rewind. The
separate scan API retains arbitrary incoming/outgoing borrow in control. -/
@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionSub001
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def residentSubMachine : Machine 33 := PSTRTMSeq005.seqMachine subMachine PSTRTMColumnRewind067.rewindMachine

def residentSubTrace (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : List (MachineState 33) :=
  (subTrace false (false :: archive) [] pairs suffix).map (PSTRTMSeq005.leftCfg (b := 5)) ++
    (PSTRTMColumnRewind067.fullTrace archive (subPairs false pairs).reverse (false :: false :: suffix)).map
      (PSTRTMSeq005.rightCfg (a := 27))

def residentSubInitial (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : MachineState 33 :=
  PSTRTMSeq005.leftCfg (b := 5) (state (readA false) (false :: archive) (operandColumns pairs ++ false :: false :: suffix))

def residentSubFinal (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : MachineState 33 :=
  PSTRTMSeq005.rightCfg (a := 27) (PSTRTMColumnRewind067.state 5 (false :: archive)
    (operandColumns (subPairs false pairs) ++ false :: false :: suffix))

/-- Uniform genuine resident subtraction for every finite pair list, including
underflow and zero width. The computed modular result is never reloaded. -/
theorem residentSub_runsFrom (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom residentSubMachine (residentSubInitial archive pairs suffix)
      (residentSubTrace archive pairs suffix) (residentSubFinal archive pairs suffix) := by
  apply PSTRTMSeq005.seq_runsFrom subMachine PSTRTMColumnRewind067.rewindMachine
    (state (readA false) (false :: archive) (operandColumns pairs ++ false :: false :: suffix))
    (state (haltLabel (finalBorrow false pairs))
      (leftColumns (subPairs false pairs).reverse ++ false :: archive) (false :: false :: suffix))
    (PSTRTMColumnRewind067.state 5 (false :: archive) (operandColumns (subPairs false pairs) ++ false :: false :: suffix))
    (subTrace false (false :: archive) [] pairs suffix)
    (PSTRTMColumnRewind067.fullTrace archive (subPairs false pairs).reverse (false :: false :: suffix))
  · exact sub_runsFrom false (false :: archive) pairs suffix
  · exact PSTRTMColumnRewind067.rewind_runsFrom archive (subPairs false pairs) (false :: false :: suffix)

theorem residentSub_length (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (residentSubTrace archive pairs suffix).length = 13 * pairs.length + 6 := by
  simp only [residentSubTrace, List.length_append, List.length_map, sub_length,
    PSTRTMColumnRewind067.full_length, List.length_reverse, subPairs_length]
  omega

theorem residentSub_final_tape (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (residentSubFinal archive pairs suffix).Tape =
      Turing.Tape.mk₂ (false :: archive) (operandColumns (subPairs false pairs) ++ false :: false :: suffix) := rfl

theorem residentSub_visitedSpace_le (archive : List Bool) (pairs : List (Bool × Bool))
    (suffix : List Bool) (inputLength : Nat) :
    visitedSpace residentSubMachine inputLength (residentSubTrace archive pairs suffix) ≤ inputLength + 26 * pairs.length + 13 := by
  have hs := PSTRTMTrace002.visitedSpace_le residentSubMachine inputLength (residentSubTrace archive pairs suffix)
  rw [residentSub_length] at hs
  omega

theorem residentSub_eval (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    residentSubFinal archive pairs suffix ∈ StateTransition.eval (Turing.TM0.step residentSubMachine)
      (residentSubInitial archive pairs suffix) := by
  have h := residentSub_runsFrom archive pairs suffix
  exact StateTransition.mem_eval.mpr ⟨PSTRTMTrace002.chain_reaches _ _ _ _ h.1 h.2.1 h.2.2.1, h.2.2.2⟩

/-- The caller's actual comparison can establish hge internally. It is a
local branch fact, not a qualification on the final original division input. -/
theorem residentSub_exact (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool)
    (hge : secondValue pairs ≤ firstValue pairs) :
    PSTRTMSeq005.RunsFrom residentSubMachine (residentSubInitial archive pairs suffix)
      (residentSubTrace archive pairs suffix) (residentSubFinal archive pairs suffix) ∧
      firstValue (subPairs false pairs) = firstValue pairs - secondValue pairs ∧
      secondValue (subPairs false pairs) = secondValue pairs ∧ finalBorrow false pairs = false :=
  ⟨residentSub_runsFrom archive pairs suffix, (subtraction_exact pairs hge).2,
    secondValue_subPairs false pairs, (subtraction_exact pairs hge).1⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionSub001
