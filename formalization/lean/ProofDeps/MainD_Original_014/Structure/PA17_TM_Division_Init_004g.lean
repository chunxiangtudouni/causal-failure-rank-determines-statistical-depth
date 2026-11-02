module
public import Structure.PA17_TM_Division_Init_004f
public import Structure.PA17_TM_Division_Tape_005a

/-! Entire standard rawPack tape to a genuinely materialized archive and
zero resident remainder, with the real head returned to resident column0. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

theorem init_initial_tape (pairs : List (Bool × Bool)) :
    (copyState pairs.reverse []).Tape = Turing.Tape.mk₁ (operandColumns pairs) := by
  change Turing.Tape.mk₂ (sep (archiveLeft [])) (residentWord pairs.reverse []) = _
  simpa [sep,archiveLeft,archivePairs,residentWord,markedColumns,leftColumns] using
    PA17TMDivisionTape005.initial_owned00 (operandColumns pairs)

theorem init_initial_eq (pairs : List (Bool × Bool)) :
    initInitial pairs = Turing.TM0.init (operandColumns pairs) := by
  change (⟨0,(copyState pairs.reverse []).Tape⟩ : MachineState 72) = ⟨0,Turing.Tape.mk₁ (operandColumns pairs)⟩
  rw [init_initial_tape]

/-- Exact whole-Tape contract, including all blank cells outside the displayed
archive/resident, three false separators and a real zero high column. -/
theorem init_final_tape (pairs : List (Bool × Bool)) :
    (initFinal pairs).Tape =
      Turing.Tape.mk₂
        (false::false::false::(operandColumns (pairs.map (fun pair => (pair.1,true)))).reverse)
        (operandColumns (pairs.map (fun pair => (false,pair.2)) ++ [(false,false)]) ++ [false,false]) := by
  change Turing.Tape.mk₂ (sep (archiveLeft pairs)) (operandColumns (residentHigh pairs)) =
    Turing.Tape.mk₂ (false::false::false::(operandColumns (archivePairs pairs)).reverse)
      (operandColumns (residentHigh pairs) ++ [false,false])
  unfold sep archiveLeft
  rw [PA17TMDivisionTape005.leftColumns_reverse]
  exact (PA17TMDivisionTape005.tape_owned00 _ _).symm

theorem init_final_label (pairs : List (Bool × Bool)) : (initFinal pairs).q = 72 := rfl

theorem init_runsFrom (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom initMachine (Turing.TM0.init (operandColumns pairs)) (initTrace pairs) (initFinal pairs) := by
  rw [← init_initial_eq]
  exact init_retained_runsFrom pairs

/-- Original Runs includes actual HALT and eval membership. No reset, head
teleport, prepared archive, numeric fuel or input-width argument is used. -/
theorem init_runs (pairs : List (Bool × Bool)) :
    Runs initMachine (operandColumns pairs) (initTrace pairs) (initFinal pairs) := by
  have h := init_runsFrom pairs
  exact PSTRTMTrace002.runs_of_chain initMachine (operandColumns pairs) (initTrace pairs) (initFinal pairs)
    h.1 h.2.1 h.2.2.1 h.2.2.2

theorem firstValue_residentHigh (pairs : List (Bool × Bool)) : firstValue (residentHigh pairs) = 0 := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit false (firstValue (residentHigh later)) = 0
    rw [ih]
    rfl

theorem secondValue_residentHigh (pairs : List (Bool × Bool)) : secondValue (residentHigh pairs) = secondValue pairs := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit b (secondValue (residentHigh later)) = Nat.bit b (secondValue later)
    rw [ih]

theorem firstValue_archivePairs (pairs : List (Bool × Bool)) : firstValue (archivePairs pairs) = firstValue pairs := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit a (firstValue (archivePairs later)) = Nat.bit a (firstValue later)
    rw [ih]

theorem init_computes (pairs : List (Bool × Bool)) :
    computes initMachine (operandColumns pairs)
      (operandColumns (residentHigh pairs) ++ [false,false])
      (64*(pairs.length+1)^2) (256*(pairs.length+1)^2) := by
  refine ⟨initTrace pairs,initFinal pairs,init_runs pairs,?_,init_length_le pairs,init_visitedSpace_le pairs⟩
  rw [init_final_tape]
  simp [Turing.Tape.mk₂,residentHigh,residentPairs]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
