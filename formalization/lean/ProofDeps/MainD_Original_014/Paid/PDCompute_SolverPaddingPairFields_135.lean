module

public import Paid.PDCompute_SolverPaddingPairs_132

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute writeCell)

/-- Pure execution facts for the same literal pairs. They give actual
boundary registers/PCs for prefix composition, never desired heap data. -/
theorem paddingPairs_execute_fields (copies : ℕ) (input : List Cell) (before : State) (pointer : ℕ)
    (address : before.register .address=.natural pointer) (one : before.register .flag=.natural 1) :
    ∃ after,linearExecute input (paddingPairsCode copies) before=some after ∧
      after.register .address=.natural (pointer+copies) ∧ after.register .flag=.natural 1 ∧
      (∀ register,register ≠ .address → after.register register=before.register register) ∧
      after.pc=before.pc+2*copies := by
  induction copies generalizing before pointer with
  | zero => exact ⟨before,rfl,by simpa only [Nat.add_zero] using address,one,fun _ _ => rfl,rfl⟩
  | succ copies ih =>
    let middle:=paddingPairResult before pointer
    have firstRun:=paddingPair_execute input before pointer address one
    have middleAddress : middle.register .address=.natural (pointer+1) := by simp [middle,paddingPairResult,State.set]
    have unchanged (register : Register) (different : register ≠ .address) : middle.register register=before.register register := by
      simp only [middle,paddingPairResult,State.set,writeCell,Function.update_of_ne different]
    have middleOne : middle.register .flag=.natural 1 := (unchanged .flag (by decide)).trans one
    have middlePC : middle.pc=before.pc+2 := rfl
    obtain ⟨after,run,afterAddress,afterOne,preserve,afterPC⟩:=ih middle (pointer+1) middleAddress middleOne
    refine ⟨after,?_,?_,afterOne,?_,?_⟩
    · rw [paddingPairsCode,PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some]
      exact run
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using afterAddress
    · exact fun register different => (preserve register different).trans (unchanged register different)
    · calc
        after.pc = middle.pc+2*copies := afterPC
        _ = before.pc+2*(copies+1) := by rw [middlePC]; ring

end PDCompute.Solver
