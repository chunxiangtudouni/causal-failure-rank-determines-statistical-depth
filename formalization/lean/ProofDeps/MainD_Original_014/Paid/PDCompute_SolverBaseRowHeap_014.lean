module

public import Paid.PDCompute_SolverBaseRowResult_013
public import Paid.PDLower_CalibrationCompute_HeapList_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

theorem baseRowLoopResult_live_mono (origin count : ℕ) (before : State) (pointer : ℕ) :
    before.live ⊆ (baseRowLoopResult origin count before pointer).live := by
  induction count generalizing before pointer with
  | zero => exact fun _ h => h
  | succ count ih =>
      let start : State := {before with pc:=origin+2}
      let returned : State := {baseRowWritesResult start pointer (count+1) with pc:=origin+1}
      intro address hm
      apply ih returned (pointer+6)
      simp [returned,baseRowWritesResult,start,hm]

theorem baseRowLoopResult_heap_below (origin count : ℕ) (before : State) (pointer address : ℕ)
    (hbelow : address < pointer) :
    (baseRowLoopResult origin count before pointer).heap address=before.heap address := by
  induction count generalizing before pointer with
  | zero => rfl
  | succ count ih =>
      let start : State := {before with pc:=origin+2}
      let returned : State := {baseRowWritesResult start pointer (count+1) with pc:=origin+1}
      change (baseRowLoopResult origin count returned (pointer+6)).heap address=before.heap address
      rw [ih returned (pointer+6) (by omega)]
      have hne : ∀ offset : ℕ, address ≠ pointer+offset := by intro offset; omega
      simp only [returned,baseRowWritesResult,Function.update_apply]
      rw [ite_eq_right (hne 5),ite_eq_right (hne 4),ite_eq_right (hne 3),ite_eq_right (hne 2),ite_eq_right (hne 1)]
      have hz : address ≠ pointer := by omega
      rw [ite_eq_right hz]

/-- Every actual base-row entry is present in live heap and has EXACTLY
the dense original finishEntry; earlier entries survive all later writes. -/
theorem baseRowLoopResult_entries (origin count : ℕ) (before : State) (pointer : ℕ) :
    ∀ index, index < count → HeapList (baseRowLoopResult origin count before pointer)
      (pointer+6*index) (denseEncodeEntry finishEntry) := by
  induction count generalizing before pointer with
  | zero => intro index hi; omega
  | succ count ih =>
      intro index hi
      let start : State := {before with pc:=origin+2}
      let returned : State := {baseRowWritesResult start pointer (count+1) with pc:=origin+1}
      change HeapList (baseRowLoopResult origin count returned (pointer+6)) (pointer+6*index) _
      cases index with
      | zero =>
          simp only [Nat.mul_zero,Nat.add_zero]
          have hfirst : HeapList returned pointer (denseEncodeEntry finishEntry) :=
            baseRowWrites_heapList start pointer (count+1)
          change PDLower.CalibrationCompute.HeapList _ _ _
          apply PDLower.CalibrationCompute.HeapList.of_values
          · intro offset hoff
            exact baseRowLoopResult_live_mono origin count returned (pointer+6) (hfirst.1 offset hoff)
          · intro offset hoff
            have hb : pointer+offset < pointer+6 := by change offset < 6 at hoff; omega
            rw [baseRowLoopResult_heap_below origin count returned (pointer+6) (pointer+offset) hb]
            exact PDLower.CalibrationCompute.HeapList.value hfirst offset hoff
      | succ index =>
          have h := ih returned (pointer+6) index (by omega)
          have hp : pointer+6+6*index=pointer+6*(index+1) := by omega
          rw [hp] at h
          exact h

end PDCompute.Solver
