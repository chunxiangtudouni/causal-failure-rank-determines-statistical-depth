module

public import Paid.PDCompute_SolverBaseRowLoop_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

theorem Frame.trans {before middle after : State} {base n k : ℕ}
    (hfirst : Frame before middle base n k) (hlater : Frame middle after base n k) : Frame before after base n k :=
  ⟨fun address hout => (hlater.1 address hout).trans (hfirst.1 address hout),
    fun address hout => (hlater.2 address hout).trans (hfirst.2 address hout)⟩

theorem baseRowLoopResult_pc (origin count : ℕ) (before : State) (pointer : ℕ) :
    (baseRowLoopResult origin count before pointer).pc=origin+18 := by
  induction count generalizing before pointer with
  | zero => rfl
  | succ count ih => exact ih _ _

theorem baseRowLoopResult_address (origin count : ℕ) (before : State) (pointer : ℕ)
    (hbefore : before.register .address=.natural pointer) :
    (baseRowLoopResult origin count before pointer).register .address=.natural (pointer+6*count) := by
  induction count generalizing before pointer with
  | zero => simpa only [baseRowLoopResult,Nat.mul_zero,Nat.add_zero] using hbefore
  | succ count ih =>
      dsimp only [baseRowLoopResult]
      have h := ih {baseRowWritesResult {before with pc:=origin+2} pointer (count+1) with pc:=origin+1}
        (pointer+6) (by simp [baseRowWritesResult])
      have he : pointer+6+6*count=pointer+6*(count+1) := by omega
      simpa only [he] using h

theorem baseRowLoopResult_index (origin count : ℕ) (before : State) (pointer : ℕ)
    (hbefore : before.register .index=.natural count) :
    (baseRowLoopResult origin count before pointer).register .index=.natural 0 := by
  induction count generalizing before pointer with
  | zero => exact hbefore
  | succ count ih =>
      apply ih
      simp [baseRowWritesResult]

theorem baseRowLoopResult_output (origin count : ℕ) (before : State) (pointer : ℕ) :
    (baseRowLoopResult origin count before pointer).output=before.output := by
  induction count generalizing before pointer with
  | zero => rfl
  | succ count ih =>
      exact ih _ _

theorem baseRowLoopResult_unchanged_register (origin count : ℕ) (before : State) (pointer : ℕ) (register : Register)
    (haddress : register ≠ .address) (hvalue : register ≠ .value) (hindex : register ≠ .index) :
    (baseRowLoopResult origin count before pointer).register register=before.register register := by
  induction count generalizing before pointer with
  | zero => rfl
  | succ count ih =>
      dsimp only [baseRowLoopResult]
      rw [ih]
      simp [baseRowWritesResult,Function.update_of_ne haddress,Function.update_of_ne hvalue,Function.update_of_ne hindex]

theorem baseRowLoopResult_frame (origin count : ℕ) (before : State) (pointer base n k : ℕ)
    (hinside : ∀ offset < 6*count, pointer+offset ∈ workspace base n k) :
    Frame before (baseRowLoopResult origin count before pointer) base n k := by
  induction count generalizing before pointer with
  | zero => exact ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
  | succ count ih =>
      let start : State := {before with pc:=origin+2}
      let returned : State := {baseRowWritesResult start pointer (count+1) with pc:=origin+1}
      have hfirst : Frame before returned base n k :=
        baseRowWrites_frame start pointer (count+1) base n k (fun offset hoff => hinside offset (by omega))
      have hlater := ih returned (pointer+6) (fun offset hoff => by
        have h := hinside (offset+6) (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
      exact hfirst.trans hlater

end PDCompute.Solver
