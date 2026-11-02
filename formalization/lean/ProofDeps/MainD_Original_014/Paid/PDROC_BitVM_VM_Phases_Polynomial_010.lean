module

public import Paid.PDROC_BitVM_Kernel_NatInstruction_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Polynomial

/-! SOURCE ONLY, pure arithmetic. C and K are fixed code constants before
ALL inputs. Stage2 is actual prepare cost P, stage6 actual core cost Q;
the six other stages use the same caller-data cubic. This module asserts
no source path or original implementation claim. -/

def stageBudget (C P Q stage D : ℕ) : ℕ :=
  if stage = 2 then P else if stage = 6 then Q else C * (D + 1)^3

def nextData (K D B : ℕ) : ℕ := 32 * (D + K * B)

def dataAfter (C K I P Q : ℕ) : ℕ → ℕ
  | 0 => I
  | stage + 1 => nextData K (dataAfter C K I P Q stage)
      (stageBudget C P Q stage (dataAfter C K I P Q stage))

def prefixBudget (C K I P Q : ℕ) : ℕ → ℕ
  | 0 => 0
  | stage + 1 => prefixBudget C K I P Q stage +
      stageBudget C P Q stage (dataAfter C K I P Q stage)

/-- B0+B1+P+B3+B4+B5+Q+B7+1, with every Di produced by nextData.
The final+1 is the full-list initial state; real path accounting is external. -/
def schedule8 (C K I P Q : ℕ) : ℕ := prefixBudget C K I P Q 8 + 1

theorem stageBudget_mono (C stage : ℕ) {P Q D P' Q' D' : ℕ}
    (prepare : P ≤ P') (core : Q ≤ Q') (data : D ≤ D') :
    stageBudget C P Q stage D ≤ stageBudget C P' Q' stage D' := by
  by_cases atPrepare : stage = 2
  · simpa only [stageBudget, atPrepare, ↓reduceIte] using prepare
  by_cases atCore : stage = 6
  · simp only [stageBudget, ite_eq_right atPrepare, ite_eq_left atCore]
    exact core
  simpa only [stageBudget, atPrepare, atCore, ↓reduceIte] using
    Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.succ_le_succ data) 3)

theorem nextData_mono (K : ℕ) {D B D' B' : ℕ} (data : D ≤ D') (cost : B ≤ B') :
    nextData K D B ≤ nextData K D' B' :=
  Nat.mul_le_mul_left 32 (Nat.add_le_add data (Nat.mul_le_mul_left K cost))

theorem dataAfter_mono (C K : ℕ) {I P Q I' P' Q' : ℕ}
    (input : I ≤ I') (prepare : P ≤ P') (core : Q ≤ Q') :
    ∀ stage, dataAfter C K I P Q stage ≤ dataAfter C K I' P' Q' stage := by
  intro stage
  induction stage with
  | zero => exact input
  | succ stage ih => exact nextData_mono K ih (stageBudget_mono C stage prepare core ih)

theorem prefixBudget_mono (C K : ℕ) {I P Q I' P' Q' : ℕ}
    (input : I ≤ I') (prepare : P ≤ P') (core : Q ≤ Q') :
    ∀ stage, prefixBudget C K I P Q stage ≤ prefixBudget C K I' P' Q' stage := by
  intro stage
  induction stage with
  | zero => exact Nat.le_refl 0
  | succ stage ih =>
    exact Nat.add_le_add ih
      (stageBudget_mono C stage prepare core (dataAfter_mono C K input prepare core stage))

theorem schedule8_mono (C K : ℕ) {I P Q I' P' Q' : ℕ}
    (input : I ≤ I') (prepare : P ≤ P') (core : Q ≤ Q') :
    schedule8 C K I P Q ≤ schedule8 C K I' P' Q' :=
  Nat.add_le_add_right (prefixBudget_mono C K input prepare core 8) 1

end PDROC.BitVM.VM.Phases.Polynomial
