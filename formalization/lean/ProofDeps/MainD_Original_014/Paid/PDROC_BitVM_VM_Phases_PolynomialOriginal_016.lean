module

public import Paid.PDROC_BitVM_VM_Phases_Polynomial_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Polynomial

/-- Pure scalar clock algebra. No numerical implementation, input model,
or concrete RAM program is imported through this proof predicate. -/
def ScalarBound (value : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ S : ℕ, 1 ≤ S → value S ≤ C * S^d

theorem ScalarBound.constant (n : ℕ) : ScalarBound (fun _ => n) :=
  ⟨n+1, 0, by omega, by intro S _; simp only [pow_zero, Nat.mul_one]; omega⟩

theorem ScalarBound.identity : ScalarBound (fun S => S) :=
  ⟨1, 1, by decide, by intro S _; simp only [pow_one, Nat.one_mul]; exact Nat.le_refl _⟩

theorem ScalarBound.mono {f g : ℕ → ℕ} (bound : ScalarBound g)
    (smaller : ∀ S, 1 ≤ S → f S ≤ g S) : ScalarBound f := by
  obtain ⟨C,d,positive,clock⟩ := bound
  exact ⟨C,d,positive,fun S hS => (smaller S hS).trans (clock S hS)⟩

theorem ScalarBound.add {f g : ℕ → ℕ} (first : ScalarBound f) (second : ScalarBound g) :
    ScalarBound (fun S => f S + g S) := by
  obtain ⟨C,d,positiveC,hf⟩ := first
  obtain ⟨K,e,positiveK,hg⟩ := second
  refine ⟨C+K,d+e,by omega,?_⟩
  intro S hS
  have fd := Nat.pow_le_pow_right hS (Nat.le_add_right d e)
  have ge := Nat.pow_le_pow_right hS (Nat.le_add_left e d)
  calc
    f S + g S ≤ C * S^(d+e) + K * S^(d+e) :=
      Nat.add_le_add ((hf S hS).trans (Nat.mul_le_mul_left C fd))
        ((hg S hS).trans (Nat.mul_le_mul_left K ge))
    _ = (C+K) * S^(d+e) := by ring

theorem ScalarBound.mul {f g : ℕ → ℕ} (first : ScalarBound f) (second : ScalarBound g) :
    ScalarBound (fun S => f S * g S) := by
  obtain ⟨C,d,positiveC,hf⟩ := first
  obtain ⟨K,e,positiveK,hg⟩ := second
  refine ⟨C*K,d+e,Nat.mul_pos positiveC positiveK,?_⟩
  intro S hS
  calc
    f S * g S ≤ (C*S^d) * (K*S^e) := Nat.mul_le_mul (hf S hS) (hg S hS)
    _ = (C*K) * S^(d+e) := by rw [pow_add]; ring

theorem ScalarBound.power {f : ℕ → ℕ} (first : ScalarBound f) (d : ℕ) :
    ScalarBound (fun S => (f S)^d) := by
  induction d with
  | zero => simpa only [pow_zero] using ScalarBound.constant 1
  | succ d ih => simpa only [pow_succ] using ih.mul first

theorem stageBudget_scalar {P Q D : ℕ → ℕ} (C stage : ℕ)
    (prepare : ScalarBound P) (core : ScalarBound Q) (data : ScalarBound D) :
    ScalarBound (fun S => stageBudget C (P S) (Q S) stage (D S)) := by
  by_cases atPrepare : stage = 2
  · simpa only [stageBudget, atPrepare, ↓reduceIte] using prepare
  by_cases atCore : stage = 6
  · simp only [stageBudget, ite_eq_right atPrepare, ite_eq_left atCore]
    exact core
  simpa only [stageBudget, atPrepare, atCore, ↓reduceIte] using
    (ScalarBound.constant C).mul ((data.add (ScalarBound.constant 1)).power 3)

theorem dataAfter_scalar {I P Q : ℕ → ℕ} (C K : ℕ)
    (input : ScalarBound I) (prepare : ScalarBound P) (core : ScalarBound Q) :
    ∀ stage, ScalarBound (fun S => dataAfter C K (I S) (P S) (Q S) stage) := by
  intro stage
  induction stage with
  | zero => exact input
  | succ stage ih =>
    exact (ScalarBound.constant 32).mul
      (ih.add ((ScalarBound.constant K).mul (stageBudget_scalar C stage prepare core ih)))

theorem prefixBudget_scalar {I P Q : ℕ → ℕ} (C K : ℕ)
    (input : ScalarBound I) (prepare : ScalarBound P) (core : ScalarBound Q) :
    ∀ stage, ScalarBound (fun S => prefixBudget C K (I S) (P S) (Q S) stage) := by
  intro stage
  induction stage with
  | zero => exact ScalarBound.constant 0
  | succ stage ih =>
    exact ih.add
      (stageBudget_scalar C stage prepare core (dataAfter_scalar C K input prepare core stage))

theorem schedule8_scalar {I P Q : ℕ → ℕ} (C K : ℕ)
    (input : ScalarBound I) (prepare : ScalarBound P) (core : ScalarBound Q) :
    ScalarBound (fun S => schedule8 C K (I S) (P S) (Q S)) :=
  (prefixBudget_scalar C K input prepare core 8).add (ScalarBound.constant 1)

end PDROC.BitVM.VM.Phases.Polynomial
