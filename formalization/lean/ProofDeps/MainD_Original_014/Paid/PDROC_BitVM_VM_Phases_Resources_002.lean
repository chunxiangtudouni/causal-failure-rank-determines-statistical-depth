module

public import Paid.PDROC_BitVM_VM_Phases_Resources_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Resources

open PaperProofs.Paid.Computation
open scoped BigOperators

/-! SOURCE ONLY. A fixed positive coefficient precedes ALL input/caller
words. The trace lemmas transfer the clock of an ALREADY selected callee;
in particular they cannot replace Calls' semantic witness. -/

def coefficient : ℕ :=
  2000 + 258 + Codec.Finalize.callerTimeCoefficient + Codec.Finalize.callerSpaceCoefficient + 1

theorem coefficient_pos : 0 < coefficient := by unfold coefficient; omega

theorem linear_le_cube (size : ℕ) : size + 1 ≤ (size + 1)^3 := by
  have grow := Nat.pow_le_pow_right (by omega : 1 ≤ size + 1) (by decide : 1 ≤ 3)
  simpa only [pow_one] using grow

theorem linear_le_uniform (contents : Stack → List Bool) (localCoefficient : ℕ)
    (bounded : localCoefficient ≤ coefficient) :
    localCoefficient * (dataSize contents + 1) ≤ coefficient * (dataSize contents + 1)^3 :=
  Nat.mul_le_mul bounded (linear_le_cube (dataSize contents))

theorem mount_uniform (cells : List Cell) (suffix : List Bool) (contents : Stack → List Bool)
    (input : contents 0 = encodeBits cells ++ suffix) :
    1000 * (Log.BankMount.preCap contents + (encodeBits cells).length + 1) ≤
      coefficient * (dataSize contents + 1)^3 :=
  (mount_budget_le cells suffix contents input).trans
    (linear_le_uniform contents 2000 (by unfold coefficient; omega))

theorem reset_uniform (contents : Stack → List Bool) :
    32 * ((∑ role : Stack, (contents role).length) + 7) + 2 ≤
      coefficient * (dataSize contents + 1)^3 :=
  (reset_budget_le contents).trans
    (linear_le_uniform contents 258 (by unfold coefficient; omega))

theorem finalize_uniform (contents : Stack → List Bool) :
    Codec.Finalize.timeBudget contents ≤ coefficient * (dataSize contents + 1)^3 :=
  (finalize_budget_le contents).trans
    (Nat.mul_le_mul_right _ (by unfold coefficient; omega))

theorem finalize_space_uniform (contents : Stack → List Bool) :
    Codec.Finalize.spaceBudget contents ≤ coefficient * (dataSize contents + 1)^3 :=
  (finalize_space_budget_le contents).trans
    (Nat.mul_le_mul_right _ (by unfold coefficient; omega))

/-- The quantifier order is explicit: this single fixed C and degree3
work for both mounting phases, both resets and both finalizers. -/
theorem uniform_components :
    ∃ C degree : ℕ, 0 < C ∧ 0 < degree ∧
      (∀ (cells : List Cell) (suffix : List Bool) (contents : Stack → List Bool),
        contents 0 = encodeBits cells ++ suffix →
        1000 * (Log.BankMount.preCap contents + (encodeBits cells).length + 1) ≤
          C * (dataSize contents + 1)^degree) ∧
      (∀ contents : Stack → List Bool,
        32 * ((∑ role : Stack, (contents role).length) + 7) + 2 ≤
          C * (dataSize contents + 1)^degree) ∧
      (∀ contents : Stack → List Bool,
        Codec.Finalize.timeBudget contents ≤ C * (dataSize contents + 1)^degree) ∧
      (∀ contents : Stack → List Bool,
        Codec.Finalize.spaceBudget contents ≤ C * (dataSize contents + 1)^degree) :=
  ⟨coefficient, 3, coefficient_pos, by decide,
    mount_uniform, reset_uniform, finalize_uniform, finalize_space_uniform⟩

theorem mount_selected {α : Type*} (run : List α) (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (input : contents 0 = encodeBits cells ++ suffix)
    (clock : run.length ≤ 1000 * (Log.BankMount.preCap contents + (encodeBits cells).length + 1)) :
    run.length ≤ coefficient * (dataSize contents + 1)^3 :=
  clock.trans (mount_uniform cells suffix contents input)

theorem reset_selected {α : Type*} (run : List α) (contents : Stack → List Bool)
    (clock : run.length ≤ 32 * ((∑ role : Stack, (contents role).length) + 7) + 2) :
    run.length ≤ coefficient * (dataSize contents + 1)^3 :=
  clock.trans (reset_uniform contents)

theorem finalize_selected {α : Type*} (run : List α) (contents : Stack → List Bool)
    (clock : run.length ≤ Codec.Finalize.timeBudget contents) :
    run.length ≤ coefficient * (dataSize contents + 1)^3 :=
  clock.trans (finalize_uniform contents)

/-- A later source-boundary envelope may be substituted here. It is a
proved bound on actual caller data, never extra machine input or fuel. -/
theorem substitute_entry_envelope (contents : Stack → List Bool) (envelope : ℕ)
    (bounded : dataSize contents ≤ envelope) :
    coefficient * (dataSize contents + 1)^3 ≤ coefficient * (envelope + 1)^3 :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

end PDROC.BitVM.VM.Phases.Resources
