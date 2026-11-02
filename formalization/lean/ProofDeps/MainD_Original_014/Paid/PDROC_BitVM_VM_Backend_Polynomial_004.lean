module

public import Paid.PDROC_BitVM_VM_Backend_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Backend

open Turing PaperProofs.Paid.Computation

variable {Λ σ : Type*} [Fintype Λ] [Inhabited Λ] [Fintype σ] [Inhabited σ]

/-! SOURCE ONLY. The final height is PRODUCED by the same actual source
path. It is not a caller qualification, machine field, workspace input or
numerical oracle. All code-dependent constants precede every input/path. -/

omit [Fintype σ] in
/-- Common003 already derives every initial stack's size from genuine
TM2.init and runs its actual source_path_occupancy induction. Taking the
given last member and the fixed32-stack sup yields the required height. -/
theorem source_final_height_le (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (closed : TM2.Supports source (Finset.univ : Finset Λ))
    (input : List Bool) (sourceTrace : List (SourceState Λ σ)) (sourceFinal : SourceState Λ σ)
    (first : sourceTrace.head? = some (TM2.init (0 : Stack) input))
    (chain : sourceTrace.IsChain (fun before after => TM2.step source before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) :
    Common.IO.Output.stackHeight sourceFinal.stk ≤
      input.length + Common.sourcePushCap source Finset.univ * sourceTrace.length := by
  have occupancy := Common.source_trace_occupancy source Finset.univ closed (0 : Stack)
    input sourceTrace first chain
  have finalWords := (occupancy sourceFinal (List.mem_of_getLast? last)).2
  unfold Common.IO.Output.stackHeight
  exact Finset.sup_le (fun slot _ => finalWords slot)

noncomputable def pathCoefficient (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ) : ℕ :=
  coefficient source * (Common.sourcePushCap source Finset.univ + 2)^2 + 1

omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
theorem pathCoefficient_pos (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ) :
    0 < pathCoefficient source := by unfold pathCoefficient; omega

omit [Fintype σ] in
/-- The old combined budget is bounded using only actual raw length I
and this source list's length N. No assumed final-height bound is needed. -/
theorem budget_of_source_path (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (closed : TM2.Supports source (Finset.univ : Finset Λ))
    (input : List Bool) (sourceTrace : List (SourceState Λ σ)) (sourceFinal : SourceState Λ σ)
    (first : sourceTrace.head? = some (TM2.init (0 : Stack) input))
    (chain : sourceTrace.IsChain (fun before after => TM2.step source before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) :
    budget source input.length sourceTrace.length (Common.IO.Output.stackHeight sourceFinal.stk) ≤
      pathCoefficient source * (input.length + sourceTrace.length + 1)^2 := by
  let I := input.length
  let N := sourceTrace.length
  let K := Common.sourcePushCap source Finset.univ
  let H := Common.IO.Output.stackHeight sourceFinal.stk
  have height : H ≤ I + K * N := source_final_height_le source closed input sourceTrace sourceFinal first chain last
  have linear : I + N + H + 1 ≤ (K + 2) * (I + N + 1) := by
    calc
      I + N + H + 1 ≤ I + N + (I + K * N) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_left height (I + N)) 1
      _ ≤ (I + N + (I + K * N) + 1) + (K * I + N + K + 1) := Nat.le_add_right _ _
      _ = (K + 2) * (I + N + 1) := by ring
  calc
    budget source input.length sourceTrace.length (Common.IO.Output.stackHeight sourceFinal.stk) ≤
        coefficient source * (I + N + H + 1)^2 := budget_quadratic source I N H
    _ ≤ coefficient source * ((K + 2) * (I + N + 1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left linear 2)
    _ = (coefficient source * (K + 2)^2) * (I + N + 1)^2 := by ring
    _ ≤ pathCoefficient source * (input.length + sourceTrace.length + 1)^2 :=
      Nat.mul_le_mul_right _ (by unfold pathCoefficient; change _ ≤ coefficient source * (K + 2)^2 + 1; omega)

omit [Fintype σ] in
/-- Explicit budget weakening for an ALREADY chosen backend list.
The source witness and bit witness are not reselected or altered. -/
theorem selected_clock {α : Type*} (bitTrace : List α)
    (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (closed : TM2.Supports source (Finset.univ : Finset Λ))
    (input : List Bool) (sourceTrace : List (SourceState Λ σ)) (sourceFinal : SourceState Λ σ)
    (first : sourceTrace.head? = some (TM2.init (0 : Stack) input))
    (chain : sourceTrace.IsChain (fun before after => TM2.step source before = some after))
    (last : sourceTrace.getLast? = some sourceFinal)
    (clock : bitTrace.length ≤ budget source input.length sourceTrace.length
      (Common.IO.Output.stackHeight sourceFinal.stk)) :
    bitTrace.length ≤ pathCoefficient source * (input.length + sourceTrace.length + 1)^2 :=
  clock.trans (budget_of_source_path source closed input sourceTrace sourceFinal first chain last)

/-- The same fixed three-stage machine and the same once-selected002
bit trace. Raw6 bootstrap, body, output extraction, HALT and naked right0
are unchanged; only their proved clock/visited upper bound is weakened. -/
theorem uniform_original_raw_backend_polynomial
    (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (closed : TM2.Supports source (Finset.univ : Finset Λ)) :
    ∃ states : ℕ, ∃ code : BitMachine states, ∃ C : ℕ, 0 < C ∧
      ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ)
        (sourceTrace : List (SourceState Λ σ)) (sourceFinal : SourceState Λ σ),
        sourceTrace.head? = some (TM2.init (0 : Stack) (encodeBits (rawInput P fee))) →
        sourceTrace.IsChain (fun before after => TM2.step source before = some after) →
        sourceTrace.getLast? = some sourceFinal → TM2.step source sourceFinal = none →
        0 < (sourceFinal.stk (0 : Stack)).length →
        ∃ trace final,
          BitRuns code (encodeBits (rawInput P fee)) trace final ∧
          final.Tape.right₀ = ListBlank.mk (sourceFinal.stk (0 : Stack)) ∧
          trace.length ≤ C * ((encodeBits (rawInput P fee)).length + sourceTrace.length + 1)^2 ∧
          visitedBitSpace code (encodeBits (rawInput P fee)).length trace ≤
            (encodeBits (rawInput P fee)).length +
              2 * (C * ((encodeBits (rawInput P fee)).length + sourceTrace.length + 1)^2) + 1 ∧
          (∀ count, visitedBitSpace code (encodeBits (rawInput P fee)).length (trace.take count) ≤
            (encodeBits (rawInput P fee)).length +
              2 * (C * ((encodeBits (rawInput P fee)).length + sourceTrace.length + 1)^2) + 1) := by
  refine ⟨_, machine source, pathCoefficient source, pathCoefficient_pos source, ?_⟩
  intro P fee sourceTrace sourceFinal first chain last halt positive
  obtain ⟨trace, final, actual, naked, oldClock, oldSpace⟩ :=
    original_raw_run source closed P fee sourceTrace sourceFinal first chain last halt positive
  have bound := budget_of_source_path source closed (encodeBits (rawInput P fee))
    sourceTrace sourceFinal first chain last
  have clock := oldClock.trans bound
  refine ⟨trace, final, actual, naked, clock, ?_, ?_⟩
  · exact Common.visitedBitSpace_of_clock _ _ _ _ clock
  · intro count
    have before := oldSpace count
    omega

end PDROC.BitVM.VM.Backend
