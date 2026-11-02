module

public import Paid.PDROC_BitVM_VM_Backend_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Backend

open Turing PaperProofs.Paid.Computation
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

variable {Λ σ : Type*} [Fintype Λ] [Inhabited Λ] [Fintype σ] [Inhabited σ]

/-! SOURCE ONLY. Only symbolic polynomial bookkeeping is new here.
The scanner, fixed alphabet compiler, sequential composition and visited
space formulas are the previously checked implementations/theorems.
Conversion to original variableGammaSize/rawSize belongs to the parent. -/

noncomputable def bodyCoefficient (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ) : ℕ :=
  SupportClock.clock
    (TM1to1.tr (FiniteTrackCodec.encode (count := 32)) FiniteTrackCodec.decode (TM2to1.tr source))
    (TM1to1.trSupp (TM2to1.tr source) (TM2to1.trSupp source Finset.univ)) *
      (Common.alphabetWriteCap (TM2to1.tr source) (TM2to1.trSupp source Finset.univ) *
        Common.sourceTM1Coefficient source Finset.univ + 1) + 1

omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
theorem bodyBudget_quadratic (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (inputLength sourceLength : ℕ) :
    bodyBudget source inputLength sourceLength ≤
      bodyCoefficient source * (inputLength + sourceLength + 1)^2 := by
  let U := inputLength + sourceLength + 1
  let A := Common.alphabetWriteCap (TM2to1.tr source) (TM2to1.trSupp source Finset.univ)
  let C := Common.sourceTM1Coefficient source Finset.univ
  let S := SupportClock.clock
    (TM1to1.tr (FiniteTrackCodec.encode (count := 32)) FiniteTrackCodec.decode (TM2to1.tr source))
    (TM1to1.trSupp (TM2to1.tr source) (TM2to1.trSupp source Finset.univ))
  have positive : 1 ≤ U^2 := Nat.one_le_pow' 2 (inputLength + sourceLength)
  have trackTime : Common.sourceTM1Budget source Finset.univ inputLength sourceLength ≤ C * U^2 :=
    Common.sourceTM1Budget_quadratic source Finset.univ inputLength sourceLength
  change bodyBudget source inputLength sourceLength ≤ (S * (A * C + 1) + 1) * U^2
  calc
    bodyBudget source inputLength sourceLength =
        S * (A * Common.sourceTM1Budget source Finset.univ inputLength sourceLength + 1) + 1 := rfl
    _ ≤ S * (A * (C * U^2) + U^2) + U^2 :=
      Nat.add_le_add (Nat.mul_le_mul_left S
        (Nat.add_le_add (Nat.mul_le_mul_left A trackTime) positive)) positive
    _ = (S * (A * C + 1) + 1) * U^2 := by ring

noncomputable def coefficient (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ) : ℕ :=
  Common.IO.Wide.bootstrapBudget + bodyCoefficient source + Common.IO.Output.outputBudget + 1

omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
theorem coefficient_pos (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ) :
    0 < coefficient source := by unfold coefficient; omega

omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
theorem budget_quadratic (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (inputLength sourceLength finalHeight : ℕ) :
    budget source inputLength sourceLength finalHeight ≤
      coefficient source * (inputLength + sourceLength + finalHeight + 1)^2 := by
  let U := inputLength + sourceLength + finalHeight + 1
  have first : (inputLength + 1)^2 ≤ U^2 := Nat.pow_le_pow_left (by dsimp only [U]; omega) 2
  have middle : (inputLength + sourceLength + 1)^2 ≤ U^2 :=
    Nat.pow_le_pow_left (by dsimp only [U]; omega) 2
  have last : (finalHeight + 1)^2 ≤ U^2 := Nat.pow_le_pow_left (by dsimp only [U]; omega) 2
  have body : bodyBudget source inputLength sourceLength ≤ bodyCoefficient source * U^2 :=
    (bodyBudget_quadratic source inputLength sourceLength).trans (Nat.mul_le_mul_left _ middle)
  calc
    budget source inputLength sourceLength finalHeight ≤
        Common.IO.Wide.bootstrapBudget * U^2 + bodyCoefficient source * U^2 +
          Common.IO.Output.outputBudget * U^2 :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ first) body) (Nat.mul_le_mul_left _ last)
    _ = (Common.IO.Wide.bootstrapBudget + bodyCoefficient source + Common.IO.Output.outputBudget) * U^2 := by ring
    _ ≤ coefficient source * (inputLength + sourceLength + finalHeight + 1)^2 :=
      Nat.mul_le_mul_right _ (by unfold coefficient; omega)

/-- ONE fixed finite machine and positive constant BEFORE ALL original
P/fee, source witnesses and final words. The conditional source path is
a proof obligation of the actual Phases implementation, not a new paper
qualification or any input to the Bool machine. Its nonempty finalstack0
will be the actual encoded artifact with its original TRUE footer. -/
theorem uniform_original_raw_backend
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
          trace.length ≤ C * ((encodeBits (rawInput P fee)).length + sourceTrace.length +
            Common.IO.Output.stackHeight sourceFinal.stk + 1)^2 ∧
          visitedBitSpace code (encodeBits (rawInput P fee)).length trace ≤
            (encodeBits (rawInput P fee)).length + 2 * (C *
              ((encodeBits (rawInput P fee)).length + sourceTrace.length +
                Common.IO.Output.stackHeight sourceFinal.stk + 1)^2) + 1 ∧
          (∀ count, visitedBitSpace code (encodeBits (rawInput P fee)).length (trace.take count) ≤
            (encodeBits (rawInput P fee)).length + 2 * (C *
              ((encodeBits (rawInput P fee)).length + sourceTrace.length +
                Common.IO.Output.stackHeight sourceFinal.stk + 1)^2) + 1) := by
  refine ⟨_, machine source, coefficient source, coefficient_pos source, ?_⟩
  intro P fee sourceTrace sourceFinal first chain last halt positive
  obtain ⟨trace, final, actual, naked, time, space⟩ :=
    original_raw_run source closed P fee sourceTrace sourceFinal first chain last halt positive
  have bound := budget_quadratic source (encodeBits (rawInput P fee)).length sourceTrace.length
    (Common.IO.Output.stackHeight sourceFinal.stk)
  have clock := time.trans bound
  refine ⟨trace, final, actual, naked, clock, ?_, ?_⟩
  · exact Common.visitedBitSpace_of_clock _ _ _ _ clock
  · intro count
    have old := space count
    omega

end PDROC.BitVM.VM.Backend
