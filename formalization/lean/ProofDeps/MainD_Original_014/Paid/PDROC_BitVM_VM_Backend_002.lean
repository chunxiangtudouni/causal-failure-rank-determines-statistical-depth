module

public import Paid.PDROC_BitVM_VM_Backend_001
public import Paid.PDROC_BitVM_Common_IO_Wide_Bool_018
public import Paid.PDROC_BitVM_Common_IO_Output_Whole_018
public import Paid.PDROC_BitVM_VM_BoolCompose_Resources_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Backend

open Turing PaperProofs.Paid.Computation
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

variable {Λ σ : Type*} [Fintype Λ] [Inhabited Λ] [Fintype σ] [Inhabited σ]

/-- All three finite Bool tables are selected from FIXED source syntax
before P/fee or any source trace is given. Seq performs real transitions
between phases on exactly the same entire Tape and physical head. -/
noncomputable def machine (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ) :=
  BoolCompose.machine (BoolCompose.machine Common.IO.Wide.bootstrapMachine (bodyMachine source))
    Common.IO.Output.outputMachine

noncomputable def budget (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (inputLength sourceLength finalHeight : ℕ) : ℕ :=
  Common.IO.Wide.bootstrapBudget * (inputLength + 1)^2 +
    bodyBudget source inputLength sourceLength + Common.IO.Output.outputBudget * (finalHeight + 1)^2

/-- The original raw6 input is physically bootstrapped, then compiled
source code executes, then the true final stack0 is physically extracted
past ALL old32-track data. SourceTrace is a proof witness discharged by
the parent's real Phases run; no trace/width/fuel becomes machine input. -/
theorem original_raw_run (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (closed : TM2.Supports source (Finset.univ : Finset Λ))
    (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (sourceTrace : List (SourceState Λ σ)) (sourceFinal : SourceState Λ σ)
    (first : sourceTrace.head? = some (TM2.init (0 : Stack) (encodeBits (rawInput P fee))))
    (chain : sourceTrace.IsChain (fun before after => TM2.step source before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) (halt : TM2.step source sourceFinal = none)
    (positive : 0 < (sourceFinal.stk (0 : Stack)).length) :
    ∃ trace final,
      BitRuns (machine source) (encodeBits (rawInput P fee)) trace final ∧
      final.Tape.right₀ = ListBlank.mk (sourceFinal.stk (0 : Stack)) ∧
      trace.length ≤ budget source (encodeBits (rawInput P fee)).length sourceTrace.length
        (Common.IO.Output.stackHeight sourceFinal.stk) ∧
      (∀ count, visitedBitSpace (machine source) (encodeBits (rawInput P fee)).length (trace.take count) ≤
        (encodeBits (rawInput P fee)).length +
          2 * budget source (encodeBits (rawInput P fee)).length sourceTrace.length
            (Common.IO.Output.stackHeight sourceFinal.stk) + 1) := by
  let input := encodeBits (rawInput P fee)
  obtain ⟨inputTrace, inputFinal, inputActual, inputTape, inputTime, _inputSpace⟩ :=
    Common.IO.Wide.original_raw_bit_run P fee
  obtain ⟨bodyTrace, bodyFinal, changed, bodyActual, represented, bodyTape, bodyTime⟩ :=
    body_runs source closed input sourceTrace sourceFinal first chain last halt
  have middle := BoolCompose.segment_on_actual_tape (bodyMachine source)
    (Common.IO.Wide.encodedInit32 input) inputFinal.Tape bodyTrace bodyFinal inputTape bodyActual
  have height : 0 < Common.IO.Output.stackHeight sourceFinal.stk :=
    positive.trans_le (Common.IO.Output.length_le_height sourceFinal.stk (0 : Stack))
  have finalWhole : bodyFinal.Tape = Tape.mk₁
      ((Common.IO.Output.canonicalTracks sourceFinal.stk).flatMap
        (fun row => (FiniteTrackCodec.encode row).toList)) :=
    bodyTape.trans (Common.IO.Output.actual_encoded_tape_canonical sourceFinal.stk height changed represented)
  obtain ⟨outputTrace, outputFinal, outputActual, outputRight, outputTime, _outputSpace⟩ :=
    Common.IO.Output.whole_output_bit_run sourceFinal.stk positive changed represented
  have right := BoolCompose.segment_on_actual_tape Common.IO.Output.outputMachine
    ((Common.IO.Output.canonicalTracks sourceFinal.stk).flatMap
      (fun row => (FiniteTrackCodec.encode row).toList))
    bodyFinal.Tape outputTrace outputFinal finalWhole outputActual
  obtain ⟨trace, final, actual, tape, time, space⟩ :=
    BoolCompose.actual_three_with_resources Common.IO.Wide.bootstrapMachine (bodyMachine source)
      Common.IO.Output.outputMachine input inputFinal bodyFinal outputFinal inputTrace bodyTrace outputTrace
      (Common.IO.Wide.bootstrapBudget * (input.length + 1)^2)
      (bodyBudget source input.length sourceTrace.length)
      (Common.IO.Output.outputBudget * (Common.IO.Output.stackHeight sourceFinal.stk + 1)^2)
      inputActual middle right inputTime bodyTime outputTime
  exact ⟨trace, final, actual, (congrArg Tape.right₀ tape).trans outputRight, time, space⟩

end PDROC.BitVM.VM.Backend
