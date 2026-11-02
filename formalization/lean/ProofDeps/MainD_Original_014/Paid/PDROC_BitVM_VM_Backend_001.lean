module

public import Paid.PDROC_BitVM_Common_TM2_004
public import Paid.PDROC_BitVM_Common_Alphabet_005
public import Paid.PDROC_BitVM_Common_IO_Wide_Codec_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Backend

open Turing PaperProofs.Paid.Computation
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

/-! SOURCE ONLY. These are thin instantiations of frozen Common004/005
at FIXED32 Bool stacks and Root030's fixed65-bit pointed alphabet.
The source label/store types and their defaults are fixed before inputs.
All lengths below are proof quantities, never fields read by the code. -/

abbrev Stack := Fin 32
abbrev SourceState (Λ σ : Type*) := TM2.Cfg (fun _ : Stack => Bool) Λ σ
abbrev Rows := Stack → Option Bool

variable {Λ σ : Type*} [Fintype Λ] [Inhabited Λ] [Fintype σ] [Inhabited σ]

noncomputable def bodyMachine (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ) :=
  Common.alphabetBitMachine (FiniteTrackCodec.encode (count := 32)) FiniteTrackCodec.decode
    (TM2to1.tr source) (TM2to1.trSupp source Finset.univ)

noncomputable def bodyBudget (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (inputLength sourceLength : ℕ) : ℕ :=
  Common.alphabetBitBudget (FiniteTrackCodec.encode (count := 32)) FiniteTrackCodec.decode
    (TM2to1.tr source) (TM2to1.trSupp source Finset.univ)
    (Common.sourceTM1Budget source Finset.univ inputLength sourceLength)

/-- Select the existing genuine compiler witness once. Its endpoint is
the WHOLE actual encoded tape from that same source trace, at the real
bottom head. The old32 stack words are retained by the representation. -/
theorem body_runs (source : Λ → TM2.Stmt (fun _ : Stack => Bool) Λ σ)
    (closed : TM2.Supports source (Finset.univ : Finset Λ))
    (input : List Bool) (sourceTrace : List (SourceState Λ σ)) (sourceFinal : SourceState Λ σ)
    (first : sourceTrace.head? = some (TM2.init (0 : Stack) input))
    (chain : sourceTrace.IsChain (fun before after => TM2.step source before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) (halt : TM2.step source sourceFinal = none) :
    ∃ trace final, ∃ changed : ListBlank Rows,
      BitRuns (bodyMachine source) (Common.IO.Wide.encodedInit32 input) trace final ∧
      (∀ slot, changed.map (proj slot) = ListBlank.mk ((sourceFinal.stk slot).map some).reverse) ∧
      final.Tape = TM1to1.trTape (FiniteTrackCodec.encode_default 32) (ScannerPaths.baseTape changed) ∧
      trace.length ≤ bodyBudget source input.length sourceTrace.length := by
  obtain ⟨trackTrace, trackFinal, trackFirst, trackChain, trackLast, trackHalt, trackRepresentation, trackTime⟩ :=
    Common.tm2_actual_track_trace source Finset.univ closed (0 : Stack) input
      sourceTrace sourceFinal first chain last halt
  obtain ⟨changed, represented, selected⟩ :=
    Common.tracks_of_representation sourceFinal trackFinal trackRepresentation
  have trackTape : trackFinal.Tape = ScannerPaths.baseTape changed := by
    simpa only [ScannerRun.compiledCfg] using congrArg TM1.Cfg.Tape selected.symm
  obtain ⟨trace, final, actual, tape, time, _space⟩ :=
    Common.alphabet_actual_bit_trace (FiniteTrackCodec.encode (count := 32)) FiniteTrackCodec.decode
      (FiniteTrackCodec.encode_default 32) FiniteTrackCodec.decode_encode
      (TM2to1.tr source) (TM2to1.trSupp source Finset.univ) (TM2to1.tr_supports source closed)
      (TM2to1.trInit (0 : Stack) input) trackTrace trackFinal trackFirst trackChain trackLast trackHalt
  have encoded : BitRuns (bodyMachine source) (Common.IO.Wide.encodedInit32 input) trace final := by
    simpa only [bodyMachine, Common.IO.Wide.encodedInit32, FiniteTrackCodec.encodedInput,
      Common.alphabetInput] using actual
  have enlarged : Common.alphabetBitBudget (FiniteTrackCodec.encode (count := 32)) FiniteTrackCodec.decode
      (TM2to1.tr source) (TM2to1.trSupp source Finset.univ) trackTrace.length ≤
      bodyBudget source input.length sourceTrace.length := by
    unfold Common.alphabetBitBudget bodyBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ trackTime) 1)) 1
  exact ⟨trace, final, changed, encoded, represented,
    tape.trans (congrArg (TM1to1.trTape (FiniteTrackCodec.encode_default 32)) trackTape), time.trans enlarged⟩

end PDROC.BitVM.VM.Backend
