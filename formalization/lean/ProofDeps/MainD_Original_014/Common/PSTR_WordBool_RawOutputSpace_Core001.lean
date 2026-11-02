module

public import Common.PSTR_WordBool_RawOutput_NativeBridge014

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutputSpace

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005
open PaperProofs.Common.Native.PSTRWordBool.RawOutput

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype σ]

/-- Exactly the complete native-plus-decoder clock already proved by014.
It may depend on the original source execution; it is not decoder weight. -/
noncomputable def totalTime
    (machine : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ) (support : Finset Λ)
    (finalSource : TM2.Cfg (fun _ : Fin 16 => Bool) Λ σ)
    (rest : List (TM2.Cfg (fun _ : Fin 16 => Bool) Λ σ))
    (bound actionBound pushBound : Nat) : Nat :=
  TM2Native.nativeBudget machine support*
    (2*((2*actionBound*(bound+pushBound+1)+1)*rest.length))+1+
      coefficient*(weight finalSource.stk)^2

/-- ONE call of014 supplies this exact trace. Its original whole clock
also bounds every prefix's visited space; no second execution is chosen. -/
theorem native_then_raw_with_prefix_space
    (machine : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports machine support)
    (slot : Fin 16) (input : List Bool)
    (finalSource : TM2.Cfg (fun _ : Fin 16 => Bool) Λ σ)
    (rest : List (TM2.Cfg (fun _ : Fin 16 => Bool) Λ σ))
    (chain : (TM2.init slot input :: rest).IsChain
      (fun before after => TM2.step machine before=some after))
    (last : (TM2.init slot input :: rest).getLast?=some finalSource)
    (halt : finalSource.l=none) (bound actionBound pushBound : Nat)
    (bounded : ∀ state ∈ TM2.init slot input :: rest, ∀ point, (state.stk point).length ≤ bound)
    (counts : ∀ state ∈ TM2.init slot input :: rest, ∀ label, state.l=some label →
      ScannerClock.actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound) :
    ∃ trace final, Runs (nativeThenRaw machine support)
      (FiniteTrackCodec.encodedInput slot input) trace final ∧
      final.q=rightLabel (a := (TM2Native.nativeSupport machine support).card) haltPort ∧
      TM0.step (nativeThenRaw machine support) final=none ∧
      final.Tape.right₀=ListBlank.mk (finalSource.stk 0) ∧
      trace.length ≤ totalTime machine support finalSource rest bound actionBound pushBound ∧
      ∀ inputLen clock, visitedSpace (nativeThenRaw machine support) inputLen (trace.take clock) ≤
        inputLen+2*totalTime machine support finalSource rest bound actionBound pushBound+1 := by
  obtain ⟨trace,final,run,label,output,time⟩ :=
    native_then_raw_actual machine support closed slot input finalSource rest chain last halt
      bound actionBound pushBound bounded counts
  have clockBound : trace.length ≤ totalTime machine support finalSource rest bound actionBound pushBound := time
  refine ⟨trace,final,run,label,run.2.2.2.1,output,clockBound,?_⟩
  intro inputLen clock
  have cells := PSTRTMTrace002.visitedSpace_le (nativeThenRaw machine support) inputLen (trace.take clock)
  have shortPrefix := (List.length_take_le' clock trace).trans clockBound
  nlinarith

end PaperProofs.Common.Native.PSTRWordBool.RawOutputSpace
