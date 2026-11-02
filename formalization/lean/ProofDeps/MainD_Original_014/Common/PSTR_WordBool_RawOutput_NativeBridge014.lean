module

public import Common.PSTR_WordBool_RawOutput_Actual011

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype σ]

/-- Actual code-level consumer of040. Its first HALT performs the real
write-self transition into this one fixed decoder, preserving the tape. -/
noncomputable def nativeThenRaw (machine : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) : Machine ((TM2Native.nativeSupport machine support).card+states+1) :=
  seqMachine (TM2Native.nativeMachine machine support) code

/-- The original040 run and this decoder are concatenated in ONE actual
machine and ONE trace. The old native workspace contract remains available
from040; this theorem does not replace it with an elapsed-time space bound. -/
theorem native_then_raw_actual
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
      final.Tape.right₀=ListBlank.mk (finalSource.stk 0) ∧
      trace.length ≤ TM2Native.nativeBudget machine support*
        (2*((2*actionBound*(bound+pushBound+1)+1)*rest.length))+1+
          coefficient*(weight finalSource.stk)^2 := by
  obtain ⟨changed,front,frontFinal,represented,frontRun,frontTape,frontClock,frontCells⟩ :=
    TM2Native.actual_native_run machine support closed slot input finalSource rest chain last halt
      bound actionBound pushBound bounded counts
  obtain ⟨back,backFinal,backRun,backLabel,backHalt,backOutput,backClock,backCells⟩ :=
    compiled_endpoint finalSource changed represented
  have retained : RunsFrom code ⟨0,frontFinal.Tape⟩ back backFinal := by
    rw [frontTape]
    exact backRun
  let trace := front.map (leftCfg (b := states)) ++
    back.map (rightCfg (a := (TM2Native.nativeSupport machine support).card))
  let final := rightCfg (a := (TM2Native.nativeSupport machine support).card) backFinal
  have run := seq_runs (TM2Native.nativeMachine machine support) code
    (FiniteTrackCodec.encodedInput slot input) frontFinal backFinal front back frontRun retained
  refine ⟨trace,final,run,?_,backOutput,?_⟩
  · change rightLabel (a := (TM2Native.nativeSupport machine support).card) backFinal.q=_
    rw [backLabel]
  · simp only [trace,List.length_append,List.length_map]
    exact Nat.add_le_add frontClock backClock

end PaperProofs.Common.Native.PSTRWordBool.RawOutput
