module
public import Structure.B23_5_RawInit_Actual035
public import Structure.B23_5_RawInit_OriginalNative024

/-! Actual original raw-input adapter instantiated into native040 and the
raw decoder. No adapter execution/staging premise remains. Source code,
support and the original040 source-run/resource obligations are preserved;
a concrete B23/L01 ISA source remains the source owner's responsibility. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.NativeActual
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype σ]

noncomputable def machine (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) : Machine (Actual.states+NativeJoin.backStates source support+1) :=
  NativeJoin.machine Actual.machine source support

noncomputable def haltPort (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) : Fin ((Actual.states+NativeJoin.backStates source support+1)+1) :=
  NativeJoin.haltPort Actual.states source support

theorem actual (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports source support) (data : List Datum)
    (finalSource : TM2.Cfg (fun _ : Fin 16 => Bool) Λ σ)
    (rest : List (TM2.Cfg (fun _ : Fin 16 => Bool) Λ σ))
    (chain : (TM2.init (0 : Fin 16) (encode data)::rest).IsChain
      (fun before after => TM2.step source before=some after))
    (last : (TM2.init (0 : Fin 16) (encode data)::rest).getLast?=some finalSource)
    (halt : finalSource.l=none) (bound actionBound pushBound : Nat)
    (bounded : ∀ state∈TM2.init (0 : Fin 16) (encode data)::rest, ∀ point,
      (state.stk point).length≤bound)
    (counts : ∀ state∈TM2.init (0 : Fin 16) (encode data)::rest, ∀ label,
      state.l=some label → ScannerClock.actions (source label)≤actionBound ∧
        AuxWorkspace.pushes (source label)≤pushBound) :
    ∃ path final, Runs (machine source support) (encode data) path final ∧
      final.q=haltPort source support ∧ TM0.step (machine source support) final=none ∧
      final.Tape.right₀=ListBlank.mk (finalSource.stk 0) ∧
      path.length≤10033000*((encode data).length+1)^3+
        RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound ∧
      ∀ inputLen clock, visitedSpace (machine source support) inputLen (path.take clock)≤
        inputLen+2*(10033000*((encode data).length+1)^3+
          RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound)+1 := by
  have adapterActual : ∀ data : List Datum, ∃ path final,
      Runs Actual.machine (encode data) path final ∧
        final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
        path.length≤10033000*((encode data).length+1)^3 := by
    intro data
    obtain ⟨path,final,run,_port,_stopped,tape,time,_space⟩:=Actual.actual data
    exact ⟨path,final,run,tape,time⟩
  exact OriginalNative.actual Actual.machine source support 10033000 3 adapterActual closed data
    finalSource rest chain last halt bound actionBound pushBound bounded counts

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.NativeActual
