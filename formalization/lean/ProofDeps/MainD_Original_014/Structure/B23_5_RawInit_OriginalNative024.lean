module
public import Structure.B23_5_RawInit_NativeJoin020

/-! Typed consumer for the eventual original-input RawInit theorem.
Both finite code tables and constants are chosen before every data list.
The adapter premise is explicitly still owed; this theorem supplies no
host-generated staging tape and is not final ISA acceptance. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.OriginalNative
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype σ]

theorem actual {a : Nat} (adapter : Machine a)
    (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ) (support : Finset Λ)
    (c d : Nat)
    (adapterActual : ∀ data : List Datum, ∃ path final,
      Runs adapter (encode data) path final ∧
        final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)) ∧
        path.length≤c*((encode data).length+1)^d)
    (closed : TM2.Supports source support) (data : List Datum)
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
    ∃ path final, Runs (NativeJoin.machine adapter source support) (encode data) path final ∧
      final.q=NativeJoin.haltPort a source support ∧
      TM0.step (NativeJoin.machine adapter source support) final=none ∧
      final.Tape.right₀=ListBlank.mk (finalSource.stk 0) ∧
      path.length≤c*((encode data).length+1)^d+
        RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound ∧
      ∀ inputLen clock, visitedSpace (NativeJoin.machine adapter source support) inputLen (path.take clock)≤
        inputLen+2*(c*((encode data).length+1)^d+
          RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound)+1 := by
  obtain ⟨front,mid,frontRun,frontTape,frontTime⟩:=adapterActual data
  have frontFrom : RunsFrom adapter ⟨0,Tape.mk₁ (encode data)⟩ front mid :=
    ⟨frontRun.1,frontRun.2.1,frontRun.2.2.1,frontRun.2.2.2.1⟩
  obtain ⟨path,final,run,port,stopped,output,time,space⟩:=
    NativeJoin.from_adapter adapter (Tape.mk₁ (encode data)) data front mid frontFrom frontTape
      (c*((encode data).length+1)^d) frontTime source support closed finalSource rest chain last halt
        bound actionBound pushBound bounded counts
  exact ⟨path,final,PSTRTMTrace002.runs_of_chain (NativeJoin.machine adapter source support)
    (encode data) path final run.1 run.2.1 run.2.2.1 run.2.2.2,
    port,stopped,output,time,space⟩

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.OriginalNative
