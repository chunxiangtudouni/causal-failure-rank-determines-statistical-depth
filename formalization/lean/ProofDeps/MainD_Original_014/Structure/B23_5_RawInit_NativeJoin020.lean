module
public import Structure.B23_5_RawInit_StagedFin16_012
public import Common.PSTR_WordBool_RawOutputSpace_Core001

/-! Literal finite-code consumer of native040 plus the actual raw decoder.
The front's whole-Tape equality is the only handoff. Source execution,
resources and fixed support remain exactly those of frozen040/014.
The staged instance is actual; an original-input instance still needs
the outstanding physical archive-to-staging producer. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.NativeJoin
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype σ]

noncomputable abbrev backStates (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) : Nat := (TM2Native.nativeSupport source support).card+RawOutput.states+1

noncomputable def machine {a : Nat} (adapter : Machine a)
    (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ) (support : Finset Λ) :
    Machine (a+backStates source support+1) :=
  seqMachine (a:=a) (b:=backStates source support) adapter (RawOutput.nativeThenRaw source support)

noncomputable def haltPort (a : Nat)
    (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ) (support : Finset Λ) :
    Fin ((a+backStates source support+1)+1) :=
  rightLabel (a:=a) (b:=backStates source support)
    (rightLabel (a:=(TM2Native.nativeSupport source support).card) (b:=RawOutput.states) RawOutput.haltPort)

theorem transport_port {a b : Nat} (cfg : MachineState b) (port : Fin (b+1))
    (same : cfg.q=port) : (rightCfg (a:=a) cfg).q=rightLabel (a:=a) port :=
  congrArg (rightLabel (a:=a)) same

theorem transport_output {a b : Nat} (cfg : MachineState b) (output : List Bool)
    (same : cfg.Tape.right₀=ListBlank.mk output) :
    (rightCfg (a:=a) cfg).Tape.right₀=ListBlank.mk output := same

theorem from_adapter {a : Nat} (adapter : Machine a) (initialTape : Tape Bool)
    (data : List Datum) (front : List (MachineState a)) (mid : MachineState a)
    (frontRun : RunsFrom adapter ⟨0,initialTape⟩ front mid)
    (frontTape : mid.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)))
    (frontClock : Nat) (frontTime : front.length≤frontClock)
    (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports source support)
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
    ∃ path final, RunsFrom (machine adapter source support) ⟨0,initialTape⟩ path final ∧
      final.q=haltPort a source support ∧ TM0.step (machine adapter source support) final=none ∧
      final.Tape.right₀=ListBlank.mk (finalSource.stk 0) ∧
      path.length≤frontClock+RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound ∧
      ∀ inputLen clock, visitedSpace (machine adapter source support) inputLen (path.take clock)≤
        inputLen+2*(frontClock+RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound)+1 := by
  obtain ⟨back,backFinal,backRun,backPort,_backHalt,backOutput,backTime,_backSpace⟩:=
    RawOutputSpace.native_then_raw_with_prefix_space source support closed (0 : Fin 16)
      (encode data) finalSource rest chain last halt bound actionBound pushBound bounded counts
  have backFrom : RunsFrom (RawOutput.nativeThenRaw source support) ⟨0,mid.Tape⟩ back backFinal := by
    rw [frontTape]
    exact ⟨backRun.1,backRun.2.1,backRun.2.2.1,backRun.2.2.2.1⟩
  let path:=front.map (leftCfg (b:=backStates source support))++back.map (rightCfg (a:=a))
  let final:=rightCfg (a:=a) backFinal
  have run : RunsFrom (machine adapter source support) ⟨0,initialTape⟩ path final :=
    seq_runsFrom adapter (RawOutput.nativeThenRaw source support) ⟨0,initialTape⟩ mid backFinal
      front back frontRun backFrom
  have time : path.length≤frontClock+RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound := by
    simp only [path,List.length_append,List.length_map]
    exact Nat.add_le_add frontTime backTime
  refine ⟨path,final,run,?_,run.2.2.2,?_,time,?_⟩
  · exact transport_port backFinal _ backPort
  · exact transport_output backFinal _ backOutput
  · intro inputLen clock
    have cells:=PSTRTMTrace002.visitedSpace_le (machine adapter source support) inputLen (path.take clock)
    have short:=(List.length_take_le' clock path).trans time
    omega

theorem staged_actual (data : List Datum) (gap : Nat)
    (source : Λ → TM2.Stmt (fun _ : Fin 16 => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports source support)
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
    ∃ path final, RunsFrom (machine StagedFin16.machine source support)
      ⟨0,StagedFin16.stagedTape data gap⟩ path final ∧
      final.q=haltPort 432 source support ∧
      TM0.step (machine StagedFin16.machine source support) final=none ∧
      final.Tape.right₀=ListBlank.mk (finalSource.stk 0) ∧
      path.length≤220*((encode data).length+gap+1)^2+
        RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound ∧
      ∀ inputLen clock, visitedSpace (machine StagedFin16.machine source support) inputLen (path.take clock)≤
        inputLen+2*(220*((encode data).length+gap+1)^2+
          RawOutputSpace.totalTime source support finalSource rest bound actionBound pushBound)+1 := by
  obtain ⟨front,mid,run,_port,tape,time,_space⟩:=StagedFin16.actual data gap
  exact from_adapter StagedFin16.machine (StagedFin16.stagedTape data gap) data front mid run tape
    (220*((encode data).length+gap+1)^2) time source support closed finalSource rest chain last halt
      bound actionBound pushBound bounded counts

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.NativeJoin
