module

public import B23_4_RatWordPrep_SeqCmp_WordPackPaths_103

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordPack

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem packet_shared (rename : RootB234.RatPacketTransport.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 15)=RatInput.Encoder.packet x tail) (scratch : before.stk (roles 4)=[]) :
    packetCfg rename (RootB234.RatPacketTransport.atState roles before.stk 0
      ((WordFields.packetIso C).symm before.var).1 ((WordFields.packetIso C).symm before.var).2
      (RatInput.Encoder.packet x tail) [] (before.stk (roles 2)))=before := by
  have bank : RootB234.RatPacketTransport.atBank roles before.stk
      (RatInput.Encoder.packet x tail) [] (before.stk (roles 2))=before.stk := by
    funext slot
    unfold RootB234.RatPacketTransport.atBank
    split_ifs with h15 h4 h2
    · subst slot; exact source.symm
    · subst slot; exact scratch.symm
    · subst slot; rfl
    · rfl
  cases before with
  | mk point memory slots =>
    change point=some (rename 0) at active
    subst point
    change (⟨some (rename 0),WordFields.packetIso C ((WordFields.packetIso C).symm memory),
      RootB234.RatPacketTransport.atBank roles slots _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    exact congrArg (fun cells => (⟨some (rename 0),memory,cells⟩ : State C)) bank

/-- The concrete caller selects roles/copy/return maps before input.
Only the actual current source packet is assumed; all paths and copied
data are produced by the existing physical transport theorem. -/
theorem actual_packet (caller : Statement C)
    (rename : RootB234.RatPacketTransport.Label → Label) (roles : RatInput.Stack ≃ RatInput.Stack)
    (copy : Bool) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 15)=RatInput.Encoder.packet x tail) (scratch : before.stk (roles 4)=[])
    (same : ∀ point,point≠4→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.packetIso C)
        (RootB234.RatPacketTransport.atProgram roles copy point))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (rename 4) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank roles before.stk
        (if copy then RatInput.Encoder.packet x tail else tail) []
        (RatInput.Encoder.packet x (before.stk (roles 2))) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  let registers := (WordFields.packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RatPacketTransport.at_actual roles copy
    before.stk registers.1 registers.2 x tail (before.stk (roles 2))
  let final := RootB234.RatPacketTransport.atState roles before.stk 4 registers.1 (false,false)
    (if copy then RatInput.Encoder.packet x tail else tail) [] (RatInput.Encoder.packet x (before.stk (roles 2)))
  have path := single_port_path (WordFields.packetIso C) rename _ caller 4 rfl
    trace _ final facts.first facts.chain facts.last rfl same
  let run : Segment caller before (packetCfg rename final) :=
    ⟨trace.map (packetCfg rename),path.1.trans (congrArg some (packet_shared rename roles before x tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨packetCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2=before.var.2.2
    rfl
  · simpa only [run,List.length_map] using facts.count

theorem natural_shared (rename : RootB234.RatPacketTransport.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (rename 2))
    (source : before.stk (roles 15)=NatField.packet number tail) (scratch : before.stk (roles 4)=[]) :
    packetCfg rename (RootB234.RatPacketTransport.atState roles before.stk 2
      ((WordFields.packetIso C).symm before.var).1 ((WordFields.packetIso C).symm before.var).2
      (NatField.packet number tail) [] (before.stk (roles 2)))=before := by
  have bank : RootB234.RatPacketTransport.atBank roles before.stk
      (NatField.packet number tail) [] (before.stk (roles 2))=before.stk := by
    funext slot
    unfold RootB234.RatPacketTransport.atBank
    split_ifs with h15 h4 h2
    · subst slot; exact source.symm
    · subst slot; exact scratch.symm
    · subst slot; rfl
    · rfl
  cases before with
  | mk point memory slots =>
    change point=some (rename 2) at active
    subst point
    change (⟨some (rename 2),WordFields.packetIso C ((WordFields.packetIso C).symm memory),
      RootB234.RatPacketTransport.atBank roles slots _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    exact congrArg (fun cells => (⟨some (rename 2),memory,cells⟩ : State C)) bank

theorem actual_natural (caller : Statement C)
    (rename : RootB234.RatPacketTransport.Label → Label) (roles : RatInput.Stack ≃ RatInput.Stack)
    (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (rename 2))
    (source : before.stk (roles 15)=NatField.packet number tail) (scratch : before.stk (roles 4)=[])
    (same : ∀ point,point≠4→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.packetIso C)
        (RootB234.RatPacketTransport.atProgram roles false point))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (rename 4) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank roles before.stk tail []
        (NatField.packet number (before.stk (roles 2))) ∧
      run.trace.length≤3*(PSTRTMNatValue017.rawPayload number).length+6 := by
  let registers := (WordFields.packetIso C).symm before.var
  obtain ⟨trace,first,chain,last,time⟩ := NatPacketMove.at_actual roles false
    before.stk registers.1 registers.2 number tail (before.stk (roles 2))
  let final := RootB234.RatPacketTransport.atState roles before.stk 4 registers.1 (false,false)
    tail [] (NatField.packet number (before.stk (roles 2)))
  have path := single_port_path (WordFields.packetIso C) rename _ caller 4 rfl
    trace _ final first chain last rfl same
  let run : Segment caller before (packetCfg rename final) :=
    ⟨trace.map (packetCfg rename),path.1.trans
      (congrArg some (natural_shared rename roles before number tail active source scratch)),path.2.1,path.2.2⟩
  refine ⟨packetCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2=before.var.2.2
    rfl
  · simpa only [run,List.length_map] using time

theorem cells_shared (op : RootB234.Cells.Operation) (rename : RootB234.Cells.Label → Label)
    (before : State C) (active : before.l=some (rename (RootB234.Cells.entry op))) :
    cellsCfg rename (RootB234.Cells.initial op ((WordFields.packetIso C).symm before.var) before.stk)=before := by
  cases before with
  | mk point memory slots =>
    change point=some (rename (RootB234.Cells.entry op)) at active
    subst point
    change (⟨some (rename (RootB234.Cells.entry op)),WordFields.packetIso C ((WordFields.packetIso C).symm memory),slots⟩ : State C)=_
    rw [Equiv.apply_symm_apply]

theorem actual_cells (caller : Statement C) (op : RootB234.Cells.Operation)
    (rename : RootB234.Cells.Label → Label) (before : State C)
    (active : before.l=some (rename (RootB234.Cells.entry op)))
    (same : ∀ point,point≠RootB234.Cells.returnPort op→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.packetIso C)
        (RootB234.Cells.program op .halt point))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (rename (RootB234.Cells.returnPort op)) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.Cells.output op before.stk ∧
      run.trace.length=(before.stk (RootB234.Cells.source op)).length+2 ∧
      ∀ current∈run.trace,current.var.2.2=before.var.2.2 ∧
        (∀ slot,(current.stk slot).length≤3*RootB234.Cells.scale before.stk) ∧
        RatInput.occupied current.stk≤48*RootB234.Cells.scale before.stk ∧
        ∀ slot,¬RootB234.Cells.Work op slot→current.stk slot=before.stk slot := by
  let registers := (WordFields.packetIso C).symm before.var
  let trace := RootB234.Cells.trace op registers before.stk
  let final := RootB234.Cells.result op registers.1 before.stk
  have facts := RootB234.Cells.actual_bounded op registers before.stk
  have atPort : RootB234.Cells.program (C := PacketContext C) op .halt (RootB234.Cells.returnPort op)=.halt := by
    cases op <;> rfl
  have path := single_port_path (WordFields.packetIso C) rename _ caller (RootB234.Cells.returnPort op) atPort
    trace _ final facts.first facts.chain facts.last rfl same
  let run : Segment caller before (cellsCfg rename final) :=
    ⟨trace.map (cellsCfg rename),path.1.trans (congrArg some (cells_shared op rename before active)),path.2.1,path.2.2⟩
  refine ⟨cellsCfg rename final,run,rfl,?_,rfl,?_,?_⟩
  · change registers.1.2.2=before.var.2.2
    rfl
  · simpa only [run,List.length_map] using facts.count
  · intro current member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    have bound := facts.boundaries original present
    refine ⟨?_,bound.2.1,bound.2.2.1,bound.2.2.2⟩
    exact congrArg (fun v : PacketContext C => v.2.2) bound.1

end B23_4_RatWordPrep.WordPack


