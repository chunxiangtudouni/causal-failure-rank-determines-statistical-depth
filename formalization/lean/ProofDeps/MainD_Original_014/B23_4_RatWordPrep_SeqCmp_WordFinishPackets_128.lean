module

public import B23_4_RatWordPrep_SeqCmp_WordFinishPaths_127

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def packetCfg (rename : RootB234.RatPacketTransport.Label → Label)
    (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (OddsInit.packetIso C) before)

theorem packet_shared (rename : RootB234.RatPacketTransport.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 15)=RatInput.Encoder.packet x tail) (scratch : before.stk (roles 4)=[]) :
    packetCfg rename (RootB234.RatPacketTransport.atState roles before.stk 0
      ((OddsInit.packetIso C).symm before.var).1 ((OddsInit.packetIso C).symm before.var).2
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
    change (⟨some (rename 0),OddsInit.packetIso C ((OddsInit.packetIso C).symm memory),
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
      LabelMap.statement rename (StoreIso.statement (OddsInit.packetIso C)
        (RootB234.RatPacketTransport.atProgram roles copy point))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (rename 4) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank roles before.stk
        (if copy then RatInput.Encoder.packet x tail else tail) []
        (RatInput.Encoder.packet x (before.stk (roles 2))) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  let registers := (OddsInit.packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RatPacketTransport.at_actual roles copy
    before.stk registers.1 registers.2 x tail (before.stk (roles 2))
  let final := RootB234.RatPacketTransport.atState roles before.stk 4 registers.1 (false,false)
    (if copy then RatInput.Encoder.packet x tail else tail) [] (RatInput.Encoder.packet x (before.stk (roles 2)))
  have path := single_port_path (OddsInit.packetIso C) rename _ caller 4 rfl
    trace _ final facts.first facts.chain facts.last rfl same
  let run : Segment caller before (packetCfg rename final) :=
    ⟨trace.map (packetCfg rename),path.1.trans (congrArg some (packet_shared rename roles before x tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨packetCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2.2=before.var.2.2.2
    rfl
  · simpa only [run,List.length_map] using facts.count

theorem natural_shared (rename : RootB234.RatPacketTransport.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (rename 2))
    (source : before.stk (roles 15)=NatField.packet number tail) (scratch : before.stk (roles 4)=[]) :
    packetCfg rename (RootB234.RatPacketTransport.atState roles before.stk 2
      ((OddsInit.packetIso C).symm before.var).1 ((OddsInit.packetIso C).symm before.var).2
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
    change (⟨some (rename 2),OddsInit.packetIso C ((OddsInit.packetIso C).symm memory),
      RootB234.RatPacketTransport.atBank roles slots _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    exact congrArg (fun cells => (⟨some (rename 2),memory,cells⟩ : State C)) bank

theorem actual_natural (caller : Statement C)
    (rename : RootB234.RatPacketTransport.Label → Label) (roles : RatInput.Stack ≃ RatInput.Stack)
    (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (rename 2))
    (source : before.stk (roles 15)=NatField.packet number tail) (scratch : before.stk (roles 4)=[])
    (same : ∀ point,point≠4→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (OddsInit.packetIso C)
        (RootB234.RatPacketTransport.atProgram roles false point))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (rename 4) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank roles before.stk tail []
        (NatField.packet number (before.stk (roles 2))) ∧
      run.trace.length≤3*(PSTRTMNatValue017.rawPayload number).length+6 := by
  let registers := (OddsInit.packetIso C).symm before.var
  obtain ⟨trace,first,chain,last,time⟩ := NatPacketMove.at_actual roles false
    before.stk registers.1 registers.2 number tail (before.stk (roles 2))
  let final := RootB234.RatPacketTransport.atState roles before.stk 4 registers.1 (false,false)
    tail [] (NatField.packet number (before.stk (roles 2)))
  have path := single_port_path (OddsInit.packetIso C) rename _ caller 4 rfl
    trace _ final first chain last rfl same
  let run : Segment caller before (packetCfg rename final) :=
    ⟨trace.map (packetCfg rename),path.1.trans
      (congrArg some (natural_shared rename roles before number tail active source scratch)),path.2.1,path.2.2⟩
  refine ⟨packetCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2.2=before.var.2.2.2
    rfl
  · simpa only [run,List.length_map] using time

def clearCfg (before : RootB234.Cells.State (PacketContext C)) : State C :=
  LabelMap.configuration clearLabel (StoreIso.configuration (OddsInit.packetIso C) before)

theorem clear_shared (before : State C) (active : before.l=some (.clear 0)) :
    clearCfg (⟨some 0,(OddsInit.packetIso C).symm before.var,before.stk⟩ : RootB234.Cells.State (PacketContext C))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.clear 0) at active
    subst point
    change (⟨some (.clear 0),OddsInit.packetIso C ((OddsInit.packetIso C).symm memory),slots⟩ : State C)=_
    rw [Equiv.apply_symm_apply]

theorem actual_clear (caller : Statement C) (before : State C) (active : before.l=some (.clear 0)) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet .targetForSub 0) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=Function.update before.stk 0 [] ∧ run.trace.length=(before.stk 0).length+2 := by
  let registers := (OddsInit.packetIso C).symm before.var
  let trace := RootB234.Cells.trace .clear0 registers before.stk
  have facts := RootB234.Cells.actual_bounded .clear0 registers before.stk
  let final := RootB234.Cells.result .clear0 registers.1 before.stk
  have path := single_port_path (OddsInit.packetIso C) clearLabel _ caller 6 rfl
    trace _ final facts.first facts.chain facts.last rfl
    (by intro point different; simp only [clearLabel,different,ite_false,program]; rfl)
  let run : Segment caller before (clearCfg final) :=
    ⟨trace.map clearCfg,path.1.trans (congrArg some (clear_shared before active)),path.2.1,path.2.2⟩
  refine ⟨clearCfg final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2.2=before.var.2.2.2
    rfl
  · have count := facts.count
    have atZero : RootB234.Cells.source .clear0=0 := by decide
    rw [atZero] at count
    simpa only [run,List.length_map] using count

end B23_4_RatWordPrep.WordFinish
