module

public import B23_4_RatWordPrep_SeqCmp_OddsInitPaths_112

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.OddsInit

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem packet_shared (rename : RootB234.RatPacketTransport.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 15)=RatInput.Encoder.packet x tail) (scratch : before.stk (roles 4)=[]) :
    packetCfg rename (RootB234.RatPacketTransport.atState roles before.stk 0
      ((packetIso C).symm before.var).1 ((packetIso C).symm before.var).2
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
    change (⟨some (rename 0),packetIso C ((packetIso C).symm memory),
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
      LabelMap.statement rename (StoreIso.statement (packetIso C)
        (RootB234.RatPacketTransport.atProgram roles copy point))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (rename 4) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank roles before.stk
        (if copy then RatInput.Encoder.packet x tail else tail) []
        (RatInput.Encoder.packet x (before.stk (roles 2))) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  let registers := (packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RatPacketTransport.at_actual roles copy
    before.stk registers.1 registers.2 x tail (before.stk (roles 2))
  let final := RootB234.RatPacketTransport.atState roles before.stk 4 registers.1 (false,false)
    (if copy then RatInput.Encoder.packet x tail else tail) [] (RatInput.Encoder.packet x (before.stk (roles 2)))
  have path := single_port_path (packetIso C) rename _ caller 4 rfl
    trace _ final facts.first facts.chain facts.last rfl same
  let run : Segment caller before (packetCfg rename final) :=
    ⟨trace.map (packetCfg rename),path.1.trans (congrArg some (packet_shared rename roles before x tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨packetCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2.2=before.var.2.2.2
    rfl
  · simpa only [run,List.length_map] using facts.count

theorem erase_shared (before : State C) (active : before.l=some (.erase 0)) :
    eraseCfg (⟨some 0,(packetIso C).symm before.var,before.stk⟩ : RootB234.Cells.State (PacketContext C))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.erase 0) at active
    subst point
    change (⟨some (.erase 0),packetIso C ((packetIso C).symm memory),slots⟩ : State C)=_
    rw [Equiv.apply_symm_apply]

theorem actual_erase (caller : Statement C) (before : State C) (active : before.l=some (.erase 0)) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.parkComp 0) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=Function.update before.stk 13 [] ∧ run.trace.length=(before.stk 13).length+2 := by
  let registers := (packetIso C).symm before.var
  let old := StackIso.slots eraseRoles.symm before.stk
  let source := RootB234.Cells.Public.clear0 (C := PacketContext C)
  let renamed : RootB234.Cells.Label → RootB234.Cells.Statement (PacketContext C) :=
    fun point => StackIso.statement eraseRoles (source point)
  let trace := RootB234.Cells.trace .clear0 registers old
  have facts := RootB234.Cells.actual_bounded .clear0 registers old
  have first : (trace.map (StackIso.configuration eraseRoles)).head?=
      some (⟨some 0,registers,before.stk⟩ : RootB234.Cells.State (PacketContext C)) := by
    rw [List.head?_map,facts.first,Option.map_some]
    change some (⟨some 0,registers,StackIso.slots eraseRoles old⟩ : RootB234.Cells.State (PacketContext C))=_
    rw [RootB234.RatPacketTransport.slots_inverse]
  have chain : (trace.map (StackIso.configuration eraseRoles)).IsChain
      (fun a b => TM2.step renamed a=some b) :=
    StackIso.chain_configuration_on eraseRoles source renamed trace facts.chain (by intros; rfl)
  let smallFinal := StackIso.configuration eraseRoles (RootB234.Cells.result .clear0 registers.1 old)
  have last : (trace.map (StackIso.configuration eraseRoles)).getLast?=some smallFinal := by
    rw [List.getLast?_map,facts.last,Option.map_some]
  have path := single_port_path (packetIso C) eraseLabel renamed caller 6 rfl _ _ smallFinal first chain last rfl
    (by intro point different; simp only [eraseLabel,different,ite_false,program]; rfl)
  let run : Segment caller before (eraseCfg smallFinal) :=
    ⟨(trace.map (StackIso.configuration eraseRoles)).map eraseCfg,
      path.1.trans (congrArg some (erase_shared before active)),path.2.1,path.2.2⟩
  refine ⟨eraseCfg smallFinal,run,rfl,?_,?_,?_⟩
  · change registers.1.2.2.2=before.var.2.2.2
    rfl
  · change StackIso.slots eraseRoles (Function.update old 0 [])=Function.update before.stk 13 []
    rw [StackIso.slots_update,RootB234.RatPacketTransport.slots_inverse]
    rfl
  · have count := facts.count
    change trace.length=(old 0).length+2 at count
    have originalCell : old 0=before.stk 13 := by rfl
    rw [originalCell] at count
    simpa only [run,List.length_map] using count

end B23_4_RatWordPrep.OddsInit

