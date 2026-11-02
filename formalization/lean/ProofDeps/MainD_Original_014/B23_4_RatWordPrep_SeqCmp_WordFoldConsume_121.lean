module

public import B23_4_RatWordPrep_SeqCmp_WordFoldPaths_118

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def packetAtCfg (rename : RootB234.RatPacketTransport.Label → Label)
    (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (OddsInit.packetIso C) before)

theorem natural_shared (rename : RootB234.RatPacketTransport.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (rename 2))
    (source : before.stk (roles 15)=NatField.packet number tail) (scratch : before.stk (roles 4)=[]) :
    packetAtCfg rename (RootB234.RatPacketTransport.atState roles before.stk 2
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
  let run : Segment caller before (packetAtCfg rename final) :=
    ⟨trace.map (packetAtCfg rename),path.1.trans
      (congrArg some (natural_shared rename roles before number tail active source scratch)),path.2.1,path.2.2⟩
  refine ⟨packetAtCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2.2=before.var.2.2.2
    rfl
  · simpa only [run,List.length_map] using time

theorem clear_shared (before : State C) (active : before.l=some (.clearQuery 0)) :
    clearCfg (⟨some 0,(OddsInit.packetIso C).symm before.var,before.stk⟩ : RootB234.Cells.State (PacketContext C))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.clearQuery 0) at active
    subst point
    change (⟨some (.clearQuery 0),OddsInit.packetIso C ((OddsInit.packetIso C).symm memory),slots⟩ : State C)=_
    rw [Equiv.apply_symm_apply]

theorem actual_clear (caller : Statement C) (before : State C) (active : before.l=some (.clearQuery 0)) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.check) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=Function.update before.stk 3 [] ∧ run.trace.length=(before.stk 3).length+2 := by
  let registers := (OddsInit.packetIso C).symm before.var
  let old := StackIso.slots clearRoles.symm before.stk
  let source := RootB234.Cells.Public.clear0 (C := PacketContext C)
  let renamed : RootB234.Cells.Label → RootB234.Cells.Statement (PacketContext C) :=
    fun point => StackIso.statement clearRoles (source point)
  let trace := RootB234.Cells.trace .clear0 registers old
  have facts := RootB234.Cells.actual_bounded .clear0 registers old
  have first : (trace.map (StackIso.configuration clearRoles)).head?=
      some (⟨some 0,registers,before.stk⟩ : RootB234.Cells.State (PacketContext C)) := by
    rw [List.head?_map,facts.first,Option.map_some]
    change some (⟨some 0,registers,StackIso.slots clearRoles old⟩ : RootB234.Cells.State (PacketContext C))=_
    rw [RootB234.RatPacketTransport.slots_inverse]
  have chain : (trace.map (StackIso.configuration clearRoles)).IsChain
      (fun a b => TM2.step renamed a=some b) :=
    StackIso.chain_configuration_on clearRoles source renamed trace facts.chain (by intros; rfl)
  let smallFinal := StackIso.configuration clearRoles (RootB234.Cells.result .clear0 registers.1 old)
  have last : (trace.map (StackIso.configuration clearRoles)).getLast?=some smallFinal := by
    rw [List.getLast?_map,facts.last,Option.map_some]
  have path := single_port_path (OddsInit.packetIso C) clearLabel renamed caller 6 rfl _ _ smallFinal first chain last rfl
    (by intro point different; simp only [clearLabel,different,ite_false,program]; rfl)
  let run : Segment caller before (clearCfg smallFinal) :=
    ⟨(trace.map (StackIso.configuration clearRoles)).map clearCfg,
      path.1.trans (congrArg some (clear_shared before active)),path.2.1,path.2.2⟩
  refine ⟨clearCfg smallFinal,run,rfl,?_,?_,?_⟩
  · change registers.1.2.2.2=before.var.2.2.2
    rfl
  · change StackIso.slots clearRoles (Function.update old 0 [])=Function.update before.stk 3 []
    rw [StackIso.slots_update,RootB234.RatPacketTransport.slots_inverse]
    rfl
  · have count := facts.count
    change trace.length=(old 0).length+2 at count
    have originalCell : old 0=before.stk 3 := by rfl
    rw [originalCell] at count
    simpa only [run,List.length_map] using count

theorem Segment.append_length_le {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

def ConsumeFrame (slot : RatInput.Stack) : Prop := slot≠0 ∧ slot≠3 ∧ slot≠4

theorem actual_consume (caller : Statement C) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (.dropQuery 2)) (source : before.stk 0=NatField.packet number tail)
    (scratch : before.stk 4=[]) (empty3 : before.stk 3=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .check ∧ final.var.2.2.2=before.var.2.2.2 ∧ final.stk 0=tail ∧
      final.stk 3=[] ∧ final.stk 4=[] ∧
      (∀ slot,ConsumeFrame slot→final.stk slot=before.stk slot) ∧
      run.trace.length≤6*(PSTRTMNatValue017.rawPayload number).length+12 := by
  obtain ⟨middle,moveRun,port,context,contents,moveTime⟩ := actual_natural caller queryLabel queryRoles
    before number tail active source scratch (by intro point different; simp only [queryLabel,different,ite_false,program])
  have parked : middle.stk 3=NatField.packet number [] := by
    rw [contents]
    change NatField.packet number (before.stk 3)=_
    rw [empty3]
  have frameMove (slot : RatInput.Stack) (n0 : slot≠0) (n3 : slot≠3) (n4 : slot≠4) : middle.stk slot=before.stk slot := by
    rw [contents]
    change (if slot=0 then _ else if slot=4 then _ else if slot=3 then _ else before.stk slot)=_
    simp only [n0,n3,n4,ite_false]
  obtain ⟨final,clearRun,finalPort,clearContext,clearContents,clearTime⟩ := actual_clear caller middle port
  let whole := moveRun.append clearRun
  refine ⟨final,whole,finalPort,clearContext.trans context,?_,?_,?_,?_,?_⟩
  · rw [clearContents,contents]; rfl
  · rw [clearContents]; rfl
  · rw [clearContents,contents]; rfl
  · intro slot safe
    rw [clearContents,Function.update_of_ne safe.2.1]
    exact frameMove slot safe.1 safe.2.1 safe.2.2
  · have size : (NatField.packet number []).length=2*(PSTRTMNatValue017.rawPayload number).length+2 := by
      simp only [NatField.packet,List.length_append,List.length_cons,List.length_nil,PSTRSymbolicRatExport.flagged_length]
    have spent : clearRun.trace.length=2*(PSTRTMNatValue017.rawPayload number).length+4 := by
      rw [clearTime,parked,size]
    have joined := moveRun.append_length_le clearRun
    change (moveRun.append clearRun).trace.length≤_
    omega

end B23_4_RatWordPrep.WordFold

