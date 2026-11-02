module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsCalls_084

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.NatPacketMove

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

theorem at_actual {C : Type*} (roles : RatInput.Stack ≃ RatInput.Stack) (copy : Bool)
    (background : RatInput.Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (source target : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (RootB234.RatPacketTransport.atState roles background 2 context memory
        (NatField.packet number source) [] target) ∧
      trace.IsChain (fun a b => TM2.step (RootB234.RatPacketTransport.atProgram roles copy) a=some b) ∧
      trace.getLast?=some (RootB234.RatPacketTransport.atState roles background 4 context (false,false)
        (if copy then NatField.packet number source else source) [] (NatField.packet number target)) ∧
      trace.length≤3*(PSTRTMNatValue017.rawPayload number).length+6 := by
  let old := StackIso.slots roles.symm background
  obtain ⟨trace,first,chain,last,time⟩ := actual copy .halt old context memory number source target
  refine ⟨trace.map (StackIso.configuration roles),?_,?_,?_,?_⟩
  · rw [List.head?_map,first,Option.map_some,←RootB234.RatPacketTransport.atState_eq]
  · exact StackIso.chain_configuration_on roles _ _ trace chain (by intros; rfl)
  · rw [List.getLast?_map,last,Option.map_some,←RootB234.RatPacketTransport.atState_eq]
  · simpa only [List.length_map] using time

end B23_4_RatWordPrep.NatPacketMove

namespace B23_4_RatWordPrep.WordFields

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem target_move_shared (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (.targetMove 0)) (source : before.stk 15=RatInput.Encoder.packet x tail)
    (scratch : before.stk 4=[]) :
    targetMoveCfg (RootB234.RatPacketTransport.atState targetRoles before.stk 0
      ((packetIso C).symm before.var).1 ((packetIso C).symm before.var).2
      (RatInput.Encoder.packet x tail) [] (before.stk 9))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.targetMove 0) at active
    subst point
    change (⟨some (.targetMove 0),packetIso C ((packetIso C).symm memory),
      RootB234.RatPacketTransport.Public.physicalBank 15 9 slots _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RatPacketTransport.Public.physicalBank]

theorem actual_target_move (caller : Statement C) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (.targetMove 0)) (source : before.stk 15=RatInput.Encoder.packet x tail)
    (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.count .boot) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 15=tail ∧ final.stk 9=RatInput.Encoder.packet x (before.stk 9) ∧ final.stk 4=[] ∧
      (∀ slot,slot≠9→slot≠4→slot≠15→final.stk slot=before.stk slot) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  let registers := (packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RatPacketTransport.at_actual targetRoles false
    before.stk registers.1 registers.2 x tail (before.stk 9)
  let final := RootB234.RatPacketTransport.atState targetRoles before.stk 4 registers.1
    (false,false) tail [] (RatInput.Encoder.packet x (before.stk 9))
  have path := single_port_path (packetIso C) targetMoveLabel _ caller 4 rfl trace _ final
    facts.first facts.chain facts.last rfl
    (by intro point different; simp only [targetMoveLabel,different,ite_false,program])
  let run : Segment caller before (targetMoveCfg final) :=
    ⟨trace.map targetMoveCfg,path.1.trans (congrArg some (target_move_shared before x tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨targetMoveCfg final,run,rfl,?_,rfl,rfl,rfl,?_,?_⟩
  · change registers.1.2.2=before.var.2.2
    rfl
  · intro slot n9 n4 n15
    change RootB234.RatPacketTransport.Public.physicalBank 15 9 before.stk _ _ _ slot=before.stk slot
    simp only [RootB234.RatPacketTransport.Public.physicalBank,n9,n4,n15,ite_false]
  · simpa only [run,List.length_map] using facts.count

def naturalMoveLabel (symbolMode : Bool) (point : RootB234.RatPacketTransport.Label) : Label :=
  if symbolMode then symbolMoveLabel point else countMoveLabel point

def naturalMoveCfg (symbolMode : Bool) (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration (naturalMoveLabel symbolMode) (StoreIso.configuration (packetIso C) before)

theorem natural_move_shared (symbolMode : Bool) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (if symbolMode then .symbolMove 2 else .countMove 2))
    (source : before.stk 15=NatField.packet number tail) (scratch : before.stk 4=[]) :
    naturalMoveCfg symbolMode (RootB234.RatPacketTransport.atState naturalRoles before.stk 2
      ((packetIso C).symm before.var).1 ((packetIso C).symm before.var).2
      (NatField.packet number tail) [] (before.stk 3))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (if symbolMode then .symbolMove 2 else .countMove 2) at active
    subst point
    change (⟨some (naturalMoveLabel symbolMode 2),packetIso C ((packetIso C).symm memory),
      RootB234.RatPacketTransport.Public.physicalBank 15 3 slots _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    have bank : RootB234.RatPacketTransport.Public.physicalBank 15 3 slots
        (NatField.packet number tail) [] (slots 3)=slots := by
      funext slot
      fin_cases slot <;> simp_all [RootB234.RatPacketTransport.Public.physicalBank]
    rw [bank]
    cases symbolMode <;> rfl

theorem actual_natural_move (symbolMode : Bool) (caller : Statement C) (before : State C)
    (number : Nat) (tail : List Bool)
    (active : before.l=some (if symbolMode then .symbolMove 2 else .countMove 2))
    (source : before.stk 15=NatField.packet number tail) (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (if symbolMode then .round 0 else .build 0) ∧
      final.var.2.2=before.var.2.2 ∧ final.stk 15=tail ∧
      final.stk 3=NatField.packet number (before.stk 3) ∧ final.stk 4=[] ∧
      (∀ slot,slot≠3→slot≠4→slot≠15→final.stk slot=before.stk slot) ∧
      run.trace.length≤3*(PSTRTMNatValue017.rawPayload number).length+6 := by
  let registers := (packetIso C).symm before.var
  obtain ⟨trace,first,chain,last,time⟩ := NatPacketMove.at_actual naturalRoles false
    before.stk registers.1 registers.2 number tail (before.stk 3)
  let final := RootB234.RatPacketTransport.atState naturalRoles before.stk 4 registers.1
    (false,false) tail [] (NatField.packet number (before.stk 3))
  have path := single_port_path (packetIso C) (naturalMoveLabel symbolMode) _ caller 4 rfl
    trace _ final first chain last rfl (by
      intro point different
      cases symbolMode <;> simp [naturalMoveLabel,countMoveLabel,symbolMoveLabel,different,program] <;> rfl)
  let run : Segment caller before (naturalMoveCfg symbolMode final) :=
    ⟨trace.map (naturalMoveCfg symbolMode),path.1.trans
      (congrArg some (natural_move_shared symbolMode before number tail active source scratch)),path.2.1,path.2.2⟩
  refine ⟨naturalMoveCfg symbolMode final,run,?_,?_,rfl,rfl,rfl,?_,?_⟩
  · cases symbolMode <;> rfl
  · change registers.1.2.2=before.var.2.2
    rfl
  · intro slot n3 n4 n15
    change RootB234.RatPacketTransport.Public.physicalBank 15 3 before.stk _ _ _ slot=before.stk slot
    simp only [RootB234.RatPacketTransport.Public.physicalBank,n3,n4,n15,ite_false]
  · simpa only [run,List.length_map] using time

end B23_4_RatWordPrep.WordFields
