module

public import RootB234_PrepEntry_NatPacketResources_080
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NatPacket

open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

structure Facts (code : Label → Statement C) (copy : Bool) (background : RatInput.Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (number : Nat) (source target : List Bool)
    (trace : List (State C)) : Prop where
  first : trace.head?=some (entry background context memory number source target)
  chain : trace.IsChain (fun a b => TM2.step code a=some b)
  last : trace.getLast?=some (finalState copy background context number source target)
  time : trace.length≤coefficient*scale background context memory number source target
  boundaries : ∀ current∈trace,current.var.1=context ∧
    (∀ slot,(current.stk slot).length≤coefficient*scale background context memory number source target) ∧
    RatInput.occupied current.stk≤coefficient*scale background context memory number source target ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (code point) current.var current.stk,
        node.1.1=context ∧
        (∀ slot,(node.2 slot).length≤coefficient*scale background context memory number source target) ∧
        RatInput.occupied node.2≤coefficient*scale background context memory number source target ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (code point) current.var current.stk≤
        coefficient*scale background context memory number source target

theorem actual_polynomial (copy : Bool) (background : RatInput.Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (number : Nat) (source target : List Bool) :
    ∃ trace,Facts (program copy .halt) copy background context memory number source target trace := by
  obtain ⟨run,_⟩:=actual copy (.halt : Statement C) background context memory number source target
  let before:=entry background context memory number source target
  let occupied:=mass background context memory number source target
  have initialBound : ∀ slot,(before.stk slot).length≤occupied := RatInput.Encoder.point_mass before.stk
  have initialFrame : ∀ slot,¬Work slot→before.stk slot=background slot := by
    intro slot safe
    simp only [Work,not_or] at safe
    change RootB234.RatPacketTransport.bank background _ _ _ slot=background slot
    simp only [RootB234.RatPacketTransport.bank,safe.1,safe.2.1,safe.2.2,ite_false]
  have timeBound:=run.count.trans (time_le background context memory number source target)
  have bounds:=trace_resources run.trace before background occupied run.first run.chain initialBound initialFrame
  have contexts:=trace_context run.trace before run.first run.chain
  have bounded : ∀ current∈run.trace,∀ slot,(current.stk slot).length≤occupied+2*(4*(occupied+1)) := by
    intro current member slot
    exact ((bounds current member).1 slot).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 timeBound) occupied)
  have caps:=resource_envelope occupied
  have proper:=NativeMulLink.no_early_halt_port (program copy (C := C) .halt) .done rfl
    run.trace (finalState copy background context number source target) run.chain run.last rfl
  refine ⟨run.trace,⟨run.first,run.chain,run.last,timeBound.trans caps.1,?_,?_⟩⟩
  · intro current member
    refine ⟨contexts current member,?_,?_,(bounds current member).2⟩
    · intro slot
      exact (bounded current member slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
    · exact (RatInput.Encoder.occupied_bound current.stk _ (bounded current member)).trans caps.2.1
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have internal:=internal_resources (copy := copy) current point _ (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,internal.2.trans caps.2.2.2⟩
    intro node inside
    obtain ⟨held,lengths,frames⟩:=internal.1 node inside
    refine ⟨held.trans (contexts current (List.mem_of_mem_dropLast member)),?_,?_,?_⟩
    · intro slot
      exact (lengths slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.2.1)
    · exact (RatInput.Encoder.occupied_bound node.2 _ lengths).trans caps.2.2.1
    · intro slot safe
      exact (frames slot safe).trans ((bounds current (List.mem_of_mem_dropLast member)).2 slot safe)

theorem final_stacks (copy : Bool) (background : RatInput.Stack → List Bool) (context : C)
    (number : Nat) (source target : List Bool) :
    let final:=finalState copy background context number source target
    final.l=some .done ∧ final.var=(context,(false,false)) ∧
    final.stk 15=(if copy then NatField.packet number source else source) ∧
    final.stk 2=NatField.packet number target ∧ final.stk 4=[] ∧
    ∀ slot,¬Work slot→final.stk slot=background slot := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro slot safe
  simp only [Work,not_or] at safe
  change RootB234.RatPacketTransport.bank background _ _ _ slot=background slot
  simp only [RootB234.RatPacketTransport.bank,safe.1,safe.2.1,safe.2.2,ite_false]

theorem entry_current (before : State C) (number : Nat) (source : List Bool)
    (active : before.l=some .field) (packet : before.stk 15=NatField.packet number source) (scratch : before.stk 4=[]) :
    entry before.stk before.var.1 before.var.2 number source (before.stk 2)=before := by
  cases before with
  | mk point memory bank =>
    change point=some .field at active
    subst point
    change (⟨some .field,memory,RootB234.RatPacketTransport.bank bank _ _ _⟩ : State C)=_
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RatPacketTransport.bank]


theorem program_eq_before_done (copy : Bool) (caller : Statement C) (point : Label) (different : point≠.done) :
    program copy caller point=program copy .halt point := by
  cases point with
  | field | reverse => rfl
  | done => exact False.elim (different rfl)

private theorem chain_same (old target : Label → Statement C) (trace : List (State C))
    (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (same : ∀ before∈trace.dropLast,∀ point,before.l=some point→target point=old point) :
    trace.IsChain (fun a b => TM2.step target a=some b) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      apply List.isChain_cons_cons.mpr
      refine ⟨?_,ih tailChain ?_⟩
      · cases first with
        | mk position memory slots =>
          cases position with
          | none => cases edge
          | some point =>
            have equality:=same ⟨some point,memory,slots⟩
              (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) point rfl
            change some (TM2.stepAux (target point) memory slots)=some next
            rw [equality]
            exact edge
      · intro current present point active
        apply same current _ point active
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present


theorem retarget (copy : Bool) (caller : Statement C) {background : RatInput.Stack → List Bool}
    {context : C} {memory : RatOutput.Store} {number : Nat} {source target : List Bool} {trace : List (State C)}
    (facts : Facts (program copy .halt) copy background context memory number source target trace) :
    Facts (program copy caller) copy background context memory number source target trace := by
  have same : ∀ current∈trace.dropLast,∀ point,current.l=some point→program copy caller point=program copy .halt point := by
    intro current member point selected
    apply program_eq_before_done copy caller point
    intro equal
    subst point
    exact (facts.proper current member).1 selected
  refine ⟨facts.first,chain_same _ _ _ facts.chain same,facts.last,facts.time,facts.boundaries,?_⟩
  intro current member
  refine ⟨(facts.proper current member).1,?_⟩
  intro point selected
  rw [same current member point selected]
  exact (facts.proper current member).2 point selected

noncomputable def statementClock (code : Label → Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (code point) current.var current.stk

noncomputable def traceClockSum (code : Label → Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock code)).sum

noncomputable def chargedCost (code : Label → Statement C) (trace : List (State C)) : Nat :=
  trace.length+traceClockSum code trace

variable {code : Label → Statement C} {copy : Bool} {background : RatInput.Stack → List Bool}
  {context : C} {memory : RatOutput.Store} {number : Nat} {source target : List Bool} {trace : List (State C)}

theorem traceClockSum_le (facts : Facts code copy background context memory number source target trace) :
    traceClockSum code trace≤coefficient^2*(scale background context memory number source target)^2 := by
  let cap:=coefficient*scale background context memory number source target
  have termwise : ∀ value∈trace.dropLast.map (statementClock code),value≤cap := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : traceClockSum code trace≤trace.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock code)) cap termwise
  have length : trace.dropLast.length≤cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum code trace≤cap*cap := sum.trans (Nat.mul_le_mul_right cap length)
    _=_ := by dsimp only [cap];ring

theorem chargedCost_le (facts : Facts code copy background context memory number source target trace) :
    chargedCost code trace≤(coefficient^2+coefficient)*(scale background context memory number source target)^2 := by
  have base : 1≤scale background context memory number source target := by unfold scale;omega
  have powers : scale background context memory number source target≤(scale background context memory number source target)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : 1≤2)
  have count:=facts.time.trans (Nat.mul_le_mul_left coefficient powers)
  calc
    chargedCost code trace≤coefficient*(scale background context memory number source target)^2+
      coefficient^2*(scale background context memory number source target)^2 := Nat.add_le_add count (traceClockSum_le facts)
    _=_ := by ring

abbrev finiteStore (C : Type*) [Fintype C] : Fintype (Store C) := inferInstance

namespace Public

theorem fixed_source (C : Type*) [Fintype C] (copy : Bool) :
    ∃ (code : Label → Statement C) (labels : Finset Label),
      TM2.Supports code labels ∧ code .done=.halt ∧
      ∀ (background : RatInput.Stack → List Bool) (context : C) (memory : RatOutput.Store)
        (number : Nat) (source target : List Bool),
        ∃ trace,Facts code copy background context memory number source target trace := by
  refine ⟨program copy .halt,Finset.univ,supports copy,rfl,?_⟩
  intro background context memory number source target
  exact actual_polynomial copy background context memory number source target

theorem static_caller (copy : Bool) (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (number : Nat) (source target : List Bool) :
    ∃ trace,Facts (program copy caller) copy background context memory number source target trace ∧
      chargedCost (program copy caller) trace≤(coefficient^2+coefficient)*(scale background context memory number source target)^2 := by
  obtain ⟨trace,old⟩:=actual_polynomial copy background context memory number source target
  have facts:=retarget copy caller old
  exact ⟨trace,facts,chargedCost_le facts⟩

/-- Internal current-state interface. The original preparation source
must genuinely establish its packet and empty temporary4; these are not
new original-caller assumptions. Arbitrary local flags are retained. -/
theorem actual_current (copy : Bool) (caller : Statement C) (before : State C) (number : Nat) (source : List Bool)
    (active : before.l=some .field) (packet : before.stk 15=NatField.packet number source) (scratch : before.stk 4=[]) :
    ∃ trace,Facts (program copy caller) copy before.stk before.var.1 before.var.2 number source (before.stk 2) trace ∧
      trace.head?=some before ∧
      chargedCost (program copy caller) trace≤(coefficient^2+coefficient)*
        (scale before.stk before.var.1 before.var.2 number source (before.stk 2))^2 := by
  obtain ⟨trace,facts,cost⟩:=static_caller copy caller before.stk before.var.1 before.var.2 number source (before.stk 2)
  exact ⟨trace,facts,facts.first.trans (congrArg some (entry_current before number source active packet scratch)),cost⟩

end Public

end RootB234.PrepEntry.NatPacket
