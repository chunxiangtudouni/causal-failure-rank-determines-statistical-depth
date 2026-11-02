module

public import RootB234_PrepEntry_StageFrontResources_053
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageFront

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*} {I : Instance}

def coefficient : Nat := 1048576
def scale (background : RatInput.Stack → List Bool) (length : Nat) : Nat :=
  RatInput.occupied background+length+1
def space (mass length : Nat) : Nat := mass+length+16*(256*(length+1)^2)

theorem resource_envelope (mass length : Nat) :
    256*(length+1)^2≤coefficient*(mass+length+1)^2 ∧
    16*space mass length≤coefficient*(mass+length+1)^2 ∧
    16*(space mass length+16)≤coefficient*(mass+length+1)^2 ∧
    32*(space mass length+17)≤coefficient*(mass+length+1)^2 := by
  have base : 1≤mass+length+1 := by omega
  have positive : 1≤(mass+length+1)^2 := Nat.pow_le_pow_left base 2
  have linear : mass+length+1≤(mass+length+1)^2 := by nlinarith only [base]
  have square := Nat.pow_le_pow_left (show length+1≤mass+length+1 by omega) 2
  dsimp only [space,coefficient]
  constructor
  · omega
  constructor
  · nlinarith only [square,linear]
  constructor <;> nlinarith only [square,linear,positive]

structure Facts (source : Label → Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry context background (preparationInput input contract budget))
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  active : final.l=some .done
  natural : final.stk 14=NatField.packet (FirstRaw.lastNatural input contract) (background 14)
  rational : final.stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) (background 13)
  fee : final.stk 12=feeOutput input (background 12)
  scratch : final.stk 7=background 7
  cursor : ListBlank.mk (final.stk 0)=ListBlank.mk (afterFee input contract budget++[true])
  stage_flag : final.var.2.2=decide (I.stageCount≠0)
  context_eq : callerContext final.var=context
  outside : ∀ slot,¬Work slot→final.stk slot=background slot
  time : trace.length≤coefficient*(scale background (preparationInput input contract budget).length)^2
  boundaries : ∀ current∈trace,callerContext current.var=context ∧
    (∀ slot,(current.stk slot).length≤coefficient*(scale background (preparationInput input contract budget).length)^2) ∧
    RatInput.occupied current.stk≤coefficient*(scale background (preparationInput input contract budget).length)^2 ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        callerContext node.1=context ∧
        (∀ slot,(node.2 slot).length≤coefficient*(scale background (preparationInput input contract budget).length)^2) ∧
        RatInput.occupied node.2≤coefficient*(scale background (preparationInput input contract budget).length)^2 ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤
        coefficient*(scale background (preparationInput input contract budget).length)^2

theorem actual_polynomial (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final,Facts (program .halt) context background input contract budget trace final := by
  obtain ⟨trace,final,first,chain,last,active,natural,rational,fee,scratch,cursor,contextEq,outside,count,stageFlag⟩:=
    actual context background input contract budget
  let bits:=preparationInput input contract budget
  let mass:=RatInput.occupied background
  let before:=entry context background bits
  have initialBound : ∀ slot,(before.stk slot).length≤mass+bits.length := by
    intro slot
    rw [show before.stk=fun point => if point=0 then bits else if point=1 then [] else background point from entry_slots _ _ _]
    change (if slot=0 then bits else if slot=1 then [] else background slot).length≤mass+bits.length
    split
    · omega
    · split
      · simp only [List.length_nil]; omega
      · have bound:=RatInput.Encoder.point_mass background slot
        omega
  have initialFrame : ∀ slot,¬Work slot→before.stk slot=background slot := by
    intro slot untouched
    have notZero : slot≠0 := by intro same; subst slot; exact untouched (by decide)
    have notOne : slot≠1 := by intro same; subst slot; exact untouched (by decide)
    rw [show before.stk=fun point => if point=0 then bits else if point=1 then [] else background point from entry_slots _ _ _]
    simp only [notZero,notOne,ite_false]
  have timeBound:=count.trans (time_le input contract budget)
  have bounds:=trace_resources trace before background (mass+bits.length) first chain initialBound initialFrame
  have contexts:=trace_context trace before first chain
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤space mass bits.length := by
    intro current present slot
    exact ((bounds current present).1 slot).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 16 timeBound) _)
  have caps:=resource_envelope mass bits.length
  have proper:=NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last active
  refine ⟨trace,final,⟨first,chain,last,active,natural,rational,fee,scratch,cursor,stageFlag,
    contextEq,outside,timeBound.trans caps.1,?_,?_⟩⟩
  · intro current present
    refine ⟨contexts current present,?_,?_,(bounds current present).2⟩
    · intro slot
      exact (bounded current present slot).trans
        ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
    · exact (RatInput.Encoder.occupied_bound current.stk _ (bounded current present)).trans caps.2.1
  · intro current present
    refine ⟨proper current present,?_⟩
    intro point selected
    have internal:=internal_resources current point _ (bounded current (List.mem_of_mem_dropLast present))
    refine ⟨?_,internal.2.trans caps.2.2.2⟩
    intro node inside
    obtain ⟨same,lengths,frames⟩:=internal.1 node inside
    refine ⟨same.trans (contexts current (List.mem_of_mem_dropLast present)),?_,?_,?_⟩
    · intro slot
      exact (lengths slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.2.1)
    · exact (RatInput.Encoder.occupied_bound node.2 _ lengths).trans caps.2.2.1
    · intro slot untouched
      exact (frames slot untouched).trans ((bounds current (List.mem_of_mem_dropLast present)).2 slot untouched)

theorem program_eq_before_done (caller : Statement C) (point : Label) (proper : point≠.done) :
    program caller point=program .halt point := by cases point <;> first | rfl | exact False.elim (proper rfl)

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

theorem retarget (caller : Statement C) {context : C} {background : RatInput.Stack → List Bool}
    {input : StatisticalInput I} {contract : Contract I} {budget : Rat} {trace : List (State C)} {final : State C}
    (facts : Facts (program .halt) context background input contract budget trace final) :
    Facts (program caller) context background input contract budget trace final := by
  have same : ∀ current∈trace.dropLast,∀ point,current.l=some point→program caller point=program .halt point := by
    intro current present point selected
    apply program_eq_before_done caller point
    intro equal
    subst point
    exact (facts.proper current present).1 selected
  refine ⟨facts.first,chain_same _ _ _ facts.chain same,facts.last,facts.active,facts.natural,facts.rational,
    facts.fee,facts.scratch,facts.cursor,facts.stage_flag,facts.context_eq,facts.outside,facts.time,facts.boundaries,?_⟩
  intro current present
  refine ⟨(facts.proper current present).1,?_⟩
  intro point selected
  rw [same current present point selected]
  exact (facts.proper current present).2 point selected

noncomputable def statementClock (source : Label → Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk

noncomputable def traceClockSum (source : Label → Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock source)).sum

noncomputable def chargedCost (source : Label → Statement C) (trace : List (State C)) : Nat :=
  trace.length+traceClockSum source trace

variable {source : Label → Statement C} {context : C} {background : RatInput.Stack → List Bool}
  {input : StatisticalInput I} {contract : Contract I} {budget : Rat} {trace : List (State C)} {final : State C}

theorem traceClockSum_le (facts : Facts source context background input contract budget trace final) :
    traceClockSum source trace≤coefficient^2*(scale background (preparationInput input contract budget).length)^4 := by
  let cap:=coefficient*(scale background (preparationInput input contract budget).length)^2
  have termwise : ∀ value∈trace.dropLast.map (statementClock source),value≤cap := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : traceClockSum source trace≤trace.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock source)) cap termwise
  have length : trace.dropLast.length≤cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum source trace≤cap*cap := sum.trans (Nat.mul_le_mul_right cap length)
    _=_ := by dsimp only [cap]; ring

theorem chargedCost_le (facts : Facts source context background input contract budget trace final) :
    chargedCost source trace≤(coefficient^2+coefficient)*(scale background (preparationInput input contract budget).length)^4 := by
  have base : 1≤scale background (preparationInput input contract budget).length := by unfold scale; omega
  have powers := Nat.pow_le_pow_right base (by decide : (2:Nat)≤4)
  have count:=facts.time.trans (Nat.mul_le_mul_left coefficient powers)
  calc
    chargedCost source trace≤coefficient*(scale background (preparationInput input contract budget).length)^4+
      coefficient^2*(scale background (preparationInput input contract budget).length)^4 := Nat.add_le_add count (traceClockSum_le facts)
    _=_ := by ring

abbrev finiteStore (C : Type*) [Fintype C] : Fintype (Store C) := inferInstance

namespace Public

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (labels : Finset Label),
      TM2.Supports source labels ∧ source .done=.halt ∧
      ∀ {I : Instance} (context : C) (background : RatInput.Stack → List Bool)
        (input : StatisticalInput I) (contract : Contract I) (budget : Rat),
        ∃ trace final,Facts source context background input contract budget trace final := by
  refine ⟨program .halt,Finset.univ,supports,rfl,?_⟩
  intro I context background input contract budget
  exact actual_polynomial context background input contract budget

theorem static_caller (caller : Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final,Facts (program caller) context background input contract budget trace final ∧
      chargedCost (program caller) trace≤(coefficient^2+coefficient)*
        (scale background (preparationInput input contract budget).length)^4 := by
  obtain ⟨trace,final,old⟩:=actual_polynomial context background input contract budget
  have facts:=retarget caller old
  exact ⟨trace,final,facts,chargedCost_le facts⟩

theorem from_default (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final,Facts (program (C := Unit) .halt) () (fun _ => []) input contract budget trace final ∧
      trace.head?=some (TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store Unit) 0
        (preparationInput input contract budget)) ∧
      chargedCost (program .halt) trace≤(coefficient^2+coefficient)*(arithmeticScale input contract budget)^4 := by
  obtain ⟨trace,final,facts⟩:=actual_polynomial () (fun _ => []) input contract budget
  have scaleBound : scale (fun _ => []) (preparationInput input contract budget).length≤arithmeticScale input contract budget := by
    simpa [scale,RatInput.occupied] using
      Budget.length_le_arithmeticScale input contract budget
  exact ⟨trace,final,facts,facts.first.trans (congrArg some (initial_default _)),
    (chargedCost_le facts).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scaleBound 4))⟩

end Public
end RootB234.PrepEntry.StageFront
