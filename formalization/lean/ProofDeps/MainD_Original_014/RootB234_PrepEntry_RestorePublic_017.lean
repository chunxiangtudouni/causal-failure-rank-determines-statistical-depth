module

public import RootB234_PrepEntry_RestoreResources_016
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Restore

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PSTRTMWordPreparationFront214

variable {C : Type*} {I : Instance}

def space (length : Nat) : Nat := length+16*(262144*(length+1)^2)
def coefficient : Nat := 268435456

theorem resource_envelope (length : Nat) :
    262144*(length+1)^2≤coefficient*(length+1)^2 ∧
    16*space length≤coefficient*(length+1)^2 ∧
    16*(space length+16)≤coefficient*(length+1)^2 ∧
    32*(space length+17)≤coefficient*(length+1)^2 := by
  have base : 1≤length+1 := by omega
  have positive : 1≤(length+1)^2 := Nat.pow_le_pow_left base 2
  have linear : length+1≤(length+1)^2 := by nlinarith only [base]
  dsimp only [space,coefficient]
  constructor
  · omega
  constructor
  · nlinarith only [positive,linear]
  constructor <;> nlinarith only [positive,linear]

structure Facts (source : Label → Statement C) (context : C)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry context (preparationInput input contract budget))
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  active : final.l=some .done
  context_eq : callerContext final.var=context
  contents : final.stk=outputBank (preparationInput input contract budget) I.stageCount I.toolCount
  time : trace.length≤coefficient*((preparationInput input contract budget).length+1)^2
  boundaries : ∀ current∈trace,callerContext current.var=context ∧
    (∀ slot,(current.stk slot).length≤coefficient*((preparationInput input contract budget).length+1)^2) ∧
    RatInput.occupied current.stk≤coefficient*((preparationInput input contract budget).length+1)^2 ∧
    ∀ slot,¬Work slot→current.stk slot=[]
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        callerContext node.1=context ∧
        (∀ slot,(node.2 slot).length≤coefficient*((preparationInput input contract budget).length+1)^2) ∧
        RatInput.occupied node.2≤coefficient*((preparationInput input contract budget).length+1)^2 ∧
        ∀ slot,¬Work slot→node.2 slot=[]) ∧
      ScannerStatement.clock (source point) current.var current.stk≤coefficient*((preparationInput input contract budget).length+1)^2

theorem actual_polynomial (context : C) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final,Facts (program .halt) context input contract budget trace final := by
  obtain ⟨trace,final,first,chain,last,active,contents,count⟩ :=
    actual .halt context input contract budget
  let bits:=preparationInput input contract budget
  let before:=entry context bits
  have frames : ∀ slot,¬Work slot→before.stk slot=[] := by
    intro slot untouched
    have notZero : slot≠0 := by intro same; subst slot; exact untouched (by decide)
    change (entry context bits).stk slot=[]
    rw [entry_slots]
    simp only [notZero,ite_false]
  have initialBound : ∀ slot,(before.stk slot).length≤bits.length := by
    intro slot
    have bound:=RatInput.Encoder.point_mass before.stk slot
    rw [entry_mass] at bound
    exact bound
  have bounds:=trace_resources trace before (fun _ => []) bits.length first chain initialBound frames
  have contexts:=trace_context trace before first chain
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤space bits.length := by
    intro current present slot
    exact ((bounds current present).1 slot).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 16 count) _)
  have caps:=resource_envelope bits.length
  have proper:=NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last active
  refine ⟨trace,final,⟨first,chain,last,active,contexts final (List.mem_of_getLast? last),contents,
    count.trans caps.1,?_,?_⟩⟩
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
    have nodeBound:=(internal.1 node inside).2.1
    refine ⟨((internal.1 node inside).1).trans (contexts current (List.mem_of_mem_dropLast present)),?_,
      (RatInput.Encoder.occupied_bound node.2 _ nodeBound).trans caps.2.2.1,?_⟩
    · intro slot
      exact (nodeBound slot).trans
        ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.2.1)
    · intro slot untouched
      exact ((internal.1 node inside).2.2 slot untouched).trans
        ((bounds current (List.mem_of_mem_dropLast present)).2 slot untouched)

theorem program_eq_before_done (caller : Statement C) (point : Label) (different : point≠.done) :
    program caller point=program .halt point := by
  cases point with
  | copy point | prep point | rewind point => rfl
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

theorem retarget (caller : Statement C) {context : C} {input : StatisticalInput I} {contract : Contract I}
    {budget : Rat} {trace : List (State C)} {final : State C}
    (facts : Facts (program .halt) context input contract budget trace final) :
    Facts (program caller) context input contract budget trace final := by
  have same : ∀ current∈trace.dropLast,∀ point,current.l=some point→program caller point=program .halt point := by
    intro current present point selected
    apply program_eq_before_done caller point
    intro equal
    subst point
    exact (facts.proper current present).1 selected
  refine ⟨facts.first,chain_same _ _ _ facts.chain same,facts.last,facts.active,
    facts.context_eq,facts.contents,facts.time,facts.boundaries,?_⟩
  intro current present
  refine ⟨(facts.proper current present).1,?_⟩
  intro point selected
  rw [same current present point selected]
  exact (facts.proper current present).2 point selected


def statementClock (source : Label → Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk

def traceClockSum (source : Label → Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock source)).sum

def chargedCost (source : Label → Statement C) (trace : List (State C)) : Nat :=
  trace.length+traceClockSum source trace

variable {source : Label → Statement C} {context : C} {input : StatisticalInput I}
  {contract : Contract I} {budget : Rat} {trace : List (State C)} {final : State C}

theorem traceClockSum_le (facts : Facts source context input contract budget trace final) :
    traceClockSum source trace≤coefficient^2*((preparationInput input contract budget).length+1)^4 := by
  let cap:=coefficient*((preparationInput input contract budget).length+1)^2
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
    _=coefficient^2*((preparationInput input contract budget).length+1)^4 := by dsimp only [cap]; ring

theorem chargedCost_le (facts : Facts source context input contract budget trace final) :
    chargedCost source trace≤(coefficient^2+coefficient)*((preparationInput input contract budget).length+1)^4 := by
  have base : 1≤(preparationInput input contract budget).length+1 := by omega
  have powers : ((preparationInput input contract budget).length+1)^2≤((preparationInput input contract budget).length+1)^4 :=
    Nat.pow_le_pow_right base (by decide : (2:Nat)≤4)
  have count:=facts.time.trans (Nat.mul_le_mul_left coefficient powers)
  calc
    chargedCost source trace≤coefficient*((preparationInput input contract budget).length+1)^4+
      coefficient^2*((preparationInput input contract budget).length+1)^4 := Nat.add_le_add count (traceClockSum_le facts)
    _=_ := by ring

theorem length_le_arithmeticScale (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    (preparationInput input contract budget).length+1≤arithmeticScale input contract budget := by
  dsimp only [arithmeticScale,inputSize]
  omega

abbrev finiteStore (C : Type*) [Fintype C] : Fintype (Store C) := inferInstance

namespace Public

theorem positive_coefficients : 0<coefficient ∧ 0<coefficient^2 ∧ 0<coefficient^2+coefficient := by decide

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (labels : Finset Label),
      TM2.Supports source labels ∧ source .done=.halt ∧
      ∀ {I : Instance} (context : C) (input : StatisticalInput I) (contract : Contract I) (budget : Rat),
        ∃ trace final,Facts source context input contract budget trace final ∧
          traceClockSum source trace≤coefficient^2*(arithmeticScale input contract budget)^4 ∧
          chargedCost source trace≤(coefficient^2+coefficient)*(arithmeticScale input contract budget)^4 := by
  refine ⟨program .halt,Finset.univ,supports,rfl,?_⟩
  intro I context input contract budget
  obtain ⟨trace,final,facts⟩:=actual_polynomial context input contract budget
  have powers:=Nat.pow_le_pow_left (length_le_arithmeticScale input contract budget) 4
  exact ⟨trace,final,facts,(traceClockSum_le facts).trans (Nat.mul_le_mul_left _ powers),
    (chargedCost_le facts).trans (Nat.mul_le_mul_left _ powers)⟩

theorem static_caller (caller : Statement C) (context : C) (input : StatisticalInput I)
    (contract : Contract I) (budget : Rat) :
    ∃ trace final,Facts (program caller) context input contract budget trace final ∧
      traceClockSum (program caller) trace≤coefficient^2*(arithmeticScale input contract budget)^4 ∧
      chargedCost (program caller) trace≤(coefficient^2+coefficient)*(arithmeticScale input contract budget)^4 := by
  obtain ⟨trace,final,old⟩:=actual_polynomial context input contract budget
  have facts:=retarget caller old
  have powers:=Nat.pow_le_pow_left (length_le_arithmeticScale input contract budget) 4
  exact ⟨trace,final,facts,(traceClockSum_le facts).trans (Nat.mul_le_mul_left _ powers),
    (chargedCost_le facts).trans (Nat.mul_le_mul_left _ powers)⟩


theorem from_default (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final,Facts (program (C := Unit) .halt) () input contract budget trace final ∧
      trace.head?=some (TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store Unit) 0
        (preparationInput input contract budget)) := by
  obtain ⟨trace,final,facts⟩:=actual_polynomial () input contract budget
  exact ⟨trace,final,facts,facts.first.trans (congrArg some (initial_default _))⟩

end Public
end RootB234.PrepEntry.Restore
