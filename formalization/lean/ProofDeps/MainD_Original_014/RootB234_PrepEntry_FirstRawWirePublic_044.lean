module

public import RootB234_PrepEntry_FirstRawWire_043
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.FirstRaw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*} {I : Instance}

theorem actual_wire_polynomial (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final left,Facts (program .halt) context background input contract budget trace final ∧
      NatPrefix.tape final.stk=Tape.mk₂ left (wireSuffix input contract budget++[true]) := by
  obtain ⟨trace,final,left,first,chain,last,active,natural,rational,scratch,cursor,contextEq,outside,count⟩:=
    actual_wire context background input contract budget
  let suffix:=wireSuffix input contract budget
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
  refine ⟨trace,final,left,⟨first,chain,last,active,natural,rational,scratch,⟨suffix,left,cursor⟩,
    contextEq,outside,timeBound.trans caps.1,?_,?_⟩,cursor⟩
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

namespace WirePublic

theorem static_caller (caller : Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final left,Facts (program caller) context background input contract budget trace final ∧
      NatPrefix.tape final.stk=Tape.mk₂ left (wireSuffix input contract budget++[true]) ∧
      chargedCost (program caller) trace≤(coefficient^2+coefficient)*
        (scale background (preparationInput input contract budget).length)^4 := by
  obtain ⟨trace,final,left,old,cursor⟩:=actual_wire_polynomial context background input contract budget
  have facts:=retarget caller old
  exact ⟨trace,final,left,facts,cursor,chargedCost_le facts⟩

theorem stage0_fields {source : Label → Statement C} {context : C} {background : RatInput.Stack → List Bool}
    {input : StatisticalInput I} {contract : Contract I} {budget : Rat} {trace : List (State C)} {final : State C}
    (facts : Facts source context background input contract budget trace final) (positive : 0<I.stageCount) :
    final.stk 14=NatField.packet (input.experiment ⟨0,positive⟩).alphabetSize (background 14) ∧
      final.stk 13=RatInput.Encoder.packet (input.experiment ⟨0,positive⟩).priorOne (background 13) := by
  have natural:=facts.natural
  rw [lastNatural_positive input contract positive] at natural
  have rational:=facts.rational
  rw [show firstValue input budget=(input.experiment ⟨0,positive⟩).priorOne from dite_eq_left positive] at rational
  exact ⟨natural,rational⟩

theorem stage0_cursor {input : StatisticalInput I} {contract : Contract I} {budget : Rat}
    {final : State C} {left : List Bool} (positive : 0<I.stageCount)
    (actual : NatPrefix.tape final.stk=Tape.mk₂ left (wireSuffix input contract budget++[true])) :
    ListBlank.mk (final.stk 0)=ListBlank.mk
      (encodeDatum (.rational (input.experiment ⟨0,positive⟩).observationFee)++
        (channelValues (input.experiment ⟨0,positive⟩)).flatMap (fun x => encodeDatum (.rational x))++
        (afterFirstExperiment input contract budget).flatMap encodeDatum++[true]) := by
  have right:=congrArg Tape.right₀ actual
  rw [wireSuffix_positive input contract budget positive] at right
  simpa only [NatPrefix.tape,Tape.mk₂,Tape.mk'_right₀,List.append_assoc] using right

theorem from_default (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final left,Facts (program (C := Unit) .halt) () (fun _ => []) input contract budget trace final ∧
      trace.head?=some (TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store Unit) 0
        (preparationInput input contract budget)) ∧
      NatPrefix.tape final.stk=Tape.mk₂ left (wireSuffix input contract budget++[true]) ∧
      chargedCost (program .halt) trace≤(coefficient^2+coefficient)*(arithmeticScale input contract budget)^4 := by
  obtain ⟨trace,final,left,facts,cursor⟩:=actual_wire_polynomial () (fun _ => []) input contract budget
  have scaleBound : scale (fun _ => []) (preparationInput input contract budget).length≤arithmeticScale input contract budget := by
    simpa [scale,RatInput.occupied] using Budget.length_le_arithmeticScale input contract budget
  exact ⟨trace,final,left,facts,facts.first.trans (congrArg some (initial_default _)),cursor,
    (chargedCost_le facts).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scaleBound 4))⟩

end WirePublic
end RootB234.PrepEntry.FirstRaw
