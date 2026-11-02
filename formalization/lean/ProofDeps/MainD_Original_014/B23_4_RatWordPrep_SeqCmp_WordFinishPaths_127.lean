module

public import B23_4_RatWordPrep_SeqCmp_WordFinishCode_126

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

theorem transport_path {σ Λ : Type*} (iso : σ ≃ Store C) (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (allowed : Λ → Prop) (trace : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final)
    (proper : ∀ current∈trace.dropLast,∀ point,current.l=some point→allowed point)
    (same : ∀ point,allowed point→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (old point))) :
    let mapCfg := fun current => LabelMap.configuration rename (StoreIso.configuration iso current)
    (trace.map mapCfg).head?=some (mapCfg before) ∧
    (trace.map mapCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map mapCfg).getLast?=some (mapCfg final) := by
  let changed := StoreIso.machine iso old
  have storePath := StoreIso.actual_path_on iso old changed trace before final first chain last
    (by intro current member point selected; rfl)
  have mapped := LabelMap.actual_path_on rename changed (program caller)
    _ _ _ storePath.1 storePath.2.1 storePath.2.2.1 (by
      intro current member point selected
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact same point (proper original present point selected))
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem single_port_path {σ Λ : Type*} (iso : σ ≃ Store C) (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt)
    (trace : List (TM2.Cfg RatInput.Alphabet Λ σ)) (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (old point))) :
    let mapCfg := fun current => LabelMap.configuration rename (StoreIso.configuration iso current)
    (trace.map mapCfg).head?=some (mapCfg before) ∧
    (trace.map mapCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map mapCfg).getLast?=some (mapCfg final) := by
  have proper := NativeMulLink.no_early_halt_port old port atPort trace final chain last active
  exact transport_path iso rename old caller (fun point => point≠port) trace before final first chain last
    (by intro current member point selected equal; subst point; exact proper current member selected) same

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) : Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)

theorem Segment.append_length_le {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

theorem pushCells_stepAux (bits : List Bool) (body : Statement C)
    (memory : Store C) (slots : RatInput.Stack → List Bool) :
    TM2.stepAux (pushCells bits body) memory slots=
      TM2.stepAux body memory (Function.update slots 15 (bits++slots 15)) := by
  induction bits generalizing body with
  | nil => simp only [pushCells,List.nil_append,Function.update_eq_self]
  | cons bit bits ih =>
    rw [pushCells,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

def oneResult (job : OneJob) (before : State C) : State C :=
  ⟨some (oneNext job),before.var,Function.update before.stk 15 (RatInput.Encoder.packet (1:Rat) []++before.stk 15)⟩

theorem one_step (caller : Statement C) (job : OneJob) (before : State C)
    (active : before.l=some (.one job)) :
    TM2.step (program caller) before=some (oneResult job before) := by
  cases before with
  | mk point memory slots =>
    change point=some (.one job) at active
    subst point
    simp only [TM2.step,program,pushCells_stepAux,TM2.stepAux,oneResult]

def actual_one (caller : Statement C) (job : OneJob) (before : State C)
    (active : before.l=some (.one job)) :
    Segment caller before (oneResult job before) :=
  ⟨[before,oneResult job before],rfl,List.isChain_cons_cons.mpr ⟨one_step caller job before active,by simp⟩,rfl⟩

end B23_4_RatWordPrep.WordFinish
