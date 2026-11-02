module

public import B23_4_RatWordPrep_SeqCmp_LookupCode_091

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem transport_path {σ Λ : Type*} (iso : σ ≃ Store C) (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (truth : Bool) (caller : Statement C)
    (allowed : Λ → Prop) (trace : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final)
    (proper : ∀ current∈trace.dropLast,∀ point,current.l=some point→allowed point)
    (same : ∀ point,allowed point→program truth caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (old point))) :
    let mapCfg := fun current => LabelMap.configuration rename (StoreIso.configuration iso current)
    (trace.map mapCfg).head?=some (mapCfg before) ∧
    (trace.map mapCfg).IsChain (fun a b => TM2.step (program truth caller) a=some b) ∧
    (trace.map mapCfg).getLast?=some (mapCfg final) := by
  let changed := StoreIso.machine iso old
  have storePath := StoreIso.actual_path_on iso old changed trace before final first chain last
    (by intro current member point selected; rfl)
  have mapped := LabelMap.actual_path_on rename changed (program truth caller)
    _ _ _ storePath.1 storePath.2.1 storePath.2.2.1 (by
      intro current member point selected
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact same point (proper original present point selected))
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem single_port_path {σ Λ : Type*} (iso : σ ≃ Store C) (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (truth : Bool) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt)
    (trace : List (TM2.Cfg RatInput.Alphabet Λ σ)) (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program truth caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (old point))) :
    let mapCfg := fun current => LabelMap.configuration rename (StoreIso.configuration iso current)
    (trace.map mapCfg).head?=some (mapCfg before) ∧
    (trace.map mapCfg).IsChain (fun a b => TM2.step (program truth caller) a=some b) ∧
    (trace.map mapCfg).getLast?=some (mapCfg final) := by
  have proper := NativeMulLink.no_early_halt_port old port atPort trace final chain last active
  exact transport_path iso rename old truth caller (fun point => point≠port) trace before final first chain last
    (by intro current member point selected equal; subst point; exact proper current member selected) same

structure Segment (truth : Bool) (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program truth caller) a=some b)
  last : trace.getLast?=some final

def Segment.append {truth : Bool} {caller : Statement C} {before middle final : State C}
    (front : Segment truth caller before middle) (back : Segment truth caller middle final) : Segment truth caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)

end B23_4_RatWordPrep.Lookup
