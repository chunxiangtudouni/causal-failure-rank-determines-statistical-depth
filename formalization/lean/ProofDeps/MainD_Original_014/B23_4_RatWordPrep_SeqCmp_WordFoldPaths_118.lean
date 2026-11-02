module

public import B23_4_RatWordPrep_SeqCmp_WordFoldCode_117

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

theorem init_path (caller : Statement C) (run : List (OddsInit.State C))
    (before final : OddsInit.State C) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (OddsInit.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map initCfg).head?=some (initCfg before) ∧
    (run.map initCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map initCfg).getLast?=some (initCfg final) := by
  have proper := NativeMulLink.no_early_halt_port (OddsInit.program .halt) .done rfl run final chain last active
  have mapped := LabelMap.actual_path_on initLabel (OddsInit.program .halt) (program caller)
    run before final first chain last (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [initLabel,different,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem lookup_path (caller : Statement C) (truth : Bool) (registers : FullStore.Aux)
    (run : List (Lookup.State C)) (before final : Lookup.State C) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Lookup.program truth .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map (lookupCfg truth registers)).head?=some (lookupCfg truth registers before) ∧
    (run.map (lookupCfg truth registers)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (lookupCfg truth registers)).getLast?=some (lookupCfg truth registers final) := by
  let old := Lookup.program (C := C) truth .halt
  let lifted : Lookup.Label → TM2.Stmt RatInput.Alphabet Lookup.Label (Store C) := ContextLift.machine old
  have contextual := ContextLift.actual_path old registers run before final first chain last
  have proper := NativeMulLink.no_early_halt_port lifted .done rfl _ _ contextual.2.1 contextual.2.2.1 active
  have mapped := LabelMap.actual_path_on (if truth then trueLabel else falseLabel) lifted (program caller)
    _ _ _ contextual.1 contextual.2.1 contextual.2.2.1 (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      cases truth with
      | false =>
        change program caller (falseLabel point)=
          LabelMap.statement falseLabel (ContextLift.statement (Lookup.program false .halt point))
        simp only [falseLabel,different,ite_false,program]
      | true =>
        change program caller (trueLabel point)=
          LabelMap.statement trueLabel (ContextLift.statement (Lookup.program true .halt point))
        simp only [trueLabel,different,ite_false,program])
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

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

end B23_4_RatWordPrep.WordFold
