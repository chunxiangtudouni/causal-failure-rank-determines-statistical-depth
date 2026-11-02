module
public import RootB236_Controller_DFSDriver_Nodes002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}

def transported {Λ σ : Type*} (roles : Stack ≃ Stack) (iso : σ ≃ Store C) (labels : Λ → Label)
    (before : TM2.Cfg Alphabet Λ σ) : State C :=
  LabelMap.configuration labels (StackIso.configuration roles (StoreIso.configuration iso before))
theorem transported_edge {Λ σ : Type*} (good bad pop finish : Statement C) (roles : Stack ≃ Stack)
    (iso : σ ≃ Store C) (labels : Λ → Label) (old : Λ → TM2.Stmt Alphabet Λ σ)
    (before after : TM2.Cfg Alphabet Λ σ) (edge : TM2.step old before=some after)
    (code : ∀ point,before.l=some point → program good bad pop finish (labels point)=
      LabelMap.statement labels (StackIso.statement roles (StoreIso.statement iso (old point)))) :
    TM2.step (program good bad pop finish) (transported roles iso labels before)=some (transported roles iso labels after) := by
  unfold transported
  rw [LabelMap.step_configuration_on labels
    (fun point => StackIso.statement roles (StoreIso.statement iso (old point))) (program good bad pop finish) _ code]
  rw [StackIso.step_configuration_on roles (StoreIso.machine iso old)
    (fun point => StackIso.statement roles (StoreIso.statement iso (old point))) _ (by intros;rfl)]
  rw [StoreIso.step_configuration iso old,edge]
  rfl

theorem transported_inside {Λ σ : Type*} (roles : Stack ≃ Stack) (iso : σ ≃ Store C) (labels : Λ → Label)
    (before : TM2.Cfg Alphabet Λ σ) (proper : ∀ point,before.l=some point → ¬Boundary (labels point)) :
    Inside (transported roles iso labels before) := by
  intro selected active
  cases before with
  | mk position memory slots =>
    cases position with
    | none => cases active
    | some point =>
      have same : labels point=selected := Option.some.inj active
      subst selected;exact proper point rfl

theorem mapped_path {Λ σ : Type*} (good bad pop finish : Statement C) (roles : Stack ≃ Stack)
    (iso : σ ≃ Store C) (labels : Λ → Label) (old : Λ → TM2.Stmt Alphabet Λ σ)
    (trace : List (TM2.Cfg Alphabet Λ σ)) (before final : TM2.Cfg Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun x y => TM2.step old x=some y))
    (last : trace.getLast?=some final)
    (code : ∀ current∈trace.dropLast,∀ point,current.l=some point → program good bad pop finish (labels point)=
      LabelMap.statement labels (StackIso.statement roles (StoreIso.statement iso (old point))))
    (proper : ∀ current∈trace.dropLast,∀ point,current.l=some point → ¬Boundary (labels point)) :
    Path good bad pop finish (transported roles iso labels before) (transported roles iso labels final) (trace.length-1) := by
  exact Path.of_mapped good bad pop finish (transported roles iso labels) _ trace before final first chain last
    (fun current member next edge => transported_edge good bad pop finish roles iso labels old current next edge (code current member))
    (fun current member => transported_inside roles iso labels current (proper current member))

private theorem labelMap_identity {Λ σ : Type*} (body : TM2.Stmt Alphabet Λ σ) :
    StackIso.statement (Equiv.refl Stack) (StoreIso.statement (Equiv.refl σ) body)=body := by
  induction body <;> simp_all [StackIso.statement,StoreIso.statement]
private theorem store_identity {Λ : Type*} (roles : Stack ≃ Stack) (body : TM2.Stmt Alphabet Λ (Store C)) :
    StackIso.statement roles (StoreIso.statement (Equiv.refl (Store C)) body)=StackIso.statement roles body := by
  have identity : StoreIso.statement (Equiv.refl (Store C)) body=body := by
    induction body <;> simp_all [StoreIso.statement]
  rw [identity]
private theorem role_identity {Λ σ : Type*} (body : TM2.Stmt Alphabet Λ σ) :
    StackIso.statement (Equiv.refl Stack) body=body := by
  induction body <;> simp_all [StackIso.statement]

theorem copy_path (good bad pop finish : Statement C) (phase : CopyPhase)
    (bg : Stack → List Bool) (memory : B23_4_RatWordPrep.WholeCopy.Store (C×Ordering)) (input backup scratch : List Bool) :
    ∃ trace,B23_4_RatWordPrep.WholeCopy.Facts (B23_4_RatWordPrep.WholeCopy.program .halt) bg memory input backup scratch trace ∧
      Path good bad pop finish
        (transported (copyRoles phase) BestUpdate.storeIso (copyMap phase)
          (B23_4_RatWordPrep.WholeCopy.state bg .boot memory input backup scratch))
        (transported (copyRoles phase) BestUpdate.storeIso (copyMap phase)
          (B23_4_RatWordPrep.WholeCopy.state bg .done (memory.1,true,true) input (input.reverse++backup) scratch))
        (2*input.length+3) := by
  obtain ⟨trace,facts⟩:=B23_4_RatWordPrep.WholeCopy.actual_bounded bg memory input backup scratch
  have path:=mapped_path good bad pop finish (copyRoles phase) BestUpdate.storeIso (copyMap phase)
    (B23_4_RatWordPrep.WholeCopy.program .halt) trace _ _ facts.first facts.chain facts.last
    (by intro current member point active
        exact copy_code good bad pop finish phase point (by intro same;subst point;exact (facts.proper current member).1 active))
    (by intro current member point active
        have proper : point≠B23_4_RatWordPrep.WholeCopy.Label.done := by intro same;subst point;exact (facts.proper current member).1 active
        cases point <;> simp_all [copyMap,Boundary,pushGood,pushBad,popFrame,rootDone])
  rw [facts.count] at path
  exact ⟨trace,facts,path⟩

theorem select_path (good bad pop finish : Statement C) (bg : Stack → List Bool)
    (memory : SelectErase.Store (C×Ordering)) (eligible remaining old5 : List Bool) (same : eligible.length=remaining.length) :
    ∃ trace final,SelectErase.Facts bg memory eligible remaining old5 trace final ∧
      Path good bad pop finish
        (transported (Equiv.refl Stack) BestUpdate.storeIso selectMap (SelectErase.initial bg memory eligible remaining old5))
        (transported (Equiv.refl Stack) BestUpdate.storeIso selectMap final) (trace.length-1) := by
  obtain ⟨trace,final,facts,_clock,_charge⟩:=SelectErase.Public.actual bg memory eligible remaining old5 same
  refine ⟨trace,final,facts,?_⟩
  apply mapped_path good bad pop finish (Equiv.refl Stack) BestUpdate.storeIso selectMap SelectErase.source trace _ _ facts.first facts.chain facts.last
  · intro current member point active
    rw [role_identity]
    exact select_code good bad pop finish point
      (by intro same;subst point;exact (facts.proper current member).1.1 active)
      (by intro same;subst point;exact (facts.proper current member).1.2 active)
  · intro current member point active
    have nf : point≠SelectErase.Label.found := by intro same;subst point;exact (facts.proper current member).1.1 active
    have ne : point≠SelectErase.Label.empty := by intro same;subst point;exact (facts.proper current member).1.2 active
    cases point <;> simp_all [selectMap,Boundary,pushGood,pushBad,popFrame,rootDone]

theorem resume_path (good bad pop finish : Statement C) (bg : Stack → List Bool)
    (memory : ResumeErase.Store (C×Ordering)) (bits parent old4 old5 : List Bool) (k : Nat)
    (extent : k+bits.length=parent.length) :
    ∃ trace final,ResumeErase.Facts bg memory bits parent old4 old5 k trace final ∧
      Path good bad pop finish
        (transported (Equiv.refl Stack) BestUpdate.storeIso resumeMap (ResumeErase.initial bg memory bits parent old4 old5 k))
        (transported (Equiv.refl Stack) BestUpdate.storeIso resumeMap final) (trace.length-1) := by
  obtain ⟨trace,final,facts,_clock,_charge⟩:=ResumeErase.Public.actual bg memory bits parent old4 old5 k extent
  refine ⟨trace,final,facts,?_⟩
  apply mapped_path good bad pop finish (Equiv.refl Stack) BestUpdate.storeIso resumeMap ResumeErase.source trace _ _ facts.first facts.chain facts.last
  · intro current member point active
    rw [role_identity]
    exact resume_code good bad pop finish point
      (by intro same;subst point;exact (facts.proper current member).1.1 active)
      (by intro same;subst point;exact (facts.proper current member).1.2 active)
  · intro current member point active
    have nf : point≠ResumeErase.foundPort := by intro same;subst point;exact (facts.proper current member).1.1 active
    have ne : point≠ResumeErase.emptyPort := by intro same;subst point;exact (facts.proper current member).1.2 active
    cases point with
    | clear => simp [resumeMap,Boundary,pushGood,pushBad,popFrame,rootDone]
    | body point => cases point <;> simp_all [resumeMap,ResumeErase.foundPort,ResumeErase.emptyPort,Boundary,pushGood,pushBad,popFrame,rootDone]

theorem best_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a b tool : Nat) (best tail : List Bool) :
    ∃ trace final,BestUpdate.Facts .halt bg context ha hb flag ord a b tool best tail trace final ∧
      Path good bad pop finish
        (transported badRoles (Equiv.refl (Store C)) bestMap
          (BestUpdate.state BestUpdate.boot (context,ha,hb,ord) (BestUpdate.bank bg a b tool best flag tail)))
        (transported badRoles (Equiv.refl (Store C)) bestMap final) (trace.length-1) := by
  obtain ⟨trace,final,facts⟩:=BestUpdate.actual_facts .halt bg context ha hb flag ord a b tool best tail
  refine ⟨trace,final,facts,?_⟩
  apply mapped_path good bad pop finish badRoles (Equiv.refl (Store C)) bestMap (BestUpdate.program .halt) trace _ _ facts.first facts.chain facts.last
  · intro current member point active
    rw [store_identity]
    exact best_code good bad pop finish point (by intro same;subst point;exact facts.proper current member active)
  · intro current member point active
    have proper : point≠BestUpdate.done := by intro same;subst point;exact facts.proper current member active
    simp only [bestMap,proper,ite_false]
    simp [Boundary,pushGood,pushBad,popFrame,rootDone]

theorem merge_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (limit a b : Nat) :
    ∃ trace final,RankMerge.Facts .halt bg context ha hb ord limit a b trace final ∧
      Path good bad pop finish
        (transported (Equiv.refl Stack) (Equiv.refl (Store C)) mergeMap
          (RankMerge.state RankMerge.entry (context,ha,hb,ord) (RankMerge.bank bg limit a b)))
        (transported (Equiv.refl Stack) (Equiv.refl (Store C)) mergeMap final) (trace.length-1) := by
  obtain ⟨trace,final,facts⟩:=RankMerge.actual_facts .halt bg context ha hb ord limit a b
  refine ⟨trace,final,facts,?_⟩
  apply mapped_path good bad pop finish (Equiv.refl Stack) (Equiv.refl (Store C)) mergeMap (RankMerge.program .halt) trace _ _ facts.first facts.chain facts.last
  · intro current member point active
    rw [labelMap_identity]
    exact merge_code good bad pop finish point (by intro same;subst point;exact facts.proper current member active)
  · intro current member point active
    have proper : point≠RankMerge.done := by intro same;subst point;exact facts.proper current member active
    simp only [mergeMap,proper,ite_false]
    simp [Boundary,pushGood,pushBad,popFrame,rootDone]
end RootB236.Controller.DFSDriver
