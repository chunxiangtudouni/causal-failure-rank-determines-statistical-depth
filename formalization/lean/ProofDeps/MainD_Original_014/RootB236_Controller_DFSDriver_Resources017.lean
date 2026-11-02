module
public import RootB236_Controller_DFSDriver_Frames011

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}

/-- One literal finite source, fixed before all staged counters and masks. -/
def source : Label → Statement C := program .halt

private theorem readonly_label {σ D Λ Ω : Type*} (project : σ → D) (labels : Λ → Ω)
    (body : TM2.Stmt Alphabet Λ σ) (good : B23_4_RatWordPrep.RawGetter.Readonly project body) :
    B23_4_RatWordPrep.RawGetter.Readonly project (LabelMap.statement labels body) := by
  induction body <;> simp_all [LabelMap.statement,B23_4_RatWordPrep.RawGetter.Readonly]
private theorem readonly_roles {σ D Λ : Type*} (project : σ → D) (roles : Stack ≃ Stack)
    (body : TM2.Stmt Alphabet Λ σ) (good : B23_4_RatWordPrep.RawGetter.Readonly project body) :
    B23_4_RatWordPrep.RawGetter.Readonly project (StackIso.statement roles body) := by
  induction body <;> simp_all [StackIso.statement,B23_4_RatWordPrep.RawGetter.Readonly]
private theorem readonly_comp {σ D E Λ : Type*} (project : σ → D) (outer : D → E)
    (body : TM2.Stmt Alphabet Λ σ) (good : B23_4_RatWordPrep.RawGetter.Readonly project body) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory => outer (project memory)) body := by
  induction body with
  | push _ _ _ ih => exact ih good
  | pop _ _ _ ih | peek _ _ _ ih => exact ⟨fun memory value => congrArg outer (good.1 memory value),ih good.2⟩
  | load _ _ ih => exact ⟨fun memory => congrArg outer (good.1 memory),ih good.2⟩
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial
private theorem readonly_iso {σ τ D Λ : Type*} (iso : σ ≃ τ) (project : τ → D)
    (body : TM2.Stmt Alphabet Λ σ)
    (good : B23_4_RatWordPrep.RawGetter.Readonly (fun memory => project (iso memory)) body) :
    B23_4_RatWordPrep.RawGetter.Readonly project (StoreIso.statement iso body) := by
  induction body with
  | push _ _ _ ih => exact ih good
  | pop _ _ _ ih | peek _ _ _ ih =>
    refine ⟨?_,ih good.2⟩
    intro memory value
    simpa only [Equiv.apply_symm_apply] using good.1 (iso.symm memory) value
  | load _ _ ih =>
    refine ⟨?_,ih good.2⟩
    intro memory
    simpa only [Equiv.apply_symm_apply] using good.1 (iso.symm memory)
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

theorem core_readonly (point : Core) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (DFSDriver.source point) := by
  cases point with
  | control point =>
    fin_cases point
    all_goals dsimp [DFSDriver.source,DFSDriver.program,B23_4_RatWordPrep.RawGetter.Readonly,capture,BestUpdate.capturePresent]
    all_goals repeat' constructor
    all_goals intros;rfl
  | copy phase point =>
    apply readonly_label
    apply readonly_roles
    apply readonly_iso
    exact readonly_comp (fun memory : (C×Ordering)×Bool×Bool => memory.1) (fun context : C×Ordering => context.1) _ (B23_4_RatWordPrep.WholeCopy.program_readonly point)
  | select point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun memory : (C×Ordering)×Bool×Bool => memory.1) (fun context : C×Ordering => context.1) _ (SelectErase.program_readonly point)
  | resume point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun memory : (C×Ordering)×Bool×Bool => memory.1) (fun context : C×Ordering => context.1) _ (ResumeErase.program_readonly point)
  | best point =>
    apply readonly_label
    apply readonly_roles
    by_cases endPoint : point=BestUpdate.done
    · subst point;trivial
    · exact BestUpdate.program_readonly .halt point endPoint
  | merge point =>
    apply readonly_label
    by_cases endPoint : point=RankMerge.done
    · subst point;trivial
    · exact RankMerge.program_readonly .halt point endPoint

theorem source_readonly (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (source point) := by
  cases point with
  | inl point =>
    change B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1)
      (if point=rootDone then .halt else LabelMap.statement coreMap (DFSDriver.source point))
    by_cases last : point=rootDone
    · rw [ite_eq_left last];trivial
    · rw [ite_eq_right last];exact readonly_label _ _ _ (core_readonly point)
  | inr point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun memory : (C×Ordering)×Bool×Bool => memory.1) (fun context : C×Ordering => context.1) _ (B23_6.DFSFrame.source_readonly point)

theorem program_source (finish : Statement C) (point : Label) (proper : point≠done) :
    program finish point=source point := by
  cases point with
  | inl point =>
    have outside : point≠rootDone := by intro same;subst point;exact proper rfl
    simp only [program,source,outside,ite_false]
  | inr point => rfl

def syntaxNodes {Λ σ : Type*} : TM2.Stmt Alphabet Λ σ → Nat
  | .push _ _ next | .pop _ _ next | .peek _ _ next | .load _ next => syntaxNodes next+1
  | .branch _ yes no => max (syntaxNodes yes) (syntaxNodes no)+1
  | .goto _ | .halt => 1

theorem syntax_nodes_count {Λ σ : Type*} (body : TM2.Stmt Alphabet Λ σ) (memory : σ) (slots : Stack → List Bool) :
    (AuxWorkspace.nodes body memory slots).length≤syntaxNodes body := by
  induction body generalizing memory slots with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih =>
    simp only [AuxWorkspace.nodes,List.length_cons,syntaxNodes];exact Nat.add_le_add_right (ih _ _) 1
  | branch test yes no yesIH noIH =>
    simp only [AuxWorkspace.nodes,syntaxNodes]
    cases choice : test memory
    · simp only [Bool.false_eq_true,ite_false,List.length_cons]
      exact Nat.add_le_add_right ((noIH _ _).trans (Nat.le_max_right _ _)) 1
    · simp only [ite_true,List.length_cons]
      exact Nat.add_le_add_right ((yesIH _ _).trans (Nat.le_max_left _ _)) 1
  | goto _ | halt => exact Nat.le_refl _

/-- Finite syntax profiles are constants of the one source, independent of runtime data or DFS visits. -/
def pushProfile (C : Type*) : Nat := 1+∑ point : Label,AuxWorkspace.pushes (source (C:=C) point)
def actionProfile (C : Type*) : Nat := 1+∑ point : Label,ScannerClock.actions (source (C:=C) point)
def nodeProfile (C : Type*) : Nat := 1+∑ point : Label,syntaxNodes (source (C:=C) point)

theorem pushes_le (finish : Statement C) (point : Label) (proper : point≠done) :
    AuxWorkspace.pushes (program finish point)≤pushProfile C := by
  rw [program_source finish point proper]
  exact (Finset.single_le_sum (fun other _ => Nat.zero_le (AuxWorkspace.pushes (source (C:=C) other))) (Finset.mem_univ point)).trans (Nat.le_add_left _ 1)
theorem actions_le (finish : Statement C) (point : Label) (proper : point≠done) :
    ScannerClock.actions (program finish point)≤actionProfile C := by
  rw [program_source finish point proper]
  exact (Finset.single_le_sum (fun other _ => Nat.zero_le (ScannerClock.actions (source (C:=C) other))) (Finset.mem_univ point)).trans (Nat.le_add_left _ 1)
theorem nodes_le (finish : Statement C) (point : Label) (proper : point≠done) :
    syntaxNodes (program finish point)≤nodeProfile C := by
  rw [program_source finish point proper]
  exact (Finset.single_le_sum (fun other _ => Nat.zero_le (syntaxNodes (source (C:=C) other))) (Finset.mem_univ point)).trans (Nat.le_add_left _ 1)

theorem step_resources (finish : Statement C) (before after : State C) (bound : Nat)
    (proper : before.l≠some done) (edge : TM2.step (program finish) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    after.var.1=before.var.1 ∧ ∀ slot,(after.stk slot).length≤bound+pushProfile C := by
  cases before with
  | mk position memory slots =>
    cases position with
    | none => cases edge
    | some point =>
      have interior : point≠done := by intro same;subst point;exact proper rfl
      have same : after=TM2.stepAux (program finish point) memory slots := (Option.some.inj edge).symm
      subst after
      have readonly:=source_readonly (C:=C) point
      rw [←program_source finish point interior] at readonly
      refine ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly _ _ readonly memory slots _ (AuxWorkspace.endpoint_mem _ _ _),?_⟩
      intro slot
      exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans (Nat.add_le_add_left (pushes_le finish point interior) bound)

end RootB236.Controller.DFSDriver.Machine
