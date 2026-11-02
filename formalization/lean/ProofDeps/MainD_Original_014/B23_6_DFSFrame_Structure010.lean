module
public import B23_6_DFSFrame_Path002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

theorem source_actions (point : Label) : ScannerClock.actions (source (C:=C) point)≤4 := by
  cases point
  case popDone kind => cases kind <;> exact of_decide_eq_true rfl
  all_goals
    simp only [source,program,clearBody_literal,reverseBody_literal,keepSeed]
    (try split_ifs) <;> exact of_decide_eq_true rfl
theorem source_pushes (point : Label) : AuxWorkspace.pushes (source (C:=C) point)≤3 := by
  cases point
  case popDone kind => cases kind <;> exact of_decide_eq_true rfl
  all_goals
    simp only [source,program,clearBody_literal,reverseBody_literal,keepSeed]
    (try split_ifs) <;> exact of_decide_eq_true rfl
theorem source_readonly (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (source point) := by
  cases point
  case popDone kind => cases kind <;> trivial
  all_goals
    simp only [source,program,clearBody_literal,reverseBody_literal,keepSeed]
    try split_ifs
    dsimp [B23_4_RatWordPrep.RawGetter.Readonly,RatDrop.capture,clean]
    repeat' constructor
    all_goals (intros;rfl)

theorem program_interior (pushCaller goodCaller badCaller : Statement C) (point : Label) (proper : Interior point) :
    program pushCaller goodCaller badCaller point=source point := by
  cases point
  case popDone kind => cases kind <;> simp_all [Interior]
  case pushDone => exact False.elim (proper.1 rfl)
  all_goals rfl

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step source before=some after) (bounded : ∀ slot,(before.stk slot).length≤bound) :
    after.var.1=before.var.1 ∧ ∀ slot,(after.stk slot).length≤bound+3 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (source point) memory contents:=(Option.some.inj edge).symm
      subst after
      refine ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (source_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _),?_⟩
      intro slot
      exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (source_pushes point) bound)

theorem trace_resources (path : List (State C)) (before : State C) (bound : Nat)
    (first : path.head?=some before) (chain : path.IsChain (fun a b => TM2.step source a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ current∈path,current.var.1=before.var.1 ∧ ∀ slot,(current.stk slot).length≤bound+3*path.length := by
  induction path generalizing before bound with
  | nil => simp
  | cons start rest ih =>
    have same : start=before:=Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have equal:=List.mem_singleton.mp member
      subst current
      exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _)⟩
    | cons next rest =>
      obtain ⟨edge,later⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _)⟩
      · have tail:=ih next (bound+3) rfl later step.2 current member
        refine ⟨tail.1.trans step.1,?_⟩
        intro slot
        have h:=tail.2 slot
        simp only [List.length_cons] at h ⊢
        omega

end B23_6.DFSFrame
