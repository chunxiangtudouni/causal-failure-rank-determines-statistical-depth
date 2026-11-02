module

public import B23_4_RatWordPrep_SeqCmp_RawCode_021

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawGetter

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

def Readonly {σ Λ : Type*} (project : σ → C) : TM2.Stmt RatInput.Alphabet Λ σ → Prop
  | .push _ _ tail => Readonly project tail
  | .peek _ update tail | .pop _ update tail =>
    (∀ memory value,project (update memory value)=project memory) ∧ Readonly project tail
  | .load update tail => (∀ memory,project (update memory)=project memory) ∧ Readonly project tail
  | .branch _ yes no => Readonly project yes ∧ Readonly project no
  | .goto _ | .halt => True

theorem nodes_readonly {σ Λ : Type*} (project : σ → C) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (good : Readonly project body) (memory : σ) (contents : RatInput.Stack → List Bool) :
    ∀ node∈AuxWorkspace.nodes body memory contents,project node.1=project memory := by
  induction body generalizing memory contents with
  | push slot value tail ih =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · rfl
    · exact ih good _ _ node later
  | peek slot update tail ih | pop slot update tail ih =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · rfl
    · exact (ih good.2 _ _ node later).trans (good.1 memory _)
  | load update tail ih =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · rfl
    · exact (ih good.2 _ _ node later).trans (good.1 memory)
  | branch test yes no ihYes ihNo =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · rfl
    · cases selected : test memory
      · exact ihNo good.2 memory contents node (by simpa only [selected,Bool.false_eq_true,ite_false] using later)
      · exact ihYes good.1 memory contents node (by simpa only [selected,ite_true] using later)
  | goto target | halt =>
    intro node member
    have same := List.mem_singleton.mp member
    subst node
    rfl

theorem program_readonly (point : Label) : Readonly (fun memory : Store C => memory.1.1) (program .halt point) := by
  cases point with
  | boot =>
    dsimp [program,Readonly,bootMemory]
    exact ⟨fun _ => rfl,trivial⟩
  | done => trivial
  | parse point =>
    fin_cases point
    all_goals
      dsimp [program,parserProgram,parserSource,parserIso,VirtualReturn.program,VirtualReturn.statement,
        VirtualReturn.core,LabelMap.statement,StoreIso.statement,StoreIso.exchange,VirtualBool.source,
        BoolOnStacks.program,ContextLift.statement,Readonly]
      repeat' constructor
      all_goals (intros; rfl)
  | extract point =>
    fin_cases point
    all_goals
      dsimp [program,LabelMap.statement,PSTRSymbolicRatExport.ratProgram,PSTRSymbolicRatExport.fieldBody,
        PSTRSymbolicNaturalExport.program,Readonly]
      repeat' constructor
      all_goals (intros; rfl)

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    after.var.1.1=before.var.1.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact nodes_readonly (fun v : Store C => v.1.1) _ (program_readonly point) memory contents
        _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,current.var.1.1=before.var.1.1 := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)

end B23_4_RatWordPrep.RawGetter
