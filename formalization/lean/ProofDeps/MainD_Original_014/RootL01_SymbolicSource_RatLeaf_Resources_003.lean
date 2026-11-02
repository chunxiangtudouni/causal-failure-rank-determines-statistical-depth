module

public import RootL01_SymbolicSource_RatLeaf_Run_002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.RatLeaf

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation

variable {C : Type*}

abbrev Work := RatInput.Encoder.Work

local instance (body : Statement C) : Decidable (StackIso.WritesOnly Work body) :=
  RatInput.Encoder.writesDecidable body

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point) ≤ 15 := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | reverseNum => exact of_decide_eq_true rfl
  | reverseDen => exact of_decide_eq_true rfl
  | den point => fin_cases point <;> exact of_decide_eq_true rfl
  | num point => fin_cases point <;> exact of_decide_eq_true rfl
  | finish => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point) ≤ 15 := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | reverseNum => exact of_decide_eq_true rfl
  | reverseDen => exact of_decide_eq_true rfl
  | den point => fin_cases point <;> exact of_decide_eq_true rfl
  | num point => fin_cases point <;> exact of_decide_eq_true rfl
  | finish => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | reverseNum => exact of_decide_eq_true rfl
  | reverseDen => exact of_decide_eq_true rfl
  | den point => fin_cases point <;> exact of_decide_eq_true rfl
  | num point => fin_cases point <;> exact of_decide_eq_true rfl
  | finish => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

def Readonly {σ Λ : Type*} (project : σ → C) : TM2.Stmt RatInput.Alphabet Λ σ → Prop
  | .push _ _ tail => Readonly project tail
  | .peek _ update tail | .pop _ update tail =>
    (∀ memory value,project (update memory value) = project memory) ∧ Readonly project tail
  | .load update tail => (∀ memory,project (update memory) = project memory) ∧ Readonly project tail
  | .branch _ yes no => Readonly project yes ∧ Readonly project no
  | .goto _ | .halt => True

theorem nodes_readonly {σ Λ : Type*} (project : σ → C) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (good : Readonly project body) (memory : σ) (contents : Bank) :
    ∀ node ∈ AuxWorkspace.nodes body memory contents,project node.1 = project memory := by
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

theorem program_readonly (point : Label) :
    Readonly (fun memory : Store C => memory.1.1) (program .halt point) := by
  cases point with
  | collect point =>
    fin_cases point
    all_goals
      dsimp [program,Readonly,collectLabel,LabelMap.statement,StoreIso.statement,exchange,
        RatInput.Encoder.exchange,StoreIso.exchange,RatInput.program,RatInput.fieldBody,
        RatInput.restoreBody,StackIso.statement,PSTRSymbolicNaturalExport.program,
        PSTRSymbolicRatExport.restoreLabel]
      repeat' constructor
      all_goals (intros; rfl)
  | reverseNum | reverseDen =>
    dsimp [program,Readonly,LabelMap.statement,StackIso.statement,RatOutput.program,RatOutput.jump]
    repeat' constructor
    all_goals (intros; rfl)
  | den point | num point =>
    fin_cases point
    all_goals
      dsimp [program,Readonly,LabelMap.statement,StackIso.statement,WordNatIO.callerProgram,
        ContextLift.statement,WordNatIO.program]
      repeat' constructor
      all_goals (intros; rfl)
  | finish =>
    dsimp [program,finishBody,leafPrefix,encodeDatum,encodeNat,natBits,Readonly,
      RatInput.Encoder.putPrefix]
    trivial
  | done => trivial

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before = some after) :
    after.var.1.1 = before.var.1.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after = TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact nodes_readonly (fun value : Store C => value.1.1) _ (program_readonly point)
        memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before = some after)
    (bounded : ∀ slot,(before.stk slot).length ≤ bound) :
    (∀ slot,(after.stk slot).length ≤ bound+15) ∧
      ∀ slot,¬Work slot → after.stk slot = before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after = TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame Work _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C) (background : Bank) (bound : Nat)
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a = some b))
    (bounded : ∀ slot,(before.stk slot).length ≤ bound)
    (frames : ∀ slot,¬Work slot → before.stk slot = background slot) :
    ∀ current ∈ trace,
      current.var.1.1 = before.var.1.1 ∧
      (∀ slot,(current.stk slot).length ≤ bound+15*trace.length) ∧
      ∀ slot,¬Work slot → current.stk slot = background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons start rest ih =>
    have equal : start = before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact ⟨rfl,fun slot => (bounded slot).trans (by simp),frames⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have step := step_resources before next bound edge bounded
      have nextFrames : ∀ slot,¬Work slot → next.stk slot = background slot :=
        fun slot untouched => (step.2 slot untouched).trans (frames slot untouched)
      intro current member
      rcases List.mem_cons.mp member with same | later
      · subst current
        exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _),frames⟩
      · have tail := ih next (bound+15) rfl tailChain step.1 nextFrames current later
        refine ⟨tail.1.trans (step_context before next edge),?_,tail.2.2⟩
        intro slot
        have perSlot := tail.2.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (program .halt point) current.var current.stk,
      node.1.1.1 = current.var.1.1 ∧
      (∀ slot,(node.2 slot).length ≤ bound+15) ∧
      ∀ slot,¬Work slot → node.2 slot = current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 30*(bound+16) := by
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨nodes_readonly _ _ (program_readonly point) _ _ node member,?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound)
    · intro slot untouched
      exact StackIso.nodes_frame Work _ (program_writes point) current.var current.stk slot untouched node member
  · have clock := ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
      (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

def time (p : Rat) : Nat := 8*RatInput.Encoder.fieldSize p+35

def scale (background : Bank) (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (p : Rat) (tail scratch output : List Bool) : Nat :=
  RatInput.occupied (entry background context memory formatter p tail scratch output).stk+15*time p

structure Facts (background : Bank) (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (p : Rat) (tail scratch output : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head? = some (entry background context memory formatter p tail scratch output)
  chain : trace.IsChain (fun a b => TM2.step (program .halt) a = some b)
  last : trace.getLast? = some final
  active : final.l = some .done
  context_eq : final.var.1.1 = context
  contents : final.stk = bank background (RatInput.Encoder.packet p tail) scratch [] [] [] []
    (leafBits p ++ output) [] []
  count : trace.length ≤ time p
  boundaries : ∀ current ∈ trace,current.var.1.1 = context ∧
    (∀ slot,(current.stk slot).length ≤ scale background context memory formatter p tail scratch output) ∧
    RatInput.occupied current.stk ≤ 16*scale background context memory formatter p tail scratch output ∧
    ∀ slot,¬Work slot → current.stk slot = background slot
  proper : ∀ current ∈ trace.dropLast,current.l ≠ some .done ∧
    ∀ point,current.l = some point →
      (∀ node ∈ AuxWorkspace.nodes (program .halt point) current.var current.stk,
        node.1.1.1 = context ∧
        RatInput.occupied node.2 ≤ 16*(scale background context memory formatter p tail scratch output+15) ∧
        ∀ slot,¬Work slot → node.2 slot = background slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤
        30*(scale background context memory formatter p tail scratch output+16)

theorem actual_bounded (background : Bank) (context : C) (memory : RatInput.Store)
    (formatter : WordNatIO.Store) (p : Rat) (tail scratch output : List Bool) :
    ∃ (trace : List (State C)) (final : State C),Facts background context memory formatter p tail scratch output trace final := by
  obtain ⟨trace,final,first,chain,last,active,contextFinal,contentsFinal,count⟩ :=
    actual_rational_leaf .halt background context memory formatter p tail scratch output
  let before := entry background context memory formatter p tail scratch output
  have frames : ∀ slot,¬Work slot → before.stk slot = background slot :=
    fun slot untouched => RatInput.Encoder.bank_frame _ _ _ _ _ _ _ _ _ _ slot untouched
  have resources := trace_resources trace before background (RatInput.occupied before.stk) first chain
    (RatInput.Encoder.point_mass before.stk) frames
  have grow : RatInput.occupied before.stk+15*trace.length ≤
      scale background context memory formatter p tail scratch output :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 15 count) _
  have perSlot : ∀ current ∈ trace,∀ slot,(current.stk slot).length ≤
      scale background context memory formatter p tail scratch output :=
    fun current member slot => ((resources current member).2.1 slot).trans grow
  refine ⟨trace,final,{
    first := first,chain := chain,last := last,active := active,context_eq := contextFinal,
    contents := contentsFinal,count := count,boundaries := ?_,proper := ?_ }⟩
  · intro current member
    exact ⟨(resources current member).1,perSlot current member,
      RatInput.Encoder.occupied_bound current.stk _ (perSlot current member),(resources current member).2.2⟩
  · have proper := NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last active
    intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have bound := internal_resources current point _ (perSlot current (List.mem_of_mem_dropLast member))
    refine ⟨?_,bound.2⟩
    intro node nodeMember
    have cap := bound.1 node nodeMember
    exact ⟨cap.1.trans ((resources current (List.mem_of_mem_dropLast member)).1),
      RatInput.Encoder.occupied_bound node.2 _ cap.2.1,
      fun slot untouched => (cap.2.2 slot untouched).trans
        ((resources current (List.mem_of_mem_dropLast member)).2.2 slot untouched)⟩

end RootL01.SymbolicSource.RatLeaf
