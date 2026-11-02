module
public import RootB234_Cells_Resources_002

/-! Ordinary finite-store API, four literal stack instances, and static
caller linking. No runtime datum chooses source code, support, or labels. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.Cells
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

namespace Public
def clear0 : Label → Statement C := program .clear0 .halt
def clear1 : Label → Statement C := program .clear1 .halt
def reverse13To3 : Label → Statement C := program .reverse13To3 .halt
def reverse3To2 : Label → Statement C := program .reverse3To2 .halt

theorem clear0_supports : TM2.Supports (clear0 (C:=C)) support := supports _ _
theorem clear1_supports : TM2.Supports (clear1 (C:=C)) support := supports _ _
theorem reverse13To3_supports : TM2.Supports (reverse13To3 (C:=C)) support := supports _ _
theorem reverse3To2_supports : TM2.Supports (reverse3To2 (C:=C)) support := supports _ _
theorem finite_store [Finite C] : Finite (Store C) := inferInstance

theorem clear0_output (before : Stack → List Bool) : output .clear0 before=Function.update before 0 [] := rfl
theorem clear1_output (before : Stack → List Bool) : output .clear1 before=Function.update before 1 [] := rfl
theorem reverse13To3_output (before : Stack → List Bool) :
    output .reverse13To3 before=Function.update (Function.update before 13 []) 3 ((before 13).reverse++before 3) := rfl
theorem reverse3To2_output (before : Stack → List Bool) :
    output .reverse3To2 before=Function.update (Function.update before 3 []) 2 ((before 3).reverse++before 2) := rfl

theorem clear0_work (slot : Stack) : Work .clear0 slot↔slot=0 := by
  change (slot=0 ∨ false=true ∧ slot=2)↔slot=0
  simp only [Bool.false_eq_true,false_and,or_false]
theorem clear1_work (slot : Stack) : Work .clear1 slot↔slot=1 := by
  change (slot=1 ∨ false=true ∧ slot=2)↔slot=1
  simp only [Bool.false_eq_true,false_and,or_false]
theorem reverse13To3_work (slot : Stack) : Work .reverse13To3 slot↔slot=13 ∨ slot=3 := by
  change (slot=13 ∨ true=true ∧ slot=3)↔_
  simp only [true_and]
theorem reverse3To2_work (slot : Stack) : Work .reverse3To2 slot↔slot=3 ∨ slot=2 := by
  change (slot=3 ∨ true=true ∧ slot=2)↔_
  simp only [true_and]

theorem clear0_cells (before : Stack → List Bool) : (output .clear0 before) 0=[] := rfl
theorem clear1_cells (before : Stack → List Bool) : (output .clear1 before) 1=[] := rfl
theorem reverse13To3_cells (before : Stack → List Bool) :
    (output .reverse13To3 before) 13=[] ∧ (output .reverse13To3 before) 3=(before 13).reverse++before 3 := ⟨rfl,rfl⟩
theorem reverse3To2_cells (before : Stack → List Bool) :
    (output .reverse3To2 before) 3=[] ∧ (output .reverse3To2 before) 2=(before 3).reverse++before 2 := ⟨rfl,rfl⟩

theorem ports :
    entry .clear0=0 ∧ returnPort .clear0=6 ∧ entry .clear1=0 ∧ returnPort .clear1=6 ∧
    entry .reverse13To3=3 ∧ returnPort .reverse13To3=4 ∧ entry .reverse3To2=3 ∧ returnPort .reverse3To2=4 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual (op : Operation) (memory : Store C) (before : Stack → List Bool) :
    ∃ path,Facts op memory before path ∧ clockSum op path≤40*(scale before)^2 ∧
      chargedCost op path≤42*(scale before)^2 := by
  have facts:=actual_bounded op memory before
  exact ⟨trace op memory before,facts,clockSum_le facts,chargedCost_le facts⟩

theorem clear0_actual (memory : Store C) (before : Stack → List Bool) :
    ∃ path,Facts .clear0 memory before path ∧ clockSum .clear0 path≤40*(scale before)^2 ∧
      chargedCost .clear0 path≤42*(scale before)^2 := actual _ _ _
theorem clear1_actual (memory : Store C) (before : Stack → List Bool) :
    ∃ path,Facts .clear1 memory before path ∧ clockSum .clear1 path≤40*(scale before)^2 ∧
      chargedCost .clear1 path≤42*(scale before)^2 := actual _ _ _
theorem reverse13To3_actual (memory : Store C) (before : Stack → List Bool) :
    ∃ path,Facts .reverse13To3 memory before path ∧ clockSum .reverse13To3 path≤40*(scale before)^2 ∧
      chargedCost .reverse13To3 path≤42*(scale before)^2 := actual _ _ _
theorem reverse3To2_actual (memory : Store C) (before : Stack → List Bool) :
    ∃ path,Facts .reverse3To2 memory before path ∧ clockSum .reverse3To2 path≤40*(scale before)^2 ∧
      chargedCost .reverse3To2 path≤42*(scale before)^2 := actual _ _ _

theorem fixed_source (C : Type*) [Fintype C] (op : Operation) :
    ∃ (code : Label → Statement C) (allowed : Finset Label),
      code=program op .halt ∧ TM2.Supports code allowed ∧
      Fintype.card (Store C)=Fintype.card C*4 ∧
      ∀ (memory : Store C) (before : Stack → List Bool),
        ∃ path,Facts op memory before path ∧ clockSum op path≤40*(scale before)^2 ∧
          chargedCost op path≤42*(scale before)^2 := by
  refine ⟨program op .halt,support,rfl,supports op .halt,?_,actual op⟩
  change Fintype.card (C×Bool×Bool)=Fintype.card C*4
  simp only [Fintype.card_prod,Fintype.card_bool]

/-- Existing active machine state, arbitrary flags and all sixteen stacks. -/
theorem from_state (op : Operation) (before : State C) (active : before.l=some (entry op)) :
    Facts op before.var before.stk (trace op before.var before.stk) ∧
      (trace op before.var before.stk).head?=some before ∧
      clockSum op (trace op before.var before.stk)≤40*(RatInput.occupied before.stk+1)^2 ∧
      chargedCost op (trace op before.var before.stk)≤42*(RatInput.occupied before.stk+1)^2 := by
  cases before with
  | mk position memory contents =>
    have equal : position=some (entry op):=active
    subst position
    have facts:=actual_bounded op memory contents
    exact ⟨facts,facts.first,clockSum_le facts,chargedCost_le facts⟩

theorem from_default (op : Operation) (before : Stack → List Bool) :
    ∃ path,Facts op (default : Store Unit) before path ∧ clockSum op path≤40*(scale before)^2 ∧
      chargedCost op path≤42*(scale before)^2 := actual _ _ _

/-- Label renaming changes no physical read, internal snapshot or clock. -/
theorem clock_labelMap {Ω : Type*} (mapping : Label → Ω) (statement : Statement C)
    (memory : Store C) (before : Stack → List Bool) :
    ScannerStatement.clock (LabelMap.statement mapping statement) memory before=
      ScannerStatement.clock statement memory before := by
  induction statement generalizing memory before with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih =>
    simp only [LabelMap.statement,ScannerStatement.clock,ih]
  | load value _ ih => exact ih (value memory) before
  | branch test _ _ yes no =>
    cases choice : test memory <;>
      simp only [LabelMap.statement,ScannerStatement.clock,choice,Bool.false_eq_true,ite_false,ite_true,yes,no]
  | goto _ | halt => rfl

def callerClock {Ω : Type*} (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (current : TM2.Cfg RatInput.Alphabet Ω (Store C)) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (code point) current.var current.stk
def callerClockSum {Ω : Type*} (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (path : List (TM2.Cfg RatInput.Alphabet Ω (Store C))) : Nat := (path.dropLast.map (callerClock code)).sum

theorem caller_body_supported {Ω : Type*} (op : Operation) (mapping : Label → Ω)
    (allowed : Finset Ω) (maps : ∀ point∈support,mapping point∈allowed) :
    TM2.SupportsStmt allowed (LabelMap.statement mapping (body (C:=C) op)) := by
  apply LabelMap.statement_supports mapping (body op) support allowed _ maps
  simpa only [program,ite_true] using (supports op (.halt : Statement C)).2 (entry op) (Finset.mem_univ _)

/-- A caller need only install the literal finite body at its fixed entry.
The return label is an ACTIVE endpoint and its body has not been executed. -/
theorem caller_chain {Ω : Type*} (op : Operation) (memory : Store C) (before : Stack → List Bool)
    (mapping : Label → Ω) (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (atEntry : code (mapping (entry op))=LabelMap.statement mapping (body op)) :
    ((trace op memory before).map (LabelMap.configuration mapping)).IsChain
      (fun a b => TM2.step code a=some b) := by
  apply LabelMap.chain_configuration_on mapping (program op .halt) code _ (trace_chain op .halt memory before)
  intro current member point selected
  have equal : point=entry op:=Option.some.inj (selected.symm.trans (trace_proper op memory before current member))
  subst point
  simpa only [program,ite_true] using atEntry

theorem caller_clock_sum {Ω : Type*} (op : Operation) (memory : Store C) (before : Stack → List Bool)
    (mapping : Label → Ω) (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (atEntry : code (mapping (entry op))=LabelMap.statement mapping (body op)) :
    callerClockSum code ((trace op memory before).map (LabelMap.configuration mapping))=
      clockSum op (trace op memory before) := by
  unfold callerClockSum clockSum
  rw [←List.map_dropLast,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro current member
  have active:=trace_proper op memory before current member
  change (match current.l.map mapping with
    | none => 0
    | some point => ScannerStatement.clock (code point) current.var current.stk)=statementClock op current
  simp only [statementClock,active,Option.map_some]
  change ScannerStatement.clock (code (mapping (entry op))) current.var current.stk=
    ScannerStatement.clock (program op .halt (entry op)) current.var current.stk
  rw [atEntry,clock_labelMap]
  simp only [program,ite_true]

theorem caller_internal {Ω : Type*} (op : Operation) (memory : Store C) (before : Stack → List Bool)
    (mapping : Label → Ω) (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (atEntry : code (mapping (entry op))=LabelMap.statement mapping (body op)) :
    ∀ current∈(trace op memory before).dropLast,
      (∀ node∈AuxWorkspace.nodes (code (mapping (entry op))) current.var current.stk,
        node.1.1=memory.1 ∧ (∀ slot,(node.2 slot).length≤4*scale before) ∧
        RatInput.occupied node.2≤64*scale before ∧ ∀ slot,¬Work op slot→node.2 slot=before slot) ∧
      ScannerStatement.clock (code (mapping (entry op))) current.var current.stk≤20*scale before := by
  intro current member
  have facts:=actual_bounded op memory before
  have bounds:=(facts.proper current member).2 (entry op) (trace_proper op memory before current member)
  rw [atEntry,LabelMap.nodes_statement,clock_labelMap]
  simpa only [program,ite_true] using bounds

theorem caller_actual {Ω : Type*} (op : Operation) (memory : Store C) (before : Stack → List Bool)
    (mapping : Label → Ω) (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (atEntry : code (mapping (entry op))=LabelMap.statement mapping (body op)) :
    ∃ path : List (TM2.Cfg RatInput.Alphabet Ω (Store C)),
      path.head?=some (LabelMap.configuration mapping (initial op memory before)) ∧
      path.IsChain (fun a b => TM2.step code a=some b) ∧
      path.getLast?=some (LabelMap.configuration mapping (result op memory.1 before)) ∧
      path.length=(before (source op)).length+2 ∧
      (∀ current∈path,current.var.1=memory.1 ∧
        (∀ slot,(current.stk slot).length≤3*scale before) ∧ RatInput.occupied current.stk≤48*scale before ∧
        ∀ slot,¬Work op slot→current.stk slot=before slot) ∧
      (∀ current∈path.dropLast,current.l=some (mapping (entry op)) ∧
        ∀ point,current.l=some point→
          (∀ node∈AuxWorkspace.nodes (code point) current.var current.stk,
            node.1.1=memory.1 ∧ (∀ slot,(node.2 slot).length≤4*scale before) ∧
            RatInput.occupied node.2≤64*scale before ∧ ∀ slot,¬Work op slot→node.2 slot=before slot) ∧
          ScannerStatement.clock (code point) current.var current.stk≤20*scale before) ∧
      callerClockSum code path≤40*(scale before)^2 ∧
      path.length+callerClockSum code path≤42*(scale before)^2 := by
  let path:=(trace op memory before).map (LabelMap.configuration mapping)
  have facts:=actual_bounded op memory before
  have clock:=caller_clock_sum op memory before mapping code atEntry
  refine ⟨path,?_,caller_chain op memory before mapping code atEntry,?_,?_,?_,?_,?_,?_⟩
  · rw [List.head?_map,facts.first,Option.map_some]
  · rw [List.getLast?_map,facts.last,Option.map_some]
  · rw [List.length_map,facts.count]
  · intro current member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    exact facts.boundaries old present
  · intro current member
    change current∈((trace op memory before).map (LabelMap.configuration mapping)).dropLast at member
    rw [←List.map_dropLast] at member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    have active:=LabelMap.configuration_active mapping old (entry op) (trace_proper op memory before old present)
    refine ⟨active,?_⟩
    intro point selected
    have equal : point=mapping (entry op):=Option.some.inj (selected.symm.trans active)
    subst point
    exact caller_internal op memory before mapping code atEntry old present
  · rw [clock]
    exact clockSum_le facts
  · rw [List.length_map,clock]
    exact chargedCost_le facts

end Public
end RootB234.Cells
