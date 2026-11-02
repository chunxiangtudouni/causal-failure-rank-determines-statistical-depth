module
public import RootB236_Controller_DFSDriver_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
def state (point : Label) (memory : Store C) (slots : Stack → List Bool) : State C := ⟨some point,memory,slots⟩
def Inside (current : State C) : Prop := ∀ point,current.l=some point → ¬Boundary point
/-- Actual steps only. The ACTIVE done body is never executed inside this path. -/
inductive Path (good bad pop finish : Statement C) : State C → State C → Nat → Prop where
  | refl {current} : Path good bad pop finish current current 0
  | step {before after final steps} (proper : Inside before)
      (edge : TM2.step (program good bad pop finish) before=some after) (later : Path good bad pop finish after final steps) :
      Path good bad pop finish before final (steps+1)
theorem Path.trans {good bad pop finish : Statement C} {before middle final : State C} {early later : Nat}
    (first : Path good bad pop finish before middle early) (last : Path good bad pop finish middle final later) :
    Path good bad pop finish before final (early+later) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using last
  | step proper edge _ ih => simpa only [Nat.add_right_comm] using Path.step proper edge (ih last)
theorem Path.actual {good bad pop finish : Statement C} {before final : State C} {steps : Nat}
    (path : Path good bad pop finish before final steps) :
    ∃ trace : List (State C),trace.head?=some before ∧
      trace.IsChain (fun x y => TM2.step (program good bad pop finish) x=some y) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧
      ∀ current∈trace.dropLast,Inside current := by
  induction path with
  | refl => exact ⟨[_],rfl,List.isChain_singleton _,rfl,rfl,by simp⟩
  | @step before after final steps proper edge _ ih =>
    obtain ⟨trace,first,chain,last,length,interior⟩:=ih
    obtain ⟨tail,rfl⟩:=List.head?_eq_some_iff.mp first
    refine ⟨before::after::tail,rfl,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_,?_⟩
    · change (after::tail).getLast?=some final;exact last
    · simp only [List.length_cons] at length ⊢;omega
    · intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact proper
      · exact interior current later
/-- Transport the same legacy chain; no stopped configuration is reset for free. -/
theorem Path.of_mapped {A : Type*} (good bad pop finish : Statement C) (mapping : A → State C)
    (relation : A → A → Prop) (trace : List A) (before final : A)
    (first : trace.head?=some before) (chain : trace.IsChain relation) (last : trace.getLast?=some final)
    (edges : ∀ current∈trace.dropLast,∀ next,relation current next →
      TM2.step (program good bad pop finish) (mapping current)=some (mapping next))
    (proper : ∀ current∈trace.dropLast,Inside (mapping current)) :
    Path good bad pop finish (mapping before) (mapping final) (trace.length-1) := by
  induction trace generalizing before with
  | nil => cases first
  | cons head tail ih =>
    have same : head=before := Option.some.inj first
    subst head
    cases tail with
    | nil =>
      have same : before=final := Option.some.inj last
      subst final;exact Path.refl
    | cons next rest =>
      obtain ⟨edge,laterChain⟩:=List.isChain_cons_cons.mp chain
      have later:=ih next rfl laterChain (by exact last)
        (by intro current member other related
            exact edges current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member) other related)
        (by intro current member
            exact proper current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member))
      have now:=Path.step (proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self))
        (edges before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self) next edge) later
      simpa only [List.length_cons,Nat.add_sub_cancel] using now

theorem control_not_boundary (point : Fin 22) (small : point.val<14 ∨ 17<point.val) : ¬Boundary (.control point) := by
  intro boundary
  rcases boundary with h | h | h | h
  all_goals have same : point.val=_ := congrArg Fin.val (Label.control.inj h)
  all_goals rcases small with small | large <;> norm_num at same <;> omega

theorem inside_control (point : Fin 22) (memory : Store C) (slots : Stack → List Bool)
    (small : point.val<14 ∨ 17<point.val) : Inside (state (.control point) memory slots) := by
  intro selected active
  have same : .control point=selected := Option.some.inj active
  subst selected;exact control_not_boundary point small

def clearPoint (phase : Fin 10) : Label := .control ⟨phase.val,by have bound:=phase.isLt;omega⟩
def nextClear (phase : Fin 10) : Label := .control ⟨phase.val+1,by have bound:=phase.isLt;omega⟩
theorem clear_code (good bad pop finish : Statement C) (phase : Fin 10) :
    program good bad pop finish (clearPoint phase)=
      .pop (clearSlot phase) BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
        (.goto (fun _ => clearPoint phase)) (.goto (fun _ => nextClear phase))) := by
  simp only [clearPoint,nextClear,program,show phase.val<10 from phase.isLt,dite_true]

theorem clear_bit (good bad pop finish : Statement C) (phase : Fin 10) (slots : Stack → List Bool)
    (memory : Store C) (value : Bool) (tail : List Bool) (present : slots (clearSlot phase)=value::tail) :
    TM2.step (program good bad pop finish) (state (clearPoint phase) memory slots)=
      some (state (clearPoint phase) (memory.1,true,memory.2.2.1,memory.2.2.2)
        (Function.update slots (clearSlot phase) tail)) := by
  change some (TM2.stepAux (program good bad pop finish (clearPoint phase)) memory slots)=_
  rw [clear_code]
  simp only [TM2.stepAux,present,BestUpdate.capturePresent,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,state]
theorem clear_empty (good bad pop finish : Statement C) (phase : Fin 10) (slots : Stack → List Bool)
    (memory : Store C) (empty : slots (clearSlot phase)=[]) :
    TM2.step (program good bad pop finish) (state (clearPoint phase) memory slots)=
      some (state (nextClear phase) (memory.1,false,memory.2.2.1,memory.2.2.2)
        (Function.update slots (clearSlot phase) [])) := by
  change some (TM2.stepAux (program good bad pop finish (clearPoint phase)) memory slots)=_
  rw [clear_code]
  simp only [TM2.stepAux,empty,BestUpdate.capturePresent,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,state]
theorem update_twice (slots : Stack → List Bool) (slot : Stack) (first last : List Bool) :
    Function.update (Function.update slots slot first) slot last=Function.update slots slot last := by
  funext other
  by_cases same : other=slot
  · subst other;simp only [Function.update_self]
  · simp only [Function.update_of_ne same]

theorem clear_path (good bad pop finish : Statement C) (phase : Fin 10) (slots : Stack → List Bool)
    (memory : Store C) (data : List Bool) (represented : slots (clearSlot phase)=data) :
    Path good bad pop finish (state (clearPoint phase) memory slots)
      (state (nextClear phase) (memory.1,false,memory.2.2.1,memory.2.2.2)
        (Function.update slots (clearSlot phase) [])) (data.length+1) := by
  induction data generalizing slots memory with
  | nil =>
    exact Path.step (inside_control _ memory slots (Or.inl (by have bound:=phase.isLt;exact Nat.lt_trans bound (by decide))))
      (clear_empty good bad pop finish phase slots memory represented) .refl
  | cons value tail ih =>
    have later:=ih (Function.update slots (clearSlot phase) tail)
      (memory.1,true,memory.2.2.1,memory.2.2.2) (by simp only [Function.update_self])
    rw [update_twice] at later
    exact Path.step (inside_control _ memory slots (Or.inl (by have bound:=phase.isLt;exact Nat.lt_trans bound (by decide))))
      (clear_bit good bad pop finish phase slots memory value tail represented) later

/-- Canonical staged-data mask stream; TRUE row markers keep q=0 live rows distinct from EOF. -/
def rows (q : Nat) (stages : List (Finset (Fin q))) : List Bool :=
  stages.flatMap (fun eligible => true::EraseSem.mask eligible)
theorem rows_cons (q : Nat) (eligible : Finset (Fin q)) (later : List (Finset (Fin q))) :
    rows q (eligible::later)=true::(EraseSem.mask eligible++rows q later) := rfl
theorem rows_length (q : Nat) (stages : List (Finset (Fin q))) : (rows q stages).length=(q+1)*stages.length := by
  induction stages with
  | nil => rfl
  | cons eligible later ih =>
    simp only [rows_cons,List.length_cons,List.length_append,EraseSem.mask_length,ih,Nat.mul_succ]
    omega

theorem rows_empty_iff (q : Nat) (stages : List (Finset (Fin q))) : rows q stages=[] ↔ stages=[] := by
  cases stages
  · simp [rows]
  · simp only [rows_cons,reduceCtorEq]
end RootB236.Controller.DFSDriver
