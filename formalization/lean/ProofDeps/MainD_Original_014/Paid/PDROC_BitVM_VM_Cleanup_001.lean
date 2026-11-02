module

public import Paid.PDROC_BitVM_Kernel_Clear_006
public import Paid.PDROC_BitVM_Native_Return_006
public import Paid.PDROC_BitVM_Common_IO_Paths_002
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.Cleanup

open Turing PDROC.BitVM.Native PDROC.BitVM.Common.IO
open PaperProofs.Common.Native.PSTRWordBool
open scoped BigOperators

abbrev Stack := Kernel.RegisterGlobal.Stack
abbrev Alphabet := Kernel.RegisterGlobal.Alphabet
abbrev Label := Fin 10
abbrev Store (Saved : Type*) := Option Bool × Saved
abbrev State (Saved : Type*) := TM2.Cfg Alphabet Label (Store Saved)

/-! Nine fixed physical work roles. Saved is caller finite control fixed
before input, never a Nat address, Cell, host heap or transition oracle.
The machine only instantiates the already checked genuine clear program. -/

def slot (stage : Fin 9) : Stack :=
  if stage.val = 0 then 0 else ⟨23 + stage.val, by omega⟩

def stageLabel (stage : Fin 9) : Label := ⟨stage.val, by omega⟩
def nextLabel (stage : Fin 9) : Label := ⟨stage.val + 1, by omega⟩
def labels (stage : Fin 9) (_ : Unit) : Label := stageLabel stage
def startLabel : Label := 0
def doneLabel : Label := 9

def program (Saved : Type*) (label : Label) : TM2.Stmt Alphabet Label (Store Saved) :=
  if inside : label.val < 9 then
    Inline.statement (τ := Saved) (labels ⟨label.val, inside⟩) (nextLabel ⟨label.val, inside⟩)
      (Kernel.Clear.program (slot ⟨label.val, inside⟩) ())
  else .halt

theorem agrees (Saved : Type*) (stage : Fin 9) : ∀ subLabel,
    program Saved (labels stage subLabel) =
      Inline.statement (τ := Saved) (labels stage) (nextLabel stage) (Kernel.Clear.program (slot stage) subLabel) := by
  intro subLabel
  cases subLabel
  simp only [labels, program, stageLabel, Fin.val_mk, stage.isLt, ↓reduceDIte]

theorem supports (Saved : Type*) : TM2.Supports (program Saved) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    by_cases inside : label.val < 9
    · simp only [program, inside, ↓reduceDIte]
      apply Inline.supports_statement _ _ (Finset.univ : Finset Unit) (Finset.univ : Finset Label)
      · intro subLabel _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact (Kernel.Clear.supports (slot ⟨label.val, inside⟩)).2 () (Finset.mem_univ _)
    · simp only [program, inside, ↓reduceDIte, TM2.SupportsStmt]

theorem pushes_zero (Saved : Type*) (label : Label) : AuxWorkspace.pushes (program Saved label) = 0 := by
  unfold program
  split <;> rfl

theorem sourcePushCap_zero (Saved : Type*) :
    PDROC.BitVM.Common.sourcePushCap (program Saved) (Finset.univ : Finset Label) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold PDROC.BitVM.Common.sourcePushCap
  exact Finset.sup_le fun label _ => (pushes_zero Saved label).le

def dataSize (contents : Stack → List Bool) := ∑ role : Stack, (contents role).length

theorem word_le_dataSize (contents : Stack → List Bool) (role : Stack) :
    (contents role).length ≤ dataSize contents := by
  change (contents role).length ≤ (Finset.univ : Finset Stack).sum (fun index => (contents index).length)
  exact Finset.single_le_sum (f := fun index : Stack => (contents index).length)
    (fun index _ => Nat.zero_le ((contents index).length)) (Finset.mem_univ role)

abbrev Cleared (count : ℕ) (role : Stack) : Prop :=
  (role.val = 0 ∧ 0 < count) ∨ (24 ≤ role.val ∧ role.val < 23 + count)

def clearedData (count : ℕ) (contents : Stack → List Bool) (role : Stack) : List Bool :=
  if Cleared count role then [] else contents role

abbrev isWork (role : Stack) : Prop := role.val = 0 ∨ 24 ≤ role.val
def cleaned (contents : Stack → List Bool) (role : Stack) : List Bool :=
  if isWork role then [] else contents role

theorem slot_val (stage : Fin 9) : (slot stage).val = if stage.val = 0 then 0 else 23 + stage.val := by
  unfold slot
  split <;> rfl

theorem clearedData_zero (contents : Stack → List Bool) : clearedData 0 contents = contents := by
  funext role
  have absent : ¬Cleared 0 role := by unfold Cleared; omega
  simp only [clearedData, absent, ↓reduceIte]

theorem clearedData_current (stage : Fin 9) (contents : Stack → List Bool) :
    clearedData stage.val contents (slot stage) = contents (slot stage) := by
  have absent : ¬Cleared stage.val (slot stage) := by
    simp only [Cleared, slot_val]
    split_ifs <;> omega
  simp only [clearedData, absent, ↓reduceIte]

theorem clearedData_step (stage : Fin 9) (contents : Stack → List Bool) :
    Function.update (clearedData stage.val contents) (slot stage) [] = clearedData (stage.val + 1) contents := by
  funext role
  by_cases here : role = slot stage
  · subst role
    rw [Function.update_self]
    have present : Cleared (stage.val + 1) (slot stage) := by
      simp only [Cleared, slot_val]
      split_ifs <;> omega
    simp only [clearedData, present, ↓reduceIte]
  · rw [Function.update_of_ne here]
    have different : role.val ≠ (slot stage).val := fun equal => here (Fin.ext equal)
    rw [slot_val] at different
    have equivalent : Cleared stage.val role ↔ Cleared (stage.val + 1) role := by
      unfold Cleared
      split_ifs at different <;> omega
    simp only [clearedData, equivalent]

theorem clearedData_nine (contents : Stack → List Bool) : clearedData 9 contents = cleaned contents := by
  funext role
  have bound := role.isLt
  have equivalent : Cleared 9 role ↔ isWork role := by unfold Cleared isWork; omega
  simp only [clearedData, cleaned, equivalent]

theorem cleaned_frame (contents : Stack → List Bool) (role : Stack)
    (safeRole : 1 ≤ role.val ∧ role.val < 24) : cleaned contents role = contents role := by
  have absent : ¬isWork role := by unfold isWork; omega
  simp only [cleaned, absent, ↓reduceIte]

theorem cleaned_work (contents : Stack → List Bool) (role : Stack) (work : isWork role) : cleaned contents role = [] := by
  simp only [cleaned, work, ↓reduceIte]

/-! ONE original Clear006 path is relabelled into its actual caller.
The final local HALT really becomes the next fixed stage's goto. -/
theorem stage_path (Saved : Type*) (stage : Fin 9) (contents : Stack → List Bool) (store : Store Saved) :
    ∃ path : ActualPath (TM2.step (program Saved))
      (⟨some (stageLabel stage), store, contents⟩ : State Saved)
      (⟨some (nextLabel stage), (none, store.2), Function.update contents (slot stage) []⟩ : State Saved),
      path.posts.length ≤ (contents (slot stage)).length + 2 := by
  obtain ⟨localTrace, localHead, localChain, localLast, localHalt, localLength, localFrame⟩ :=
    Kernel.Clear.runs (slot stage) contents store.1
  obtain ⟨trace, final, head, chain, last, label, data, vars, length⟩ :=
    Inline.actual_return_trace (labels stage) (nextLabel stage) (Kernel.Clear.program (slot stage))
      (program Saved) (agrees Saved stage) localTrace
      (⟨some (), store.1, contents⟩ : Kernel.Clear.State)
      (⟨none, none, Function.update contents (slot stage) []⟩ : Kernel.Clear.State) store.2
      localHead localChain localLast localHalt
  have finalEqual : final =
      (⟨some (nextLabel stage), (none, store.2), Function.update contents (slot stage) []⟩ : State Saved) := by
    rcases final with ⟨finalLabel, finalStore, finalData⟩
    change finalLabel = some (nextLabel stage) at label
    change finalStore = (none, store.2) at vars
    change finalData = Function.update contents (slot stage) [] at data
    subst finalLabel
    subst finalStore
    subst finalData
    rfl
  rw [finalEqual] at last
  have actualHead : trace.head? = some (⟨some (stageLabel stage), store, contents⟩ : State Saved) := head
  cases trace with
  | nil => simp only [List.head?_nil, reduceCtorEq] at actualHead
  | cons first rest =>
    have same : first = (⟨some (stageLabel stage), store, contents⟩ : State Saved) := Option.some.inj actualHead
    subst first
    refine ⟨⟨rest, chain, last⟩, ?_⟩
    change rest.length ≤ (contents (slot stage)).length + 2
    rw [localLength] at length
    simp only [List.length_cons] at length
    omega

end PDROC.BitVM.VM.Cleanup
