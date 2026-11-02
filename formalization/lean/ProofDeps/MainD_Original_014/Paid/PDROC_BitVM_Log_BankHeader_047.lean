module

public import Paid.PDROC_BitVM_Log_BankField_046
public import Paid.PDROC_BitVM_Log_Header_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

@[expose] public section

namespace PDROC.BitVM.Log.BankHeader

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native

/-! Genuine canonical list-count scan on global0/24/25, with a fixed finite
store adapter to the108 flags used by actual clears. Count is Bool DATA.
The Nat parameter below specifies the encoded input; it is not in sigma. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev WideState := TM2.Cfg Alphabet Header.Label Header.Store
abbrev Label := Header.Label ⊕ Unit
abbrev SourceStore := Header.Store × (Unit × Lookup.Store)
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def embedding : Header.Stack ↪ Stack where
  toFun := fun index => if index = 0 then 0 else if index = 1 then 24 else 25
  inj' := by intro left right equal; fin_cases left <;> fin_cases right <;> simp_all

def wideProgram := Lift.machine embedding Header.program
def startLabel : Label := .inl 0
def doneLabel : Label := .inr ()

def sourceProgram : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl label => Inline.statement (τ := Unit × Lookup.Store) Sum.inl doneLabel (wideProgram label)
  | .inr _ => .halt

def storeIso : SourceStore ≃ Store where
  toFun := fun store => ((store.1, store.2.1), store.2.2)
  invFun := fun store => (store.1.1, (store.1.2, store.2))
  left_inv := by intro store; rcases store with ⟨flag, marker, query⟩; rfl
  right_inv := by intro store; rcases store with ⟨⟨flag, marker⟩, query⟩; rfl

def program := StoreIso.machine storeIso sourceProgram
def finished (store : Store) : Store := ((none, store.1.2), store.2)

def result (count : ℕ) (suffix : List Bool) (contents : Stack → List Bool) :=
  Function.update (Function.update contents 0 suffix) 25 ((encodeNatBits count).reverse ++ contents 25)

theorem agrees : ∀ label,
    sourceProgram (.inl label) = Inline.statement (τ := Unit × Lookup.Store) Sum.inl doneLabel (wideProgram label) := by
  intro label; rfl

theorem wide_supports : TM2.Supports wideProgram (Finset.univ : Finset Header.Label) :=
  Lift.supports embedding Header.program (Finset.univ : Finset Header.Label) Header.supports

theorem source_supports : TM2.Supports sourceProgram (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label with
    | inl label =>
      apply Inline.supports_statement Sum.inl doneLabel
        (Finset.univ : Finset Header.Label) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact wide_supports.2 label (Finset.mem_univ _)
    | inr marker => cases marker; simp [sourceProgram, TM2.SupportsStmt]

theorem supports : TM2.Supports program (Finset.univ : Finset Label) :=
  StoreIso.supports storeIso sourceProgram (Finset.univ : Finset Label) source_supports

theorem representation (count : ℕ) (suffix : List Bool) (before : WideState)
    (position : before.l = some 0) (input : before.stk 0 = encodeNatBits count ++ suffix)
    (ticks : before.stk 24 = []) :
    Lift.cfg embedding before = Header.state (some 0) before.var
      (encodeNatBits count ++ suffix) [] (before.stk 25) := by
  have slots : Lift.slots embedding before.stk = Header.slots (encodeNatBits count ++ suffix) [] (before.stk 25) := by
    funext index
    fin_cases index <;> simp [Lift.slots, embedding, Header.slots, TwoStack.stackContents, input, ticks]
  change (⟨before.l, before.var, Lift.slots embedding before.stk⟩ : Header.State) = _
  rw [position]
  exact congrArg (fun contents : Header.Stack → List Bool => (⟨some 0, before.var, contents⟩ : Header.State)) slots

theorem result_shape (count : ℕ) (suffix : List Bool) (contents data : Stack → List Bool)
    (ticks : contents 24 = [])
    (projected : Lift.slots embedding data = Header.slots suffix [] ((encodeNatBits count).reverse ++ contents 25))
    (frame : ∀ index : Stack, (∀ localIndex, index ≠ embedding localIndex) → data index = contents index) :
    data = result count suffix contents := by
  funext index
  by_cases mapped : ∃ localIndex, embedding localIndex = index
  · rcases mapped with ⟨localIndex, rfl⟩
    have fact := congrFun projected localIndex
    fin_cases localIndex <;>
      simpa [Lift.slots, embedding, Header.slots, TwoStack.stackContents, result, ticks] using fact
  · have not0 : index ≠ 0 := by
      intro equal
      apply mapped
      refine ⟨0, ?_⟩
      simpa [embedding] using equal.symm
    have not25 : index ≠ 25 := by
      intro equal
      apply mapped
      refine ⟨2, ?_⟩
      simpa [embedding] using equal.symm
    rw [result, Function.update_of_ne not25, Function.update_of_ne not0]
    exact frame index (fun localIndex equal => mapped ⟨localIndex, equal.symm⟩)

theorem wide_runs (count : ℕ) (suffix : List Bool) (before : WideState)
    (position : before.l = some 0) (input : before.stk 0 = encodeNatBits count ++ suffix)
    (ticks : before.stk 24 = []) :
    ∃ (run : List WideState) (after : WideState),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step wideProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step wideProgram after = none ∧ after.l = none ∧
      after.var = none ∧ after.stk = result count suffix before.stk ∧ run.length = 2 * natBits count + 4 := by
  let sourceStart := Header.state (some 0) before.var (encodeNatBits count ++ suffix) [] (before.stk 25)
  let sourceFinal := Header.state none none suffix [] ((encodeNatBits count).reverse ++ before.stk 25)
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt, sourceLength, sourceInput, sourceTicks, sourceArchive⟩ :=
    Header.officialNat_runs count suffix (before.stk 25) before.var
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = sourceStart := Option.some.inj sourceHead
    subst first
    obtain ⟨posts, after, length, chain, last, projected, frame⟩ :=
      Lift.path embedding Header.program before sourceStart sourceFinal rest
        (representation count suffix before position input ticks) sourceChain sourceLast
    have halt : TM2.step wideProgram after = none := by
      apply Lift.halt_project embedding Header.program after
      rw [projected]
      exact sourceHalt
    have done : after.l = none := congrArg (fun state : Header.State => state.l) projected
    have vars : after.var = none := congrArg (fun state : Header.State => state.var) projected
    have data : Lift.slots embedding after.stk = Header.slots suffix []
        ((encodeNatBits count).reverse ++ before.stk 25) := by
      simpa only [Lift.cfg, sourceFinal, Header.state] using congrArg (fun state : Header.State => state.stk) projected
    refine ⟨before :: posts, after, rfl, chain, last, halt, done, vars,
      result_shape count suffix before.stk after.stk ticks data frame, ?_⟩
    simp only [List.length_cons] at sourceLength ⊢
    omega

theorem source_runs (count : ℕ) (suffix : List Bool) (contents : Stack → List Bool) (store : SourceStore)
    (input : contents 0 = encodeNatBits count ++ suffix) (ticks : contents 24 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, store, contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step sourceProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step sourceProgram after = none ∧ after.l = none ∧
      after.var = (none, store.2) ∧ after.stk = result count suffix contents ∧ run.length = 2 * natBits count + 5 := by
  let before : WideState := ⟨some 0, store.1, contents⟩
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    wide_runs count suffix before rfl input ticks
  obtain ⟨returned, after, head, chain, last, label, data, saved, length⟩ :=
    Inline.actual_return_trace Sum.inl doneLabel wideProgram sourceProgram agrees source before sourceFinal store.2
      sourceHead sourceChain sourceLast sourceHalt
  have varExact : after.var = (none, store.2) := by rw [saved, sourceVar]
  have dataExact : after.stk = result count suffix contents := data.trans sourceData
  have afterEq : after = (⟨some doneLabel, (none, store.2), result count suffix contents⟩ : SourceState) := by
    rcases after with ⟨currentLabel, currentVar, currentData⟩
    change currentLabel = some doneLabel at label
    change currentVar = (none, store.2) at varExact
    change currentData = result count suffix contents at dataExact
    subst currentLabel; subst currentVar; subst currentData
    rfl
  let final : SourceState := ⟨none, (none, store.2), result count suffix contents⟩
  let run := returned ++ [final]
  have actual : run.IsChain (fun a b => TM2.step sourceProgram a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [afterEq]
    rfl
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons returned final [], rfl, rfl, rfl, rfl, ?_⟩
  · simp only [run, List.head?_append, head, Option.some_or, Inline.cfg, before,
      Option.map_some, Option.getD_some, startLabel]
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

theorem runs (count : ℕ) (suffix : List Bool) (contents : Stack → List Bool) (store : Store)
    (input : contents 0 = encodeNatBits count ++ suffix) (ticks : contents 24 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧ after.l = none ∧
      after.var = finished store ∧ after.stk = result count suffix contents ∧ run.length = 2 * natBits count + 5 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    source_runs count suffix contents (storeIso.symm store) input ticks
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso sourceProgram source
      (⟨some startLabel, storeIso.symm store, contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.BankHeader
