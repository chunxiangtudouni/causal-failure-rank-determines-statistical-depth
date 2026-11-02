module

public import Paid.PDROC_BitVM_VM_Control_Direct_001
public import Paid.PDROC_BitVM_Log_InputLiteral_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.VM.Control.PCLiteral

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Log

/-! Static source-PC literals, not runtime widths. This adapter reuses the exact
parent RegisterMove literal clear/push program and its genuine trace. The word
is fixed by source code BEFORE all raw inputs; PC values >=13 are supported.
No Log source or inspector is modified. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev WideState := TM2.Cfg Alphabet Unit (Option Bool)
abbrev Label := Unit ⊕ Unit
abbrev SourceStore := BankHeader.SourceStore
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def embedding : TwoStack.Stack ↪ Stack := PDROC.BitVM.Log.InputLiteral.embedding

def wideProgram (literal : List Bool) := Lift.machine embedding (Kernel.RegisterMove.literalProgram (literal))
def startLabel : Label := .inl ()
def doneLabel : Label := .inr ()

def sourceProgram (literal : List Bool) : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl _ => Inline.statement (τ := Unit × Lookup.Store) Sum.inl doneLabel (wideProgram literal ())
  | .inr _ => .halt

def program (literal : List Bool) := StoreIso.machine BankHeader.storeIso (sourceProgram literal)

theorem agrees (literal : List Bool) : ∀ label,
    sourceProgram literal (.inl label) =
      Inline.statement (τ := Unit × Lookup.Store) Sum.inl doneLabel (wideProgram literal label) := by
  intro label; cases label; rfl

theorem wide_supports (literal : List Bool) : TM2.Supports (wideProgram literal) (Finset.univ : Finset Unit) :=
  Lift.supports embedding (Kernel.RegisterMove.literalProgram (literal)) (Finset.univ : Finset Unit)
    (Kernel.RegisterMove.literal_supports (literal))

theorem source_supports (literal : List Bool) : TM2.Supports (sourceProgram literal) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label with
    | inl marker =>
      cases marker
      apply Inline.supports_statement Sum.inl doneLabel (Finset.univ : Finset Unit) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact (wide_supports literal).2 () (Finset.mem_univ _)
    | inr marker => cases marker; simp [sourceProgram, TM2.SupportsStmt]

theorem supports (literal : List Bool) : TM2.Supports (program literal) (Finset.univ : Finset Label) :=
  StoreIso.supports BankHeader.storeIso (sourceProgram literal) (Finset.univ : Finset Label) (source_supports literal)

theorem representation (before : WideState) (position : before.l = some ()) (scratch : before.stk 28 = []) :
    Lift.cfg embedding before = Kernel.RegisterMove.clearState (some ()) before.var (before.stk 0) (before.stk 24) := by
  have slots : Lift.slots embedding before.stk = TwoStack.threeStacks (before.stk 0) (before.stk 24) [] := by
    funext index
    fin_cases index <;> simp [Lift.slots, embedding, PDROC.BitVM.Log.InputLiteral.embedding, TwoStack.threeStacks, scratch]
  change (⟨before.l, before.var, Lift.slots embedding before.stk⟩ : TM2.Cfg TwoStack.Alphabet Unit (Option Bool)) = _
  rw [position]
  exact congrArg (fun contents : TwoStack.Stack → List Bool =>
    (⟨some (), before.var, contents⟩ : TM2.Cfg TwoStack.Alphabet Unit (Option Bool))) slots

theorem data_shape (literal : List Bool) (contents data : Stack → List Bool) (scratch : contents 28 = [])
    (projected : Lift.slots embedding data = TwoStack.threeStacks (contents 0) (literal) [])
    (frame : ∀ index : Stack, (∀ localIndex, index ≠ embedding localIndex) → data index = contents index) :
    data = Function.update contents 24 (literal) := by
  funext index
  by_cases mapped : ∃ localIndex, embedding localIndex = index
  · rcases mapped with ⟨localIndex, rfl⟩
    have fact := congrFun projected localIndex
    fin_cases localIndex <;> simpa [Lift.slots, embedding, PDROC.BitVM.Log.InputLiteral.embedding, TwoStack.threeStacks, scratch] using fact
  · have not24 : index ≠ 24 := by
      intro equal
      apply mapped
      refine ⟨1, ?_⟩
      simpa [embedding, PDROC.BitVM.Log.InputLiteral.embedding] using equal.symm
    rw [Function.update_of_ne not24]
    exact frame index (fun localIndex equal => mapped ⟨localIndex, equal.symm⟩)

theorem wide_runs (literal : List Bool) (before : WideState) (position : before.l = some ()) (scratch : before.stk 28 = []) :
    ∃ (run : List WideState) (after : WideState),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (wideProgram literal) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (wideProgram literal) after = none ∧ after.l = none ∧
      after.var = none ∧ after.stk = Function.update before.stk 24 (literal) ∧
      run.length = (before.stk 24).length + 2 := by
  let sourceStart := Kernel.RegisterMove.clearState (some ()) before.var (before.stk 0) (before.stk 24)
  let sourceFinal := Kernel.RegisterMove.clearState none none (before.stk 0) (literal)
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt, sourceLength, sourceInput, sourceTarget, sourceScratch⟩ :=
    Kernel.RegisterMove.literal_runs (literal) (before.stk 0) (before.stk 24) before.var
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = sourceStart := Option.some.inj sourceHead
    subst first
    obtain ⟨posts, after, length, chain, last, projected, frame⟩ :=
      Lift.path embedding (Kernel.RegisterMove.literalProgram (literal)) before sourceStart sourceFinal rest
        (representation before position scratch) sourceChain sourceLast
    have halt : TM2.step (wideProgram literal) after = none := by
      apply Lift.halt_project embedding (Kernel.RegisterMove.literalProgram (literal)) after
      rw [projected]
      exact sourceHalt
    have done : after.l = none := congrArg (fun state : TM2.Cfg TwoStack.Alphabet Unit (Option Bool) => state.l) projected
    have vars : after.var = none := congrArg (fun state : TM2.Cfg TwoStack.Alphabet Unit (Option Bool) => state.var) projected
    have data : Lift.slots embedding after.stk = TwoStack.threeStacks (before.stk 0) (literal) [] := by
      simpa only [Lift.cfg, sourceFinal, Kernel.RegisterMove.clearState] using
        congrArg (fun state : TM2.Cfg TwoStack.Alphabet Unit (Option Bool) => state.stk) projected
    refine ⟨before :: posts, after, rfl, chain, last, halt, done, vars, data_shape literal before.stk after.stk scratch data frame, ?_⟩
    simp only [List.length_cons] at sourceLength ⊢
    omega

theorem source_runs (literal : List Bool) (contents : Stack → List Bool) (store : SourceStore) (scratch : contents 28 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, store, contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram literal) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram literal) after = none ∧ after.l = none ∧
      after.var = (none, store.2) ∧ after.stk = Function.update contents 24 (literal) ∧
      run.length = (contents 24).length + 3 := by
  let before : WideState := ⟨some (), store.1, contents⟩
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    wide_runs literal before rfl scratch
  obtain ⟨returned, after, head, chain, last, label, data, vars, length⟩ :=
    Inline.actual_return_trace Sum.inl doneLabel (wideProgram literal) (sourceProgram literal) (agrees literal) source before sourceFinal store.2
      sourceHead sourceChain sourceLast sourceHalt
  have varExact : after.var = (none, store.2) := by rw [vars, sourceVar]
  have dataExact : after.stk = Function.update contents 24 (literal) := data.trans sourceData
  have afterEq : after = (⟨some doneLabel, (none, store.2), Function.update contents 24 (literal)⟩ : SourceState) := by
    rcases after with ⟨currentLabel, currentVar, currentData⟩
    change currentLabel = some doneLabel at label
    change currentVar = (none, store.2) at varExact
    change currentData = Function.update contents 24 (literal) at dataExact
    subst currentLabel; subst currentVar; subst currentData
    rfl
  let final : SourceState := ⟨none, (none, store.2), Function.update contents 24 (literal)⟩
  let run := returned ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (sourceProgram literal) a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [afterEq]
    rfl
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons returned final [], rfl, rfl, rfl, rfl, ?_⟩
  · simp only [run, List.head?_append, head, Option.some_or, Inline.cfg, before, Option.map_some, Option.getD_some, startLabel]
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    change source.length = (contents 24).length + 2 at sourceLength
    omega

theorem runs (literal : List Bool) (contents : Stack → List Bool) (store : Store) (scratch : contents 28 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program literal) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program literal) after = none ∧ after.l = none ∧
      after.var = BankHeader.finished store ∧ after.stk = Function.update contents 24 (literal) ∧
      run.length = (contents 24).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    source_runs literal contents (BankHeader.storeIso.symm store) scratch
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace BankHeader.storeIso (sourceProgram literal) source
      (⟨some startLabel, BankHeader.storeIso.symm store, contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

/-- A candidate is a FINITE SOURCE-CODE choice, before the raw input.
The actual literal macro clears old24, pushes its real byte word, keeps26
and all other caller data, and ends with28 genuinely empty. -/
theorem pc_runs (code : Program) (candidate : PC code) (contents : Stack → List Bool)
    (store : Store) (scratch : contents 28 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun before final => TM2.step (program (encodeNatBits candidate.val)) before = some final) ∧
      run.getLast? = some after ∧ TM2.step (program (encodeNatBits candidate.val)) after = none ∧ after.l = none ∧
      after.var = BankHeader.finished store ∧
      after.stk = Function.update contents 24 (encodeNatBits candidate.val) ∧
      run.length = (contents 24).length + 3 :=
  runs (encodeNatBits candidate.val) contents store scratch

end PDROC.BitVM.VM.Control.PCLiteral
