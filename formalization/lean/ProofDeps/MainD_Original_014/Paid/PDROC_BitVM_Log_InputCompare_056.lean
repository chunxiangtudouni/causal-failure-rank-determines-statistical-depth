module

public import Paid.PDROC_BitVM_Log_BankMount_054

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.Log.InputCompare

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native

/-! Actual per-Bool input-address comparison. Candidate24 is a physically
written canonical word; query26 was physically read from a Nat register.
The program contains NO Nat comparison. Nat equality is only the proven
meaning of the resulting finite flag, by the passed canonical codec lemma. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev WideState := TM2.Cfg Alphabet Query.Label Query.Store
abbrev Label := Query.Label ⊕ Unit
abbrev SourceStore := Query.Store × Kernel.NatMarshal.Store
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def wideProgram := Lift.machine Lookup.heapWorkEmbed Query.program
def startLabel : Label := .inl 0
def doneLabel : Label := .inr ()
def sourceProgram : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl label => Inline.statement (τ := Kernel.NatMarshal.Store) Sum.inl doneLabel (wideProgram label)
  | .inr _ => .halt
def program := StoreIso.machine BankFieldRoot.storeIso sourceProgram

def compared (contents : Stack → List Bool) := Function.update (Function.update contents 24 []) 27 []

theorem agrees : ∀ label, sourceProgram (.inl label) =
    Inline.statement (τ := Kernel.NatMarshal.Store) Sum.inl doneLabel (wideProgram label) := by intro label; rfl

theorem wide_supports : TM2.Supports wideProgram (Finset.univ : Finset Query.Label) :=
  Lift.supports Lookup.heapWorkEmbed Query.program (Finset.univ : Finset Query.Label) Query.supports

theorem source_supports : TM2.Supports sourceProgram (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label with
    | inl label =>
      apply Inline.supports_statement Sum.inl doneLabel
        (Finset.univ : Finset Query.Label) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact wide_supports.2 label (Finset.mem_univ _)
    | inr marker => cases marker; simp [sourceProgram, TM2.SupportsStmt]

theorem supports : TM2.Supports program (Finset.univ : Finset Label) :=
  StoreIso.supports BankFieldRoot.storeIso sourceProgram (Finset.univ : Finset Label) source_supports

theorem representation (candidate query : ℕ) (before : WideState) (position : before.l = some 0)
    (address : before.stk 24 = encodeNatBits candidate) (queryValue : before.stk 26 = encodeNatBits query)
    (saved : before.stk 27 = []) :
    Lift.cfg Lookup.heapWorkEmbed before = Query.state (some 0) before.var
      (encodeNatBits candidate) (encodeNatBits query) [] (Lift.slots Lookup.heapWorkEmbed before.stk) := by
  have slots : Lift.slots Lookup.heapWorkEmbed before.stk = Query.slots
      (encodeNatBits candidate) (encodeNatBits query) [] (Lift.slots Lookup.heapWorkEmbed before.stk) := by
    funext index
    fin_cases index <;> simp [Lift.slots, Lookup.heapWorkEmbed, Query.slots, address, queryValue, saved]
  change (⟨before.l, before.var, Lift.slots Lookup.heapWorkEmbed before.stk⟩ : Query.State) = _
  rw [position]
  exact congrArg (fun contents : Query.Stack → List Bool => (⟨some 0, before.var, contents⟩ : Query.State)) slots

theorem compared_shape (query : ℕ) (contents data : Stack → List Bool)
    (queryValue : contents 26 = encodeNatBits query)
    (projected : Lift.slots Lookup.heapWorkEmbed data = Query.slots [] (encodeNatBits query) []
      (Lift.slots Lookup.heapWorkEmbed contents))
    (frame : ∀ index : Stack, (∀ localIndex, index ≠ Lookup.heapWorkEmbed localIndex) → data index = contents index) :
    data = compared contents := by
  funext index
  by_cases mapped : ∃ localIndex, Lookup.heapWorkEmbed localIndex = index
  · rcases mapped with ⟨localIndex, rfl⟩
    have fact := congrFun projected localIndex
    fin_cases localIndex <;>
      simpa [Lift.slots, Lookup.heapWorkEmbed, Query.slots, compared, queryValue] using fact
  · have not24 : index ≠ 24 := by
      intro equal
      apply mapped
      refine ⟨1, ?_⟩
      simpa [Lookup.heapWorkEmbed] using equal.symm
    have not27 : index ≠ 27 := by
      intro equal
      apply mapped
      refine ⟨4, ?_⟩
      simpa [Lookup.heapWorkEmbed] using equal.symm
    rw [compared, Function.update_of_ne not27, Function.update_of_ne not24]
    exact frame index (fun localIndex equal => mapped ⟨localIndex, equal.symm⟩)

theorem wide_runs (candidate query : ℕ) (before : WideState) (position : before.l = some 0)
    (address : before.stk 24 = encodeNatBits candidate) (queryValue : before.stk 26 = encodeNatBits query)
    (saved : before.stk 27 = []) :
    ∃ (run : List WideState) (after : WideState),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step wideProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step wideProgram after = none ∧ after.l = none ∧
      Query.equality after.var = decide (candidate = query) ∧ Query.recordTag after.var = Query.recordTag before.var ∧
      after.stk = compared before.stk ∧ run.length ≤ 4 * natBits candidate + 7 := by
  let other := Lift.slots Lookup.heapWorkEmbed before.stk
  let sourceStart := Query.state (some 0) before.var (encodeNatBits candidate) (encodeNatBits query) [] other
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceFlag, sourceTag, sourceData, sourceLength⟩ :=
    Query.nat_address_compare_runs candidate query other before.var
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = sourceStart := Option.some.inj sourceHead
    subst first
    obtain ⟨posts, after, length, chain, last, projected, frame⟩ :=
      Lift.path Lookup.heapWorkEmbed Query.program before sourceStart sourceFinal rest
        (representation candidate query before position address queryValue saved) sourceChain sourceLast
    have halt : TM2.step wideProgram after = none := by
      apply Lift.halt_project Lookup.heapWorkEmbed Query.program after
      rw [projected]
      exact sourceHalt
    have done : after.l = none := (congrArg (fun state : Query.State => state.l) projected).trans sourceDone
    have vars : after.var = sourceFinal.var := congrArg (fun state : Query.State => state.var) projected
    have data : Lift.slots Lookup.heapWorkEmbed after.stk = Query.slots [] (encodeNatBits query) [] other := by
      simpa only [Lift.cfg] using (congrArg (fun state : Query.State => state.stk) projected).trans sourceData
    refine ⟨before :: posts, after, rfl, chain, last, halt, done, ?_, ?_,
      compared_shape query before.stk after.stk queryValue data frame, ?_⟩
    · rw [vars]; exact sourceFlag
    · rw [vars]; exact sourceTag
    · simp only [List.length_cons] at sourceLength ⊢
      omega

theorem source_runs (candidate query : ℕ) (contents : Stack → List Bool) (store : SourceStore)
    (address : contents 24 = encodeNatBits candidate) (queryValue : contents 26 = encodeNatBits query)
    (savedWord : contents 27 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, store, contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step sourceProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step sourceProgram after = none ∧ after.l = none ∧
      after.var.2 = store.2 ∧ Query.equality after.var.1 = decide (candidate = query) ∧
      Query.recordTag after.var.1 = Query.recordTag store.1 ∧ after.stk = compared contents ∧
      run.length ≤ 4 * natBits candidate + 8 := by
  let before : WideState := ⟨some 0, store.1, contents⟩
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceFlag, sourceTag, sourceData, sourceLength⟩ :=
    wide_runs candidate query before rfl address queryValue savedWord
  obtain ⟨returned, after, head, chain, last, label, data, vars, length⟩ :=
    Inline.actual_return_trace Sum.inl doneLabel wideProgram sourceProgram agrees source before sourceFinal store.2
      sourceHead sourceChain sourceLast sourceHalt
  have afterEq : after = (⟨some doneLabel, (sourceFinal.var, store.2), sourceFinal.stk⟩ : SourceState) := by
    rcases after with ⟨currentLabel, currentVar, currentData⟩
    change currentLabel = some doneLabel at label
    change currentVar = (sourceFinal.var, store.2) at vars
    change currentData = sourceFinal.stk at data
    subst currentLabel; subst currentVar; subst currentData
    rfl
  let final : SourceState := ⟨none, (sourceFinal.var, store.2), sourceFinal.stk⟩
  let run := returned ++ [final]
  have actual : run.IsChain (fun a b => TM2.step sourceProgram a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [afterEq]
    rfl
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons returned final [], rfl, rfl, rfl,
    sourceFlag, sourceTag, sourceData, ?_⟩
  · simp only [run, List.head?_append, head, Option.some_or, Inline.cfg, before, Option.map_some, Option.getD_some, startLabel]
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

theorem runs (candidate query : ℕ) (contents : Stack → List Bool) (store : Store)
    (address : contents 24 = encodeNatBits candidate) (queryValue : contents 26 = encodeNatBits query)
    (savedWord : contents 27 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧ after.l = none ∧
      after.var.1 = store.1 ∧ Query.equality after.var.2.1 = decide (candidate = query) ∧
      Query.recordTag after.var.2.1 = Query.recordTag store.2.1 ∧ after.stk = compared contents ∧
      run.length ≤ 4 * natBits candidate + 8 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone,
    sourceSaved, sourceFlag, sourceTag, sourceData, sourceLength⟩ :=
    source_runs candidate query contents (BankFieldRoot.storeIso.symm store) address queryValue savedWord
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace BankFieldRoot.storeIso sourceProgram source
      (⟨some startLabel, BankFieldRoot.storeIso.symm store, contents⟩ : SourceState) sourceFinal
      sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, ?_, ?_, data.trans sourceData, ?_⟩
  · rw [saved]; exact sourceSaved
  · rw [saved]; exact sourceFlag
  · rw [saved]; exact sourceTag
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.InputCompare
