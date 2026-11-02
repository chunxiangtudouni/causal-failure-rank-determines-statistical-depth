module

public import Paid.PDROC_BitVM_Log_CellCopy_003
public import Paid.PDROC_BitVM_Log_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.CellCopy

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-- The actual mirrored field path returns into the Cell-copy program.
Only literal local code agreement is assumed, never a successful Cell oracle. -/
theorem field_return_run (labels : CellField.Label → Label) (returnLabel : Label)
    (agrees : ∀ label, enrichedProgram (labels label) = fieldCode labels returnLabel label)
    (value : ℕ) (suffix archive captured : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ run : List EnrichedState,
      run.head? = some (enrichedState (some (labels 0)) (store, ())
        (encodeNatBits value ++ suffix) [] archive captured other) ∧
      run.IsChain (fun a b => TM2.step enrichedProgram a = some b) ∧
      run.getLast? = some (enrichedState (some returnLabel) ((none, store.2), ()) suffix []
        ((encodeNatBits value).reverse ++ archive) ((encodeNatBits value).reverse ++ captured) other) ∧
      run.length = 2 * natBits value + 4 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    CellField.official_field_runs value suffix archive captured other store
  obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
    Native.Inline.actual_return_trace labels returnLabel CellField.program enrichedProgram agrees
      source (Capture.state (some 0) store (encodeNatBits value ++ suffix) [] archive captured other)
      sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have afterEq : after = enrichedState (some returnLabel) ((none, store.2), ()) suffix []
      ((encodeNatBits value).reverse ++ archive) ((encodeNatBits value).reverse ++ captured) other := by
    have varEq : after.var = ((none, store.2), ()) := by rw [localStoreEq, sourceVar]
    have slotsEq : after.stk = Capture.slots suffix [] ((encodeNatBits value).reverse ++ archive)
        ((encodeNatBits value).reverse ++ captured) other := data.trans sourceData
    rcases after with ⟨label, vars, contents⟩
    change label = some returnLabel at returned
    change vars = ((none, store.2), ()) at varEq
    change contents = Capture.slots suffix [] ((encodeNatBits value).reverse ++ archive)
      ((encodeNatBits value).reverse ++ captured) other at slotsEq
    subst label
    subst vars
    subst contents
    rfl
  refine ⟨run, ?_, chain, ?_, length.trans sourceLength⟩
  · exact head
  · simpa only [afterEq] using last

theorem close_enriched (source : List EnrichedState) (before : EnrichedState)
    (suffix archive captured : List Bool) (other : Stack → List Bool) (store : Enriched) (limit : ℕ)
    (head : source.head? = some before)
    (chain : source.IsChain (fun a b => TM2.step enrichedProgram a = some b))
    (last : source.getLast? = some (enrichedState (some doneLabel) store suffix [] archive captured other))
    (length : source.length ≤ limit) :
    ∃ (run : List EnrichedState) (after : EnrichedState),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step enrichedProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step enrichedProgram after = none ∧
      after.l = none ∧ after.var = store ∧ after.stk = Capture.slots suffix [] archive captured other ∧
      run.length ≤ limit + 1 := by
  let after := enrichedState none store suffix [] archive captured other
  let run := source ++ [after]
  have actual : run.IsChain (fun a b => TM2.step enrichedProgram a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old
    subst next
    exact done_halt suffix [] archive captured other store
  refine ⟨run, after, ?_, actual, ?_, halted suffix [] archive captured other store,
    rfl, rfl, rfl, ?_⟩
  · change (source ++ [after]).head? = some before
    simp only [List.head?_append, head, Option.some_or]
  · exact List.getLast?_append_cons source after []
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

theorem natural_enriched_runs (value : ℕ) (suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    ∃ (run : List EnrichedState) (after : EnrichedState),
      run.head? = some (enrichedState (some startLabel) (store, ())
        (encodeCellBits (.natural value) ++ suffix) [] archive captured other) ∧
      run.IsChain (fun a b => TM2.step enrichedProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step enrichedProgram after = none ∧
      after.l = none ∧ after.var = ((none, store.2), ()) ∧
      after.stk = Capture.slots suffix [] ((encodeCellBits (.natural value)).reverse ++ archive)
        ((encodeCellBits (.natural value)).reverse ++ captured) other ∧
      run.length ≤ (encodeCellBits (.natural value)).length + 6 := by
  let innerStore := Query.setRecord store (some false)
  obtain ⟨part, partHead, partChain, partLast, partLength⟩ :=
    field_return_run naturalLabel doneLabel (by intro label; rfl)
      value suffix (false :: archive) (false :: captured) other innerStore
  let before := enrichedState (some startLabel) (store, ())
    (encodeCellBits (.natural value) ++ suffix) [] archive captured other
  let source := before :: part
  have sourceHead : source.head? = some before := rfl
  have sourceChain : source.IsChain (fun a b => TM2.step enrichedProgram a = some b) := by
    apply List.IsChain.cons partChain
    intro next hn
    rw [partHead] at hn
    have equal := Option.mem_some_iff.mp hn
    subst next
    exact tag_false (encodeNatBits value ++ suffix) [] archive captured other (store, ())
  have archiveEq : ∀ tail : List Bool, (encodeNatBits value).reverse ++ false :: tail =
      (encodeCellBits (.natural value)).reverse ++ tail := by
    intro tail
    simp [encodeCellBits, List.reverse_cons, List.append_assoc]
  have sourceLast : source.getLast? = some (enrichedState (some doneLabel) ((none, store.2), ())
      suffix [] ((encodeCellBits (.natural value)).reverse ++ archive)
        ((encodeCellBits (.natural value)).reverse ++ captured) other) := by
    simp only [source, List.getLast?_cons, partLast, Option.getD_some, archiveEq]
    rfl
  have sourceLength : source.length ≤ (encodeCellBits (.natural value)).length + 5 := by
    simp only [source, List.length_cons, partLength, encodeCellBits, List.length_cons, Log.nat_word_length]
    omega
  exact close_enriched source before suffix ((encodeCellBits (.natural value)).reverse ++ archive)
    ((encodeCellBits (.natural value)).reverse ++ captured) other ((none, store.2), ())
    ((encodeCellBits (.natural value)).length + 5) sourceHead sourceChain sourceLast sourceLength

end PDROC.BitVM.Log.CellCopy

namespace PDROC.BitVM.Log.CellCopy

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

theorem rational_enriched_runs (value : ℚ) (suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    ∃ (run : List EnrichedState) (after : EnrichedState),
      run.head? = some (enrichedState (some startLabel) (store, ())
        (encodeCellBits (.rational value) ++ suffix) [] archive captured other) ∧
      run.IsChain (fun a b => TM2.step enrichedProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step enrichedProgram after = none ∧
      after.l = none ∧ after.var = ((none, store.2), ()) ∧
      after.stk = Capture.slots suffix [] ((encodeCellBits (.rational value)).reverse ++ archive)
        ((encodeCellBits (.rational value)).reverse ++ captured) other ∧
      run.length ≤ (encodeCellBits (.rational value)).length + 6 := by
  let sign : Bool := decide (value < 0)
  let tagStore := Query.setRecord store (some true)
  let signStore := Query.setRecord tagStore (some sign)
  let numWord := encodeNatBits value.num.natAbs
  let denWord := encodeNatBits value.den
  let numArchive := numWord.reverse ++ sign :: true :: archive
  let numCaptured := numWord.reverse ++ sign :: true :: captured
  obtain ⟨numTrace, numHead, numChain, numLast, numLength⟩ :=
    field_return_run numeratorLabel (denominatorLabel 0) (by intro label; rfl)
      value.num.natAbs (denWord ++ suffix) (sign :: true :: archive) (sign :: true :: captured) other signStore
  obtain ⟨denTrace, denHead, denChain, denLast, denLength⟩ :=
    field_return_run denominatorLabel doneLabel (by intro label; rfl)
      value.den suffix numArchive numCaptured other (none, store.2)
  let before := enrichedState (some startLabel) (store, ())
    (encodeCellBits (.rational value) ++ suffix) [] archive captured other
  let beforeSign := enrichedState (some signLabel) (tagStore, ())
    (sign :: (numWord ++ (denWord ++ suffix))) [] (true :: archive) (true :: captured) other
  let leadTrace := before :: beforeSign :: numTrace
  have leadHead : leadTrace.head? = some before := rfl
  have leadChain : leadTrace.IsChain (fun a b => TM2.step enrichedProgram a = some b) := by
    apply List.isChain_cons_cons.mpr
    constructor
    · simpa only [before, beforeSign, encodeCellBits, sign, numWord, denWord, tagStore, setRecord,
        List.cons_append, List.nil_append, List.append_assoc] using
        tag_true (sign :: (numWord ++ (denWord ++ suffix))) [] archive captured other (store, ())
    · apply List.IsChain.cons numChain
      intro next hn
      rw [numHead] at hn
      have equal := Option.mem_some_iff.mp hn
      subst next
      exact sign_bit sign (numWord ++ (denWord ++ suffix)) [] (true :: archive) (true :: captured) other (tagStore, ())
  let middle := enrichedState (some (denominatorLabel 0)) ((none, store.2), ())
    (denWord ++ suffix) [] numArchive numCaptured other
  have leadLast : leadTrace.getLast? = some middle := by
    simp only [leadTrace, List.getLast?_cons, numLast, Option.getD_some]
    rfl
  have leadLength : leadTrace.length = 2 + numTrace.length := by
    simp only [leadTrace, List.length_cons]; omega
  let joined := leadTrace ++ denTrace.tail
  have joinedHead : joined.head? = some before := by
    simp only [joined, List.head?_append, leadHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step enrichedProgram a = some b) :=
    TwoStack.join_chain leadTrace denTrace middle leadChain denChain leadLast denHead
  have denNotOne : denTrace.length ≠ 1 := by omega
  have archiveEq : (encodeNatBits value.den).reverse ++ numArchive =
      (encodeCellBits (.rational value)).reverse ++ archive := by
    simp [numArchive, numWord, sign, encodeCellBits, List.reverse_append, List.append_assoc]
  have capturedEq : (encodeNatBits value.den).reverse ++ numCaptured =
      (encodeCellBits (.rational value)).reverse ++ captured := by
    simp [numCaptured, numWord, sign, encodeCellBits, List.reverse_append, List.append_assoc]
  have joinedLast : joined.getLast? = some (enrichedState (some doneLabel) ((none, store.2), ())
      suffix [] ((encodeCellBits (.rational value)).reverse ++ archive)
        ((encodeCellBits (.rational value)).reverse ++ captured) other) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, denNotOne, ↓reduceIte,
      denLast, archiveEq, capturedEq, Option.some_or]
  have joinedLength : joined.length ≤ (encodeCellBits (.rational value)).length + 5 := by
    simp only [joined, List.length_append, List.length_tail, leadLength, numLength]
    simp only [encodeCellBits, List.length_append, List.length_cons, List.length_nil, Log.nat_word_length]
    omega
  exact close_enriched joined before suffix ((encodeCellBits (.rational value)).reverse ++ archive)
    ((encodeCellBits (.rational value)).reverse ++ captured) other ((none, store.2), ())
    ((encodeCellBits (.rational value)).length + 5) joinedHead joinedChain joinedLast joinedLength

/-- The public program uses the same finite Query store. Parent StoreIso
maps the ONE enriched real path without changing tape data, cost or HALT. -/
theorem copy_runs (value : Cell) (suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some startLabel) store (encodeCellBits value ++ suffix)
        [] archive captured other) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = Capture.slots suffix [] ((encodeCellBits value).reverse ++ archive)
        ((encodeCellBits value).reverse ++ captured) other ∧
      run.length ≤ (encodeCellBits value).length + 6 := by
  have enriched : ∃ (run : List EnrichedState) (after : EnrichedState),
      run.head? = some (enrichedState (some startLabel) (store, ())
        (encodeCellBits value ++ suffix) [] archive captured other) ∧
      run.IsChain (fun a b => TM2.step enrichedProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step enrichedProgram after = none ∧
      after.l = none ∧ after.var = ((none, store.2), ()) ∧
      after.stk = Capture.slots suffix [] ((encodeCellBits value).reverse ++ archive)
        ((encodeCellBits value).reverse ++ captured) other ∧
      run.length ≤ (encodeCellBits value).length + 6 := by
    cases value with
    | natural value => exact natural_enriched_runs value suffix archive captured other store
    | rational value => exact rational_enriched_runs value suffix archive captured other store
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := enriched
  obtain ⟨run, after, head, chain, last, halt, label, varEq, data, length⟩ :=
    Native.StoreIso.actual_trace peel enrichedProgram source
      (enrichedState (some startLabel) (store, ()) (encodeCellBits value ++ suffix)
        [] archive captured other) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, ?_, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · exact head
  · rw [varEq, sourceVar]
    rfl
  · rw [length]
    exact sourceLength

end PDROC.BitVM.Log.CellCopy
