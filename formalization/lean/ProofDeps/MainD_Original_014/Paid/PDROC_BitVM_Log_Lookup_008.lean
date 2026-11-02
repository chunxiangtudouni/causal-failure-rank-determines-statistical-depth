module

public import Paid.PDROC_BitVM_Log_Lookup_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.Lookup

open Turing PaperProofs.Paid.Computation

/-! Matched Cells and restoration are real finite-stack subroutines. The
selected component path is mapped once, with its local halt becoming the
actual lookup return. No logical lookup or Cell decoding is executed here. -/

def copiedState (label : Option Label) (store : Store) (captured input archive query result : List Bool) : State :=
  ⟨label, store, Capture.slots input [] archive captured (slots input archive query result)⟩

theorem copy_return_runs (value : Cell) (input archive query result : List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some (copyLabel CellCopy.startLabel)) store
        (encodeCellBits value ++ input) archive query result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some (copiedState (some (valueLabel 0)) ((none, store.1.2), store.2)
        (encodeCellBits value).reverse input ((encodeCellBits value).reverse ++ archive) query result) ∧
      run.length ≤ (encodeCellBits value).length + 6 := by
  let other := slots input archive query result
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    CellCopy.copy_runs value input archive [] other store.1
  obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
    Native.Inline.actual_return_trace copyLabel (valueLabel 0) CellCopy.program program
      (by intro label; rfl) source
      (CellCopy.state (some CellCopy.startLabel) store.1 (encodeCellBits value ++ input) [] archive [] other)
      sourceFinal store.2 sourceHead sourceChain sourceLast sourceHalt
  have initialSlots : Capture.slots (encodeCellBits value ++ input) [] archive [] other =
      slots (encodeCellBits value ++ input) archive query result := by
    funext index; fin_cases index <;> simp [Capture.slots, slots, other]
  have finalSlots : after.stk = Capture.slots input [] ((encodeCellBits value).reverse ++ archive)
      (encodeCellBits value).reverse (slots input ((encodeCellBits value).reverse ++ archive) query result) := by
    rw [data, sourceData]
    funext index; fin_cases index <;> simp [Capture.slots, slots, other]
  have finalStore : after.var = ((none, store.1.2), store.2) := by rw [localStoreEq, sourceVar]
  have afterEq : after = copiedState (some (valueLabel 0)) ((none, store.1.2), store.2)
      (encodeCellBits value).reverse input ((encodeCellBits value).reverse ++ archive) query result := by
    rcases after with ⟨label, vars, contents⟩
    change label = some (valueLabel 0) at returned
    change vars = ((none, store.1.2), store.2) at finalStore
    change contents = _ at finalSlots
    subst label; subst vars; subst contents
    rfl
  refine ⟨run, ?_, chain, ?_, ?_⟩
  · simpa only [Native.Inline.cfg, CellCopy.state, initialSlots, Option.map_some,
      Option.getD_some, state, Prod.eta] using head
  · simpa only [afterEq] using last
  · rw [length]; exact sourceLength

/-- Actual reverse-value6 is drained to result5, restoring the original
Cell byte order. The history archive and query remain unchanged. -/
theorem value_return_runs (captured input archive query result : List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (copiedState (some (valueLabel 0)) store captured input archive query result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some (state (some (historyLabel 0)) ((none, store.1.2), store.2)
        input archive query (captured.reverse ++ result)) ∧
      run.length = captured.length + 3 := by
  let other := slots input archive query result
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    Drain.drain_runs true captured result other store.1
  obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
    Native.Inline.actual_return_trace valueLabel (historyLabel 0) (Drain.program true) program
      (by intro label; rfl) source
      (Drain.state true (some 0) store.1 captured result other)
      sourceFinal store.2 sourceHead sourceChain sourceLast sourceHalt
  have initialSlots : Drain.slots true captured result other =
      Capture.slots input [] archive captured (slots input archive query result) := by
    funext index; fin_cases index <;> simp [Drain.slots, Drain.source, Drain.target, Capture.slots, slots, other]
  have finalSlots : after.stk = slots input archive query (captured.reverse ++ result) := by
    rw [data, sourceData]
    funext index; fin_cases index <;> simp [Drain.slots, Drain.source, Drain.target, slots, other]
  have finalStore : after.var = ((none, store.1.2), store.2) := by rw [localStoreEq, sourceVar]
  have afterEq : after = state (some (historyLabel 0)) ((none, store.1.2), store.2)
      input archive query (captured.reverse ++ result) := by
    rcases after with ⟨label, vars, contents⟩
    change label = some (historyLabel 0) at returned
    change vars = ((none, store.1.2), store.2) at finalStore
    change contents = _ at finalSlots
    subst label; subst vars; subst contents
    rfl
  refine ⟨run, ?_, chain, ?_, length.trans sourceLength⟩
  · simpa only [Native.Inline.cfg, Drain.state, initialSlots, Option.map_some,
      Option.getD_some, copiedState, Prod.eta] using head
  · simpa only [afterEq] using last

/-- Every consumed history byte is physically restored by archive2→input0.
The unmatched suffix stays on input0 throughout; query/result are carried. -/
theorem history_return_runs (input archive query result : List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some (historyLabel 0)) store input archive query result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some (state (some doneLabel) ((none, store.1.2), store.2)
        (archive.reverse ++ input) [] query result) ∧
      run.length = archive.length + 3 := by
  let other := slots input archive query result
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    Drain.drain_runs false archive input other store.1
  obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
    Native.Inline.actual_return_trace historyLabel doneLabel (Drain.program false) program
      (by intro label; rfl) source
      (Drain.state false (some 0) store.1 archive input other)
      sourceFinal store.2 sourceHead sourceChain sourceLast sourceHalt
  have initialSlots : Drain.slots false archive input other = slots input archive query result := by
    funext index; fin_cases index <;> simp [Drain.slots, Drain.source, Drain.target, slots, other]
  have finalSlots : after.stk = slots (archive.reverse ++ input) [] query result := by
    rw [data, sourceData]
    funext index; fin_cases index <;> simp [Drain.slots, Drain.source, Drain.target, slots, other]
  have finalStore : after.var = ((none, store.1.2), store.2) := by rw [localStoreEq, sourceVar]
  have afterEq : after = state (some doneLabel) ((none, store.1.2), store.2)
      (archive.reverse ++ input) [] query result := by
    rcases after with ⟨label, vars, contents⟩
    change label = some doneLabel at returned
    change vars = ((none, store.1.2), store.2) at finalStore
    change contents = _ at finalSlots
    subst label; subst vars; subst contents
    rfl
  refine ⟨run, ?_, chain, ?_, length.trans sourceLength⟩
  · simpa only [Native.Inline.cfg, Drain.state, initialSlots, Option.map_some,
      Option.getD_some, state, Prod.eta] using head
  · simpa only [afterEq] using last

end PDROC.BitVM.Log.Lookup
