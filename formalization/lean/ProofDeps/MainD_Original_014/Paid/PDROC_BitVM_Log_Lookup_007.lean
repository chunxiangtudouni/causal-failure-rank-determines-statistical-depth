module

public import Paid.PDROC_BitVM_Log_Lookup_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.Lookup

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! The address scanner, Bool comparison and unmatched-Cell skip return
into the ONE fixed lookup program. All paths below are selected from actual
source paths and mapped by Native.Inline, including the real return step. -/

def addressState (label : Option Label) (store : Store) (address input archive query result : List Bool) : State :=
  ⟨label, store, Query.slots address query [] (slots input archive query result)⟩

theorem capture_empty_slots (input archive query result : List Bool) :
    Capture.slots input [] archive [] (slots input archive query result) = slots input archive query result := by
  funext index; fin_cases index <;> simp [Capture.slots, slots]

theorem capture_address_slots (address input archive query result : List Bool) :
    Capture.slots input address archive [] (slots input archive query result) =
      Query.slots address query [] (slots input archive query result) := by
  funext index; fin_cases index <;> simp [Capture.slots, Query.slots, slots]

theorem query_empty_slots (input archive query result : List Bool) :
    Query.slots [] query [] (slots input archive query result) = slots input archive query result := by
  funext index; fin_cases index <;> simp [Query.slots, slots]

theorem skip_empty_slots (input archive query result : List Bool) :
    CellSkip.slots input [] archive (slots input archive query result) = slots input archive query result := by
  funext index; fin_cases index <;> simp [CellSkip.slots, slots]

/-- A canonical field is read and archived; its actual bytes are available
on address stack1. Query and result remain real caller data. -/
theorem capture_return_runs (address : ℕ) (input archive query result : List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some (captureLabel 0)) store
        (encodeNatBits address ++ input) archive query result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some (addressState (some (compareLabel 0)) ((none, store.1.2), store.2)
        (encodeNatBits address) input ((encodeNatBits address).reverse ++ archive) query result) ∧
      run.length = 4 * natBits address + 6 := by
  let other := slots input archive query result
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    Capture.officialNat_capture_runs address input archive other store.1
  obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
    Native.Inline.actual_return_trace captureLabel (compareLabel 0) Capture.program program
      (by intro label; rfl) source
      (Capture.state (some 0) store.1 (encodeNatBits address ++ input) [] archive [] other)
      sourceFinal store.2 sourceHead sourceChain sourceLast sourceHalt
  have initialSlots : Capture.slots (encodeNatBits address ++ input) [] archive [] other =
      slots (encodeNatBits address ++ input) archive query result := by
    funext index; fin_cases index <;> simp [Capture.slots, slots, other]
  have finalSlots : after.stk = Query.slots (encodeNatBits address) query []
      (slots input ((encodeNatBits address).reverse ++ archive) query result) := by
    rw [data, sourceData]
    funext index; fin_cases index <;> simp [Capture.slots, Query.slots, slots, other]
  have finalStore : after.var = ((none, store.1.2), store.2) := by rw [localStoreEq, sourceVar]
  have afterEq : after = addressState (some (compareLabel 0)) ((none, store.1.2), store.2)
      (encodeNatBits address) input ((encodeNatBits address).reverse ++ archive) query result := by
    rcases after with ⟨label, vars, contents⟩
    change label = some (compareLabel 0) at returned
    change vars = ((none, store.1.2), store.2) at finalStore
    change contents = _ at finalSlots
    subst label; subst vars; subst contents
    rfl
  refine ⟨run, ?_, chain, ?_, length.trans sourceLength⟩
  · simpa only [Native.Inline.cfg, Capture.state, initialSlots, Option.map_some, Option.getD_some,
      state, Prod.eta] using head
  · simpa only [afterEq] using last

/-- The equality flag is obtained from actual Bool comparisons and canonical
codec injectivity; logical Nat equality is only the result proposition. -/
theorem compare_return_runs (address query : ℕ) (input archive result : List Bool) (store : Store) :
    ∃ (run : List State) (finalStore : Store),
      run.head? = some (addressState (some (compareLabel 0)) store
        (encodeNatBits address) input archive (encodeNatBits query) result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some (state (some decideLabel) finalStore input archive (encodeNatBits query) result) ∧
      Query.equality finalStore.1 = decide (address = query) ∧
      Query.recordTag finalStore.1 = Query.recordTag store.1 ∧
      run.length ≤ 4 * natBits address + 7 := by
  let other := slots input archive (encodeNatBits query) result
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceMatch, sourceTag, sourceData, sourceLength⟩ :=
    Query.nat_address_compare_runs address query other store.1
  obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
    Native.Inline.actual_return_trace compareLabel decideLabel Query.program program
      (by intro label; rfl) source
      (Query.state (some 0) store.1 (encodeNatBits address) (encodeNatBits query) [] other)
      sourceFinal store.2 sourceHead sourceChain sourceLast sourceHalt
  have finalSlots : after.stk = slots input archive (encodeNatBits query) result := by
    rw [data, sourceData]
    exact query_empty_slots input archive (encodeNatBits query) result
  have afterEq : after = state (some decideLabel) (sourceFinal.var, store.2)
      input archive (encodeNatBits query) result := by
    rcases after with ⟨label, vars, contents⟩
    change label = some decideLabel at returned
    change vars = (sourceFinal.var, store.2) at localStoreEq
    change contents = _ at finalSlots
    subst label; subst vars; subst contents
    rfl
  refine ⟨run, (sourceFinal.var, store.2), ?_, chain, ?_, sourceMatch, sourceTag, ?_⟩
  · simpa only [Native.Inline.cfg, Query.state, Option.map_some, Option.getD_some,
      addressState, other, Prod.eta] using head
  · simpa only [afterEq] using last
  · rw [length]; exact sourceLength

/-- An unmatched store consumes its real Cell encoding and archives every
byte, with no host Cell decoder in the finite transition code. -/
theorem skip_return_runs (value : Cell) (input archive query result : List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some (skipLabel CellSkip.startLabel)) store
        (encodeCellBits value ++ input) archive query result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some (state (some gateLabel) ((none, store.1.2), store.2) input
        ((encodeCellBits value).reverse ++ archive) query result) ∧
      run.length ≤ (encodeCellBits value).length + 6 := by
  let other := slots input archive query result
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    CellSkip.skip_runs value input archive other store.1
  obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
    Native.Inline.actual_return_trace skipLabel gateLabel CellSkip.program program
      (by intro label; rfl) source
      (CellSkip.state (some CellSkip.startLabel) store.1 (encodeCellBits value ++ input) [] archive other)
      sourceFinal store.2 sourceHead sourceChain sourceLast sourceHalt
  have initialSlots : CellSkip.slots (encodeCellBits value ++ input) [] archive other =
      slots (encodeCellBits value ++ input) archive query result := by
    funext index; fin_cases index <;> simp [CellSkip.slots, slots, other]
  have finalSlots : after.stk = slots input ((encodeCellBits value).reverse ++ archive) query result := by
    rw [data, sourceData]
    funext index; fin_cases index <;> simp [CellSkip.slots, slots, other]
  have finalStore : after.var = ((none, store.1.2), store.2) := by rw [localStoreEq, sourceVar]
  have afterEq : after = state (some gateLabel) ((none, store.1.2), store.2) input
      ((encodeCellBits value).reverse ++ archive) query result := by
    rcases after with ⟨label, vars, contents⟩
    change label = some gateLabel at returned
    change vars = ((none, store.1.2), store.2) at finalStore
    change contents = _ at finalSlots
    subst label; subst vars; subst contents
    rfl
  refine ⟨run, ?_, chain, ?_, ?_⟩
  · simpa only [Native.Inline.cfg, CellSkip.state, initialSlots, Option.map_some,
      Option.getD_some, state, Prod.eta] using head
  · simpa only [afterEq] using last
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.Lookup
