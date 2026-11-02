module

public import Paid.PDROC_BitVM_Log_Lookup_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.Lookup

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Lookup-local path contracts only package an actual list of configurations.
Composition joins these very paths at their identical actual endpoint. -/

def Route (before after : State) (limit : ℕ) : Prop :=
  ∃ run : List State, run.head? = some before ∧
    run.IsChain (fun a b => TM2.step program a = some b) ∧
    run.getLast? = some after ∧ run.length ≤ limit

theorem Route.mono {before after : State} {small large : ℕ}
    (path : Route before after small) (bound : small ≤ large) : Route before after large := by
  obtain ⟨run, head, chain, last, length⟩ := path
  exact ⟨run, head, chain, last, length.trans bound⟩

theorem Route.edge {before after : State} (edge : TM2.step program before = some after) :
    Route before after 2 := by
  refine ⟨[before, after], rfl, ?_, rfl, le_rfl⟩
  exact List.isChain_cons_cons.mpr ⟨edge, List.isChain_singleton after⟩

theorem Route.trans {before middle after : State} {leftLimit rightLimit : ℕ}
    (left : Route before middle leftLimit) (right : Route middle after rightLimit) :
    Route before after (leftLimit + rightLimit) := by
  obtain ⟨leftTrace, leftHead, leftChain, leftLast, leftLength⟩ := left
  obtain ⟨rightTrace, rightHead, rightChain, rightLast, rightLength⟩ := right
  cases rightTrace with
  | nil => simp only [List.head?_nil, reduceCtorEq] at rightHead
  | cons first rest =>
    cases rest with
    | nil =>
      have firstMiddle : first = middle := Option.some.inj rightHead
      have firstAfter : first = after := Option.some.inj rightLast
      have same : middle = after := firstMiddle.symm.trans firstAfter
      exact ⟨leftTrace, leftHead, leftChain, leftLast.trans (congrArg some same), by omega⟩
    | cons second tail =>
      let joined := leftTrace ++ (first :: second :: tail).tail
      have joinedHead : joined.head? = some before := by
        simp only [joined, List.head?_append, leftHead, Option.some_or]
      have joinedChain : joined.IsChain (fun a b => TM2.step program a = some b) :=
        TwoStack.join_chain leftTrace (first :: second :: tail) middle
          leftChain rightChain leftLast rightHead
      have notOne : (first :: second :: tail).length ≠ 1 := by simp
      have joinedLast : joined.getLast? = some after := by
        simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
          rightLast, Option.some_or]
      refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
      simp only [joined, List.length_append, List.length_tail]
      omega

def cleared (store : Store) : Store := ((none, store.1.2), store.2)

theorem cleared_equality (store : Store) : Query.equality (cleared store).1 = Query.equality store.1 := rfl
theorem cleared_tag (store : Store) : Query.recordTag (cleared store).1 = Query.recordTag store.1 := rfl
theorem cleared_cleared (store : Store) : cleared (cleared store) = cleared store := rfl

/-- A real history drain followed by the actual final halt. In particular,
no host reverse or restoration operation is put into the machine code. -/
theorem finish_route (input archive query result : List Bool) (store : Store) :
    Route (state (some (historyLabel 0)) store input archive query result)
      (state none (cleared store) (archive.reverse ++ input) [] query result)
      (archive.length + 5) := by
  obtain ⟨run, head, chain, last, length⟩ := history_return_runs input archive query result store
  have restore : Route (state (some (historyLabel 0)) store input archive query result)
      (state (some doneLabel) (cleared store) (archive.reverse ++ input) [] query result)
      (archive.length + 3) := ⟨run, head, chain, last, length.le⟩
  exact restore.trans (Route.edge (done_halt (archive.reverse ++ input) [] query result (cleared store)))

/-- The record tag is read from input, its address is captured, every address
Bool is compared, and the query is restored before dispatch. The postcondition
identifies the result via codec injectivity, never a host comparison step. -/
theorem read_record_route (tag : Bool) (address query : ℕ)
    (input archive result : List Bool) (store : Store) :
    ∃ finalStore : Store,
      Route (state (some gateLabel) store (tag :: (encodeNatBits address ++ input))
        archive (encodeNatBits query) result)
        (state (some decideLabel) finalStore input
          ((encodeNatBits address).reverse ++ tag :: archive) (encodeNatBits query) result)
        (8 * natBits address + 15) ∧
      Query.equality finalStore.1 = decide (address = query) ∧
      Query.recordTag finalStore.1 = tag := by
  let tagStore := setTag (setRecord store (some tag)) tag
  have tagPath := Route.edge (gate_tag tag (encodeNatBits address ++ input) archive
    (encodeNatBits query) result store)
  obtain ⟨captureTrace, captureHead, captureChain, captureLast, captureLength⟩ :=
    capture_return_runs address input (tag :: archive) (encodeNatBits query) result tagStore
  have capturePath : Route (state (some (captureLabel 0)) tagStore
      (encodeNatBits address ++ input) (tag :: archive) (encodeNatBits query) result)
      (addressState (some (compareLabel 0)) (cleared tagStore) (encodeNatBits address)
        input ((encodeNatBits address).reverse ++ tag :: archive) (encodeNatBits query) result)
      (4 * natBits address + 6) :=
    ⟨captureTrace, captureHead, captureChain, captureLast, captureLength.le⟩
  obtain ⟨compareTrace, finalStore, compareHead, compareChain, compareLast, matched, recordTag, compareLength⟩ :=
    compare_return_runs address query input ((encodeNatBits address).reverse ++ tag :: archive)
      result (cleared tagStore)
  have comparePath : Route (addressState (some (compareLabel 0)) (cleared tagStore)
      (encodeNatBits address) input ((encodeNatBits address).reverse ++ tag :: archive)
      (encodeNatBits query) result)
      (state (some decideLabel) finalStore input
        ((encodeNatBits address).reverse ++ tag :: archive) (encodeNatBits query) result)
      (4 * natBits address + 7) :=
    ⟨compareTrace, compareHead, compareChain, compareLast, compareLength⟩
  refine ⟨finalStore, (tagPath.trans (capturePath.trans comparePath)).mono (by omega), matched, ?_⟩
  simpa only [cleared, tagStore, Query.recordTag, setTag] using recordTag

end PDROC.BitVM.Log.Lookup
