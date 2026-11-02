module

public import Paid.PDROC_BitVM_Log_Lookup_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.Log.Lookup

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Complete newest-first heap lookup by the actual fixed finite Bool-stack
program. Logical history/query parameters describe data, not control fields.
The returned route is assembled once from actual primitive component paths. -/

theorem lookup_route (newest : List HeapEvent) (query : ℕ)
    (archive result : List Bool) (store : Store) :
    ∃ finalStore : Store,
      Route (state (some gateLabel) store (newest.flatMap encodeEvent) archive (encodeNatBits query) result)
        (state none finalStore (archive.reverse ++ newest.flatMap encodeEvent) [] (encodeNatBits query)
          (valueBytes (lookupNewest newest query) ++ result))
        (100 * (newest.length + 1) * ((newest.flatMap encodeEvent).length + archive.length + 1)) ∧
      (Query.equality finalStore.1 && Query.recordTag finalStore.1) = (lookupNewest newest query).isSome := by
  induction newest generalizing archive store with
  | nil =>
    let eofStore := missing (setRecord store none)
    have eofPath := Route.edge (gate_eof archive (encodeNatBits query) result store)
    have finishPath := finish_route [] archive (encodeNatBits query) result eofStore
    have whole := eofPath.trans finishPath
    refine ⟨cleared eofStore, ?_, ?_⟩
    · simpa only [List.flatMap_nil, List.length_nil, List.nil_append, List.append_nil, lookupNewest, valueBytes] using
        whole.mono (large := 100 * (0 + 1) * (0 + archive.length + 1)) (by omega)
    · rfl
  | cons event older ih =>
    by_cases same : event.address = query
    · obtain ⟨finalStore, foundPath, foundFlag⟩ :=
        matched_record_route event query (older.flatMap encodeEvent) archive result store same
      refine ⟨finalStore, ?_, ?_⟩
      · have sameLookup : lookupNewest (event :: older) query = event.value := by
          simp only [lookupNewest, same, ↓reduceIte]
        simpa only [sameLookup, List.flatMap_cons] using foundPath.mono
          (large := 100 * ((event :: older).length + 1) *
            (((event :: older).flatMap encodeEvent).length + archive.length + 1)) (by
          simp only [List.length_cons, List.flatMap_cons, List.length_append]
          nlinarith)
      · simpa only [lookupNewest, same, ↓reduceIte] using foundFlag
    · obtain ⟨nextStore, scanPath⟩ :=
        unmatched_record_route event query (older.flatMap encodeEvent) archive result store same
      obtain ⟨finalStore, olderPath, olderFlag⟩ := ih ((encodeEvent event).reverse ++ archive) nextStore
      have whole := scanPath.trans olderPath
      have restored : ((encodeEvent event).reverse ++ archive).reverse ++ older.flatMap encodeEvent =
          archive.reverse ++ (event :: older).flatMap encodeEvent := by
        simp only [List.reverse_append, List.reverse_reverse, List.flatMap_cons, List.append_assoc]
      have sameLookup : lookupNewest (event :: older) query = lookupNewest older query := by
        simp only [lookupNewest, Ne.symm same, ↓reduceIte]
      refine ⟨finalStore, ?_, ?_⟩
      · simpa only [sameLookup, restored, List.flatMap_cons] using whole.mono
          (large := 100 * ((event :: older).length + 1) *
            (((event :: older).flatMap encodeEvent).length + archive.length + 1)) (by
          simp only [List.length_cons, List.flatMap_cons, List.length_append, List.length_reverse]
          nlinarith)
      · simpa only [sameLookup] using olderFlag

/-- One actual lookup macro run. Both returned Cell bytes and the complete
old history/query are real stack data. An absent or tombstoned address leaves
the result stack unchanged and reports false, as required for a failed load. -/
theorem lookup_runs (newest : List HeapEvent) (query : ℕ) (result : List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some gateLabel) store (newest.flatMap encodeEvent) [] (encodeNatBits query) result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧
      after.stk = slots (newest.flatMap encodeEvent) [] (encodeNatBits query)
        (valueBytes (lookupNewest newest query) ++ result) ∧
      (Query.equality after.var.1 && Query.recordTag after.var.1) = (lookupNewest newest query).isSome ∧
      run.length ≤ 100 * (newest.length + 1) * ((newest.flatMap encodeEvent).length + 1) := by
  obtain ⟨finalStore, path, flag⟩ := lookup_route newest query [] result store
  obtain ⟨run, head, chain, last, length⟩ := path
  let after := state none finalStore (newest.flatMap encodeEvent) [] (encodeNatBits query)
    (valueBytes (lookupNewest newest query) ++ result)
  refine ⟨run, after, head, chain, ?_, rfl, rfl, rfl, flag, ?_⟩
  · simpa only [List.reverse_nil, List.nil_append] using last
  · simpa only [List.length_nil, Nat.add_zero] using length

/-- Chronological source histories use exactly the same selected macro
path. The newest-first specification is only a theorem identifying its answer. -/
theorem chronological_lookup_runs (events : List HeapEvent) (query : ℕ) (result : List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some gateLabel) store (encodeHistory events) [] (encodeNatBits query) result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧
      after.stk = slots (encodeHistory events) [] (encodeNatBits query) (valueBytes (lookup events query) ++ result) ∧
      (Query.equality after.var.1 && Query.recordTag after.var.1) = (lookup events query).isSome ∧
      run.length ≤ 100 * (events.length + 1) * ((encodeHistory events).length + 1) := by
  simpa only [encodeHistory, lookup_eq_newest, List.length_reverse] using
    lookup_runs events.reverse query result store

end PDROC.BitVM.Log.Lookup
