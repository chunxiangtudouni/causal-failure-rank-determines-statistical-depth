module

public import Paid.PDROC_BitVM_Log_Lookup_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.Log.Lookup

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! One-record correctness for the actual finite lookup machine. These
logical lists and Nat addresses specify its paths, never its control store.
A matching tombstone takes the immediate restoration branch. -/

def valueBytes : Option Cell → List Bool
  | none => []
  | some value => encodeCellBits value

theorem unmatched_record_route (event : HeapEvent) (query : ℕ)
    (input archive result : List Bool) (store : Store) (different : event.address ≠ query) :
    ∃ finalStore : Store,
      Route (state (some gateLabel) store (encodeEvent event ++ input) archive (encodeNatBits query) result)
        (state (some gateLabel) finalStore input ((encodeEvent event).reverse ++ archive)
          (encodeNatBits query) result)
        (20 * ((encodeEvent event).length + 1)) := by
  rcases event with ⟨address, value⟩
  cases value with
  | none =>
    obtain ⟨compared, readPath, matched, tag⟩ := read_record_route false address query input archive result store
    have noMatch : Query.equality compared.1 = false := matched.trans (by simp [different])
    have dispatched := Route.edge (decide_older (slots input
      ((encodeNatBits address).reverse ++ false :: archive) (encodeNatBits query) result) compared noMatch tag)
    have whole := readPath.trans dispatched
    refine ⟨compared, ?_⟩
    have normalized : (encodeNatBits address).reverse ++ false :: archive =
        (encodeEvent ⟨address, none⟩).reverse ++ archive := by
      simp only [encodeEvent, List.reverse_cons, List.append_assoc, List.singleton_append]
    simpa only [state, encodeEvent, List.cons_append, normalized] using whole.mono
      (large := 20 * ((encodeEvent ⟨address, none⟩).length + 1)) (by
      simp only [encodeEvent, List.length_cons, nat_word_length]
      omega)
  | some value =>
    obtain ⟨compared, readPath, matched, tag⟩ :=
      read_record_route true address query (encodeCellBits value ++ input) archive result store
    have noMatch : Query.equality compared.1 = false := matched.trans (by simp [different])
    have dispatched := Route.edge (decide_skip (slots (encodeCellBits value ++ input)
      ((encodeNatBits address).reverse ++ true :: archive) (encodeNatBits query) result) compared noMatch tag)
    obtain ⟨skipTrace, skipHead, skipChain, skipLast, skipLength⟩ :=
      skip_return_runs value input ((encodeNatBits address).reverse ++ true :: archive)
        (encodeNatBits query) result compared
    have skipPath : Route (state (some (skipLabel CellSkip.startLabel)) compared
        (encodeCellBits value ++ input) ((encodeNatBits address).reverse ++ true :: archive)
        (encodeNatBits query) result)
        (state (some gateLabel) (cleared compared) input
          ((encodeCellBits value).reverse ++ ((encodeNatBits address).reverse ++ true :: archive))
          (encodeNatBits query) result)
        ((encodeCellBits value).length + 6) :=
      ⟨skipTrace, skipHead, skipChain, skipLast, skipLength⟩
    have whole := readPath.trans (dispatched.trans skipPath)
    refine ⟨cleared compared, ?_⟩
    have normalized : (encodeCellBits value).reverse ++ ((encodeNatBits address).reverse ++ true :: archive) =
        (encodeEvent ⟨address, some value⟩).reverse ++ archive := by
      simp only [encodeEvent, List.reverse_cons, List.reverse_append, List.append_assoc, List.singleton_append]
    simpa only [encodeEvent, List.cons_append, List.append_assoc, normalized] using whole.mono
      (large := 20 * ((encodeEvent ⟨address, some value⟩).length + 1)) (by
      simp only [encodeEvent, List.length_cons, List.length_append, nat_word_length]
      omega)

theorem matched_record_route (event : HeapEvent) (query : ℕ)
    (input archive result : List Bool) (store : Store) (same : event.address = query) :
    ∃ finalStore : Store,
      Route (state (some gateLabel) store (encodeEvent event ++ input) archive (encodeNatBits query) result)
        (state none finalStore (archive.reverse ++ (encodeEvent event ++ input)) []
          (encodeNatBits query) (valueBytes event.value ++ result))
        (50 * ((encodeEvent event).length + input.length + archive.length + 1)) ∧
      (Query.equality finalStore.1 && Query.recordTag finalStore.1) = event.value.isSome := by
  rcases event with ⟨address, value⟩
  change address = query at same
  cases value with
  | none =>
    obtain ⟨compared, readPath, matched, tag⟩ := read_record_route false address query input archive result store
    have yesMatch : Query.equality compared.1 = true := matched.trans (by simp [same])
    have dispatched := Route.edge (decide_tombstone (slots input
      ((encodeNatBits address).reverse ++ false :: archive) (encodeNatBits query) result) compared yesMatch tag)
    have finishPath := finish_route input ((encodeNatBits address).reverse ++ false :: archive)
      (encodeNatBits query) result compared
    have whole := readPath.trans (dispatched.trans finishPath)
    refine ⟨cleared compared, ?_, ?_⟩
    · have restored : ((encodeNatBits address).reverse ++ false :: archive).reverse ++ input =
          archive.reverse ++ (encodeEvent ⟨address, none⟩ ++ input) := by
        simp only [encodeEvent, List.reverse_append, List.reverse_cons, List.reverse_reverse,
          List.append_assoc, List.singleton_append]
      simpa only [encodeEvent, List.cons_append, restored, valueBytes, List.nil_append] using whole.mono
        (large := 50 * ((encodeEvent ⟨address, none⟩).length + input.length + archive.length + 1)) (by
        simp only [encodeEvent, List.length_cons, List.length_append, List.length_reverse, nat_word_length]
        omega)
    · simp only [cleared_equality, cleared_tag, yesMatch, tag, Bool.true_and, Option.isSome_none]
  | some value =>
    obtain ⟨compared, readPath, matched, tag⟩ :=
      read_record_route true address query (encodeCellBits value ++ input) archive result store
    have yesMatch : Query.equality compared.1 = true := matched.trans (by simp [same])
    have dispatched := Route.edge (decide_store (slots (encodeCellBits value ++ input)
      ((encodeNatBits address).reverse ++ true :: archive) (encodeNatBits query) result) compared yesMatch tag)
    obtain ⟨copyTrace, copyHead, copyChain, copyLast, copyLength⟩ :=
      copy_return_runs value input ((encodeNatBits address).reverse ++ true :: archive)
        (encodeNatBits query) result compared
    let fullArchive := (encodeCellBits value).reverse ++ ((encodeNatBits address).reverse ++ true :: archive)
    have copyPath : Route (state (some (copyLabel CellCopy.startLabel)) compared
        (encodeCellBits value ++ input) ((encodeNatBits address).reverse ++ true :: archive)
        (encodeNatBits query) result)
        (copiedState (some (valueLabel 0)) (cleared compared) (encodeCellBits value).reverse input
          fullArchive (encodeNatBits query) result)
        ((encodeCellBits value).length + 6) :=
      ⟨copyTrace, copyHead, copyChain, copyLast, copyLength⟩
    obtain ⟨valueTrace, valueHead, valueChain, valueLast, valueLength⟩ :=
      value_return_runs (encodeCellBits value).reverse input fullArchive (encodeNatBits query) result (cleared compared)
    have valuePath : Route (copiedState (some (valueLabel 0)) (cleared compared) (encodeCellBits value).reverse
        input fullArchive (encodeNatBits query) result)
        (state (some (historyLabel 0)) (cleared compared) input fullArchive (encodeNatBits query)
          (encodeCellBits value ++ result))
        ((encodeCellBits value).length + 3) := by
      refine ⟨valueTrace, valueHead, valueChain, ?_, ?_⟩
      · simpa only [List.reverse_reverse, cleared] using valueLast
      · simpa only [List.length_reverse] using valueLength.le
    have finishPath := finish_route input fullArchive (encodeNatBits query)
      (encodeCellBits value ++ result) (cleared compared)
    have whole := readPath.trans (dispatched.trans (copyPath.trans (valuePath.trans finishPath)))
    refine ⟨cleared compared, ?_, ?_⟩
    · have restored : fullArchive.reverse ++ input = archive.reverse ++ (encodeEvent ⟨address, some value⟩ ++ input) := by
        simp only [fullArchive, encodeEvent, List.reverse_append, List.reverse_cons, List.reverse_reverse,
          List.cons_append, List.append_assoc, List.nil_append]
      simpa only [encodeEvent, List.cons_append, List.append_assoc, restored, valueBytes, cleared_cleared] using
        whole.mono
          (large := 50 * ((encodeEvent ⟨address, some value⟩).length + input.length + archive.length + 1)) (by
          simp only [fullArchive, encodeEvent, List.length_cons, List.length_append, List.length_reverse, nat_word_length]
          omega)
    · simp only [cleared_equality, cleared_tag, yesMatch, tag, Bool.true_and, Option.isSome_some]

end PDROC.BitVM.Log.Lookup
