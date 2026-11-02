module

public import Structure.PA06_A19Prepare_CompactParents035Cards
public import Structure.PA06_A19Prepare_RawHeader039Entry

set_option autoImplicit false
set_option warningAsError true

/-! The same raw parent clock and the actual original 104-op Header body.
Both ord and all-candidate card data are transported by the actual heap
frame. No source-card premise, new ROM, new code or restarted run occurs. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRawHeader039Cards

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open PA06A19PrepareRawHeader039Body (headerProgram headerClock heapWords wordRun_add)
open PA06A19PrepareRawHeader039Entry (headerStart headerSuffix program front front_length program_layout)

/- Keep projection over an abstract state and use the exact PC label in
WordParents. Transfer the separate Nat label equality explicitly, rather
than asking definitional equality to normalize labels under Nat.mul. -/
private theorem wordParents_pc (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q))
    (parents : PA06A19PrepareCompactParents035Entry.WordParents q full state) :
    state.pc.toNat = 5 * PA06A19PrepareCompactParents035Entry.inputStart := by
  exact parents.2.1

private theorem inputStart_headerStart :
    PA06A19PrepareCompactParents035Entry.inputStart = headerStart := by
  rfl

private theorem wordParents_active (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q))
    (parents : PA06A19PrepareCompactParents035Entry.WordParents q full state) :
    state.halted = false := by
  exact parents.1

theorem raw_header_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (initialUsed : Finset (Fin q)) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (program tail))) :
    ∃ parentClock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full,
      let bits := indexWidth 32 full.length q
      let rom := CompactControllerClaims.controllerInput q full initialUsed
      let initial := natInitial.toWord bits
      let before := packingRun rom (program tail) parentClock initial
      let after := packingRun rom (program tail) (parentClock + headerClock full.length q) initial
      PA06A19PrepareCompactParents035Entry.WordParents q full before ∧
        PA06A19PrepareCompactParents035Ord.OrdData q full before ∧
        PA06A19PrepareCompactParents035Cards.CardData q full before ∧
        PA06A19PrepareCompactParents035Ord.OrdData q full after ∧
        PA06A19PrepareCompactParents035Cards.CardData q full after ∧
        after.pc.toNat = 5 * (headerStart + 104) ∧ after.halted = false ∧
        PA06A19PrepareRuntimePacked016.Header q after.heap ∧
        (∀ address : BitVec bits, 16 ≤ address.toNat → after.heap address = before.heap address) ∧
        ∀ count < parentClock + headerClock full.length q,
          let current := packingRun rom (program tail) count initial
          current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
              packingAccessFits rom (heapWords full.length q (prepareNormalization q full).indexed.nodes.size) current op := by
  let bits := indexWidth 32 full.length q
  let rom := CompactControllerClaims.controllerInput q full initialUsed
  let initial := natInitial.toWord bits
  let t := (prepareNormalization q full).indexed.nodes.size
  obtain ⟨parentClock, bound, _nativeEntry, _inverse, _registers, parents, ordinal, cards,
      _ordTransport, _wordPrefix, prefixSafe⟩ :=
    PA06A19PrepareCompactParents035Cards.parent_entry q full (headerSuffix tail) initialUsed hq hlaminar hend hcode
  let before := packingRun rom (program tail) parentClock initial
  have startPC : before.pc.toNat = 5 * (front tail).length := by
    rw [front_length]
    exact (wordParents_pc q full before parents).trans
      (congrArg (fun start : Nat => 5 * start) inputStart_headerStart)
  have startActive : before.halted = false := wordParents_active q full before parents
  have header := PA06A19PrepareRawHeader039Body.embedded_header q full initialUsed t hq
    (front tail) tail before startPC startActive
    (by rw [program_layout]; exact hend) (by rw [program_layout]; exact hcode)
  dsimp only at header
  rw [program_layout, front_length] at header
  refine ⟨parentClock, bound, ?_⟩
  dsimp only
  refine ⟨parents, ordinal, cards, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wordRun_add]
    exact PA06A19PrepareCompactParents035Ord.ord_data_frame q full before _ header.2.2.2.1 ordinal
  · rw [wordRun_add]
    exact PA06A19PrepareCompactParents035Cards.card_data_frame q full before _ header.2.2.2.1 cards
  · rw [wordRun_add]
    exact header.1
  · rw [wordRun_add]
    exact header.2.1
  · rw [wordRun_add]
    exact header.2.2.1
  · rw [wordRun_add]
    exact header.2.2.2.1
  · intro count hc
    by_cases early : count < parentClock
    · have safe := prefixSafe count early
      dsimp only at safe
      obtain ⟨active, window, op, decoded, access⟩ := safe
      refine ⟨active, window, op, decoded, ?_⟩
      exact PA06A19PrepareRawHeader039Body.packingAccess_mono rom
        (PA06A19PrepareCompactWord008.linearLimit full.length q) (heapWords full.length q t)
        (PA06A19PrepareRawHeader039Body.compact_room full.length q t hq) _ op access
    · have eq : count = parentClock + (count - parentClock) := by omega
      have safe := header.2.2.2.2 (count - parentClock) (by omega)
      rw [eq, wordRun_add]
      exact safe

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRawHeader039Cards
