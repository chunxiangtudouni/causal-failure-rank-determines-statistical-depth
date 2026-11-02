module

public import Structure.PA06_A19Prepare_CompactParents035Ord
public import Structure.PA06_A19Prepare_RawHeader039Entry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Ord source data on the same actual raw→Header execution. The true
Sorted candidate and retained membership are produced by035Ord, then the
actual104-op cache frame preserves every physical ord word at address>=16.
The old weak WordParents ABI is retained, and no candidate oracle is an
input to this producer. The code and original bounds are unchanged. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRawHeader039Ord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open PA06A19PrepareRawHeader039Body (headerProgram headerClock heapWords wordRun_add)
open PA06A19PrepareRawHeader039Entry (headerStart headerSuffix program front front_length program_layout)
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
        PA06A19PrepareCompactParents035Ord.OrdData q full after ∧
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
  obtain ⟨parentClock, bound, _nativeEntry, _inverse, _registers, parents, ordinal, _ordTransport, _wordPrefix, prefixSafe⟩ :=
    PA06A19PrepareCompactParents035Ord.parent_entry q full (headerSuffix tail) initialUsed hq hlaminar hend hcode
  let before := packingRun rom (program tail) parentClock initial
  have startPC : before.pc.toNat = 5 * (front tail).length := by
    rw [front_length]
    exact parents.2.1
  have header := PA06A19PrepareRawHeader039Body.embedded_header q full initialUsed t hq
    (front tail) tail before startPC parents.1
    (by rw [program_layout]; exact hend) (by rw [program_layout]; exact hcode)
  dsimp only at header
  rw [program_layout, front_length] at header
  refine ⟨parentClock, bound, ?_⟩
  dsimp only
  refine ⟨parents, ordinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wordRun_add]
    exact PA06A19PrepareCompactParents035Ord.ord_data_frame q full before _ header.2.2.2.1 ordinal
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


end PaperProofs.Structure.LaminarTree.PA06A19PrepareRawHeader039Ord
