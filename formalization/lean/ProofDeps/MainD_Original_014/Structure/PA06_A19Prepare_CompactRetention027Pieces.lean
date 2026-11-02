module

public import Structure.PA06_A19Prepare_CompactRetention027Updates

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Three genuine retention update pieces, from ordinary source-cell bounds
to encoded execution/prefix safety and exact outputs. No completed card,
keep or whole-run safety result is supplied as a qualification. The full
398-op loop and the006 initialization handoff are still separate steps. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention027Pieces

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety RawCandidateRetentionRAM
open RawCandidateRetentionWordChunks (Chunk chunkCode chunkLength chunkOffset)
open PA06A19PrepareCompactRetention027

inductive Update where
  | afterCard | innerTail | finish

def Update.original : Update → Chunk
  | .afterCard => .afterCard
  | .innerTail => .innerTail
  | .finish => .finish

def Needs (q : Nat) (full : List (Finset (Fin q))) (piece : Update) (state : NatState) : Prop :=
  state.heap 8 = 16 ∧ match piece with
    | .afterCard => state.heap 1 ≤ full.length + q + 1 ∧ state.heap 4 ≤ q
    | .innerTail => state.heap 5 ≤ q ∧ state.heap 6 ≤ q ∧ state.heap 19 ≤ 1 ∧
        state.heap 18 ≤ full.length + q + 1
    | .finish => state.heap 16 = full.length + q + 1 ∧ state.heap 1 ≤ full.length + q + 1 ∧
        state.heap 17 ≤ full.length + q + 1 ∧ state.heap 19 ≤ 1

theorem prefix_fit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (piece : Update) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (needs : Needs q full piece state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (count : Nat) (hc : count ≤ chunkLength piece.original) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start piece.original).take count) state) := by
  cases piece with
  | afterCard => exact afterCard_prefix_fit q full state hr needs.1 needs.2.1 needs.2.2 count hc
  | innerTail =>
    exact innerTail_prefix_fit q full start state hr needs.1 needs.2.1 needs.2.2.1 needs.2.2.2.1
      needs.2.2.2.2 hend count hc
  | finish =>
    exact finishCandidate_prefix_fit q full start state hr needs.1 needs.2.1 needs.2.2.1 needs.2.2.2.1
      needs.2.2.2.2 hend count hc

theorem prefix_access (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (piece : Update) (state : NatState)
    (needs : Needs q full piece state) (count : Nat) (hc : count < chunkLength piece.original) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start piece.original).take count) state)
      ((chunkCode start piece.original).getD count paddingOp) := by
  cases piece with
  | afterCard => exact afterCard_prefix_access q full state needs.1 needs.2.1 count hc
  | innerTail => exact innerTail_prefix_access q full start state needs.1 count hc
  | finish => exact finishCandidate_prefix_access q full start state needs.1 needs.2.1 needs.2.2.1 count hc

abbrev SafePoint := PA06A19PrepareCompactRetention020Args.SafePoint

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem piece_run (piece : Update) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset piece.original)) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing (chunkLength piece.original) state =
      runOps (rawIncidenceROM q full) (chunkCode start piece.original) state := by
  rw [RawCandidateRetentionWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
    piece.original state hpc ha _ le_rfl, List.take_of_length_le
      (by rw [RawCandidateRetentionWordChunks.chunk_code_length])]

theorem piece_safe (piece : Update) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset piece.original)) (ha : state.halted = false)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (needs : Needs q full piece state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength piece.original) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength piece.original) state) := by
  constructor
  · intro count hc
    have run := RawCandidateRetentionWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
      piece.original state hpc ha count hc.le
    have pc := RawCandidateRetentionWordSafety.chunk_run_pc q full containing start hbound hcode
      piece.original state hpc ha count hc
    have span := RawCandidateRetentionWordChunks.chunk_span piece.original
    refine ⟨?_, chunkOffset piece.original + count, by omega, ?_, ?_,
      (chunkCode start piece.original).getD count paddingOp, ?_, ?_⟩
    · rw [run]
      exact prefix_fit q full start piece state hr needs hend count hc.le
    · rw [pc]
      omega
    · rw [run, runOps_halted, ha]
    · rw [pc, natFetch_body containing (start + chunkOffset piece.original + count) (by omega), decode_encode]
      have hh := (hcode (chunkOffset piece.original + count) (by omega)).trans
        (RawCandidateRetentionWordChunks.chunk_slice start piece.original count hc)
      rw [List.getD_eq_getElem _ paddingOp (by omega)] at hh
      simpa only [Nat.add_assoc] using congrArg some hh
    · rw [run]
      exact prefix_access q full start piece state needs count hc
  · rw [RawCandidateRetentionWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
      piece.original state hpc ha (chunkLength piece.original) le_rfl]
    exact prefix_fit q full start piece state hr needs hend _ le_rfl

/-- Full-width Word prefixes of these same actual update pieces. -/
theorem piece_word (piece : Update) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset piece.original)) (ha : state.halted = false)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (needs : Needs q full piece state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ chunkLength piece.original) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 32 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q) := by
  have safe := piece_safe q full containing start hbound hcode piece state hpc ha hr needs hend
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  have point := safe.1 k (by omega)
  have registers := point.1
  obtain ⟨offset, hoff, pc, _⟩ := point.2
  refine ⟨registers, ?_⟩
  rw [pc]
  exact lt_of_le_of_lt (by omega) hend

/-- Exact existing Nat outputs, attached to the real encoded update run. -/
theorem afterCard_output (state : NatState) (hpc : state.pc = 5 * (start + 154))
    (ha : state.halted = false) (hptr : state.heap 8 = 16) :
    (natRun (rawIncidenceROM q full) containing 26 state).heap =
      Function.update (Function.update (Function.update state.heap
        (cardAddress 16 (state.heap 1)) (state.heap 4)) 19 (min 1 (state.heap 4))) 18 (state.heap 1 + 1) := by
  have run := piece_run q full containing start hbound hcode .afterCard state hpc ha
  change natRun (rawIncidenceROM q full) containing 26 state = runOps (rawIncidenceROM q full) afterCard state at run
  rw [run]
  exact afterCard_heap (rawIncidenceROM q full) 16 state hptr (by decide)

theorem innerTail_output (state : NatState) (hpc : state.pc = 5 * (start + 332))
    (ha : state.halted = false) (hptr : state.heap 8 = 16) :
    let actual := natRun (rawIncidenceROM q full) containing 32 state
    actual.heap = Function.update (Function.update state.heap 19
      (if state.heap 5 + state.heap 6 = 0 then 0 else state.heap 19)) 18 (state.heap 18 + 1) ∧
      actual.pc = 5 * (start + 180) ∧ actual.halted = false := by
  dsimp only
  have run := piece_run q full containing start hbound hcode .innerTail state hpc ha
  change natRun (rawIncidenceROM q full) containing 32 state = runOps (rawIncidenceROM q full) (innerTail start) state at run
  rw [run]
  exact ⟨innerTail_heap (rawIncidenceROM q full) start 16 state hptr (by decide),
    (innerTail_control (rawIncidenceROM q full) start state).1,
    (innerTail_control (rawIncidenceROM q full) start state).2.trans ha⟩

theorem finish_output (state : NatState) (hpc : state.pc = 5 * (start + 364))
    (ha : state.halted = false) (hptr : state.heap 8 = 16) :
    let actual := natRun (rawIncidenceROM q full) containing 34 state
    actual.heap = Function.update (Function.update state.heap
      (keepAddress 16 (state.heap 16) (state.heap 1)) (state.heap 19)) 17 (state.heap 17 + 1) ∧
      actual.pc = 5 * (start + 6) ∧ actual.halted = false := by
  dsimp only
  have run := piece_run q full containing start hbound hcode .finish state hpc ha
  change natRun (rawIncidenceROM q full) containing 34 state = runOps (rawIncidenceROM q full) (finishCandidate start) state at run
  rw [run]
  exact ⟨finishCandidate_heap (rawIncidenceROM q full) start 16 state hptr (by decide),
    (finishCandidate_control (rawIncidenceROM q full) start state).1,
    (finishCandidate_control (rawIncidenceROM q full) start state).2.trans ha⟩

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention027Pieces
