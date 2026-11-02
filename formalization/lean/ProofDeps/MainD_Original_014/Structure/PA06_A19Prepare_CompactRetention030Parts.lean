module

public import Structure.PA06_A19Prepare_CompactRetention027Pieces

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Composition interfaces for the SAME398-op retention program. All eight
small pieces are supplied by020/027; the original125-op dynamic PairScan
is injected with its proven8-word scratch allocation. All qualifiers are
ordinary source-cell data at actual execution boundaries, not hSafe or
old-width register bounds. The Nat retention kernel is unchanged. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Parts

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety RawCandidateRetentionRAM
open RawCandidateRetentionWordChunks (Chunk chunkCode chunkOffset chunkLength)

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit
abbrev SafePoint := PA06A19PrepareCompactRetention020Args.SafePoint

def Needs (q : Nat) (full : List (Finset (Fin q))) (chunk : Chunk) (state : NatState) : Prop :=
  state.heap 8 = 16 ∧ match chunk with
    | .initialize => True
    | .outerTest => state.heap 16 = full.length + q + 1 ∧ state.heap 17 ≤ full.length + q + 1
    | .cardArgs => state.heap 17 ≤ full.length + q + 1
    | .afterCard => state.heap 1 ≤ full.length + q + 1 ∧ state.heap 4 ≤ q
    | .innerTest => state.heap 16 = full.length + q + 1 ∧ state.heap 18 ≤ full.length + q + 1
    | .pairArgs => state.heap 17 ≤ full.length + q + 1 ∧ state.heap 18 ≤ full.length + q + 1
    | .innerTail => state.heap 5 ≤ q ∧ state.heap 6 ≤ q ∧ state.heap 19 ≤ 1 ∧ state.heap 18 ≤ full.length + q + 1
    | .finish => state.heap 16 = full.length + q + 1 ∧ state.heap 1 ≤ full.length + q + 1 ∧
        state.heap 17 ≤ full.length + q + 1 ∧ state.heap 19 ≤ 1

theorem point_pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (point : SafePoint q full containing start state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    Fits (indexWidth 32 full.length q) state.pc := by
  obtain ⟨offset, hoff, pc, _⟩ := point.2
  rw [pc]
  exact lt_of_le_of_lt (by omega) hend

private theorem access_mono (rom : PhysicalROM) (small large : Nat) (state : NatState) (op : PackingOp)
    (hroom : small ≤ large) (access : NatAccessFits rom small state op) : NatAccessFits rom large state op := by
  cases op with
  | base op =>
    cases op with
    | subtract target left right => trivial
    | base instruction =>
      cases instruction <;> simp only [NatAccessFits, AccessFits] at access ⊢
      all_goals first | exact access | exact access.trans_le hroom
  | arithmetic operation target left right => trivial
  | jumpIfZero condition target => trivial

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem piece_run (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing (chunkLength chunk) state =
      runOps (rawIncidenceROM q full) (chunkCode start chunk) state := by
  rw [RawCandidateRetentionWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
    chunk state hpc ha _ le_rfl,
    List.take_of_length_le (by rw [RawCandidateRetentionWordChunks.chunk_code_length])]

theorem piece_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (needs : Needs q full chunk state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  cases chunk with
  | «initialize» =>
    exact PA06A19PrepareCompactRetention020Args.piece_safe q full containing start hbound hcode
      .initialize state hpc ha hr needs hend
  | outerTest =>
    exact PA06A19PrepareCompactRetention020Args.piece_safe q full containing start hbound hcode
      .outerTest state hpc ha hr needs hend
  | cardArgs =>
    exact PA06A19PrepareCompactRetention020Args.piece_safe q full containing start hbound hcode
      .cardArgs state hpc ha hr needs hend
  | afterCard =>
    exact PA06A19PrepareCompactRetention027Pieces.piece_safe q full containing start hbound hcode
      .afterCard state hpc ha hr needs hend
  | innerTest =>
    exact PA06A19PrepareCompactRetention020Args.piece_safe q full containing start hbound hcode
      .innerTest state hpc ha hr needs hend
  | pairArgs =>
    exact PA06A19PrepareCompactRetention020Args.piece_safe q full containing start hbound hcode
      .pairArgs state hpc ha hr needs hend
  | innerTail =>
    exact PA06A19PrepareCompactRetention027Pieces.piece_safe q full containing start hbound hcode
      .innerTail state hpc ha hr needs hend
  | finish =>
    exact PA06A19PrepareCompactRetention027Pieces.piece_safe q full containing start hbound hcode
      .finish state hpc ha hr needs hend

omit hbound hcode in
theorem pair_point (offset : Nat) (hoffset : offset = 29 ∨ offset = 207) (state : NatState)
    (point : PA06A19PrepareCompactRetention020.SafePoint q full containing (start + offset) state) :
    SafePoint q full containing start state := by
  obtain ⟨registers, localOffset, hlocal, pc, active, op, decoded, access⟩ := point
  refine ⟨registers, offset + localOffset, ?_, ?_, active, op, decoded, ?_⟩
  · rcases hoffset with rfl | rfl <;> omega
  · rw [pc]
    omega
  · exact access_mono (rawIncidenceROM q full) 8 (linearLimit full.length q) state op
      (by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega) access

theorem pair_safe (offset : Nat) (hoffset : offset = 29 ∨ offset = 207)
    (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (RawCandidatePairScan.totalSteps full.length left.val right.val q) ∧
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing
        (RawCandidatePairScan.totalSteps full.length left.val right.val q) state) := by
  have slice := RawCandidateRetentionWordSafety.pair_slice containing start hbound hcode offset hoffset
  have hend' : Fits (indexWidth 32 full.length q) (5 * (start + offset + 125)) := by
    apply lt_of_le_of_lt _ hend
    rcases hoffset with rfl | rfl <;> omega
  have safe := PA06A19PrepareCompactRetention020PairLoop.scan_nat_safe q full containing (start + offset) slice.1 slice.2
    left right state hpc ha hl hr hfit hend'
  exact ⟨fun count hc => pair_point q full containing start offset hoffset _ (safe.1 count hc), safe.2⟩

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Parts
