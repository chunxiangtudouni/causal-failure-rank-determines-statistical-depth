module

public import PaperProofs.Structure.RawCandidateRetentionWordChunks
public import PaperProofs.Structure.RawCandidatePairScanWord

/-! Actual-code safety assembly for the fixed retention pieces and its
two dynamic pair-scan calls.  Data bounds for the small pieces are proved
separately; whole-loop composition must discharge them at real boundaries. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateRetentionRAM
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateWorkspaceBounds (workspaceLimit)
open RawCandidateRetentionWordChunks (Chunk chunkCode chunkOffset chunkLength chunkLead)

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 16 full.length q) state ∧
    ∃ offset < 398, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (h : SafePoint q full containing start state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398))) :
    Fits (indexWidth 16 full.length q) state.pc := by
  obtain ⟨offset, hoff, hp, _⟩ := h.2
  rw [hp]
  exact lt_of_le_of_lt (by omega) hend

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem chunk_run_pc (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count < chunkLength chunk) :
    (natRun (rawIncidenceROM q full) containing count state).pc = 5 * (start + chunkOffset chunk + count) := by
  have hsmall : count ≤ chunkLength chunk - 1 := by omega
  have heq : (chunkCode start chunk).take count = (chunkLead start chunk).take count := by
    rw [RawCandidateRetentionWordChunks.chunkLead, List.take_take, min_eq_left hsmall]
  have hno : ∀ op ∈ (chunkCode start chunk).take count, NoJump op := by
    rw [heq]
    intro op hop
    exact RawCandidateRetentionWordChunks.chunk_lead_noJump start chunk op (List.mem_of_mem_take hop)
  rw [RawCandidateRetentionWordChunks.chunk_run_prefix _ containing start hbound hcode chunk state hpc ha count hc.le,
    runOps_pc _ _ _ hno, List.length_take_of_le (by rw [RawCandidateRetentionWordChunks.chunk_code_length]; omega), hpc]
  omega

theorem chunk_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hf : ∀ count ≤ chunkLength chunk, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state))
    (hx : ∀ count < chunkLength chunk, NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)
      ((chunkCode start chunk).getD count paddingOp)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  constructor
  · intro count hc
    have hr := RawCandidateRetentionWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
      chunk state hpc ha count hc.le
    have hp := chunk_run_pc q full containing start hbound hcode chunk state hpc ha count hc
    have hs := RawCandidateRetentionWordChunks.chunk_span chunk
    refine ⟨?_, chunkOffset chunk + count, by omega, ?_, ?_,
      (chunkCode start chunk).getD count paddingOp, ?_, ?_⟩
    · rw [hr]
      exact hf count hc.le
    · rw [hp]
      omega
    · rw [hr, runOps_halted, ha]
    · rw [hp, natFetch_body containing (start + chunkOffset chunk + count) (by omega), decode_encode]
      have hh := (hcode (chunkOffset chunk + count) (by omega)).trans
        (RawCandidateRetentionWordChunks.chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ paddingOp (by omega)] at hh
      simpa only [Nat.add_assoc] using congrArg some hh
    · rw [hr]
      exact hx count hc
  · rw [RawCandidateRetentionWordChunks.chunk_run_prefix _ containing start hbound hcode
      chunk state hpc ha (chunkLength chunk) le_rfl]
    exact hf _ le_rfl

omit hbound hcode in
private theorem getD_middle (left middle right : List PackingOp) (position : Nat) (hp : position < middle.length) :
    (left ++ middle ++ right).getD (left.length + position) paddingOp = middle.getD position paddingOp := by
  rw [List.getD_append (left ++ middle) right paddingOp _ (by simp only [List.length_append]; omega),
    List.getD_append_right left middle paddingOp _ (by omega), Nat.add_sub_cancel_left]

theorem pair_slice (offset : Nat) (hoffset : offset = 29 ∨ offset = 207) :
    start + offset + 125 ≤ containing.length ∧
      ∀ position < 125, containing.getD ((start + offset) + position) paddingOp =
        (RawCandidatePairScan.programAt (start + offset)).getD position paddingOp := by
  have hoff : offset + 125 ≤ 398 := by rcases hoffset with rfl | rfl <;> omega
  refine ⟨by omega, ?_⟩
  intro position hp
  have hlocal : (programAt start).getD (offset + position) paddingOp =
      (RawCandidatePairScan.programAt (start + offset)).getD position paddingOp := by
    rcases hoffset with rfl | rfl
    · let suffix := betweenScans start ++ RawCandidatePairScan.programAt (start + 207) ++ innerTail start ++ finishCandidate start
      have heq : programAt start = beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ suffix := by
        simp only [programAt, suffix, List.append_assoc]
      have hh := getD_middle (beforeCard start) (RawCandidatePairScan.programAt (start + 29)) suffix position
        (by rw [RawCandidatePairScan.programAt_length]; exact hp)
      rw [beforeCard_length] at hh
      rw [heq]
      exact hh
    · let codePrefix := beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ betweenScans start
      have hlength : codePrefix.length = 207 := by
        simp only [codePrefix, List.length_append, beforeCard_length, betweenScans_length, RawCandidatePairScan.programAt_length]
      have heq : programAt start = codePrefix ++ RawCandidatePairScan.programAt (start + 207) ++
          (innerTail start ++ finishCandidate start) := by
        simp only [programAt, codePrefix, List.append_assoc]
      have hh := getD_middle codePrefix (RawCandidatePairScan.programAt (start + 207)) (innerTail start ++ finishCandidate start)
        position (by rw [RawCandidatePairScan.programAt_length]; exact hp)
      rw [hlength] at hh
      rw [heq]
      exact hh
  have hh := (hcode (offset + position) (by omega)).trans hlocal
  simpa only [Nat.add_assoc] using hh

omit hbound hcode in
theorem pair_point (offset : Nat) (hoffset : offset = 29 ∨ offset = 207) (state : NatState)
    (hp : RawCandidatePairScanWord.SafePoint q full containing (start + offset) state) :
    SafePoint q full containing start state := by
  obtain ⟨hr, localOffset, hlocal, pc, active, op, hd, hx⟩ := hp
  refine ⟨hr, offset + localOffset, ?_, ?_, active, op, hd, hx⟩
  · rcases hoffset with rfl | rfl <;> omega
  · rw [pc]
    omega

theorem pair_safe (offset : Nat) (hoffset : offset = 29 ∨ offset = 207)
    (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (RawCandidatePairScan.totalSteps full.length left.val right.val q) ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing
        (RawCandidatePairScan.totalSteps full.length left.val right.val q) state) := by
  have hs := pair_slice containing start hbound hcode offset hoffset
  have hend' : Fits (indexWidth 16 full.length q) (5 * ((start + offset) + 125)) := by
    apply lt_of_le_of_lt _ hend
    rcases hoffset with rfl | rfl <;> omega
  have hp := RawCandidatePairScanWord.scan_nat_safe q full containing (start + offset) hs.1 hs.2
    left right state hpc ha hl hr hf hend'
  exact ⟨fun count hc => pair_point q full containing start offset hoffset _ (hp.1 count hc), hp.2⟩

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordSafety
