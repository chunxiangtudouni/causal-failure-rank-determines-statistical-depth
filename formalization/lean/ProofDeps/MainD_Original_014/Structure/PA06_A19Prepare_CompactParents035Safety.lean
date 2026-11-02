module

public import Structure.PA06_A19Prepare_CompactParents035Pieces
public import Structure.PA06_A19Prepare_CompactRetention020PairLoop
public import PaperProofs.Structure.RawCandidateParentWordSafety

/-! Actual-code safety assembly for the fixed parent pieces and its
dynamic pair-scan call.  Data bounds for the small pieces are proved
separately; whole-loop composition must discharge them at real boundaries. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Safety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM
open RawIncidenceScanSafety (NatAccessFits)
abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit
open RawCandidateParentWordChunks (Chunk chunkCode chunkOffset chunkLength chunkLead)

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 32 full.length q) state ∧
    ∃ offset < 361, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (h : SafePoint q full containing start state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    Fits (indexWidth 32 full.length q) state.pc := by
  obtain ⟨offset, hoff, hp, _⟩ := h.2
  rw [hp]
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
  (hbound : start + 361 ≤ containing.length)
  (hcode : ∀ position < 361, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem chunk_run_pc (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count < chunkLength chunk) :
    (natRun (rawIncidenceROM q full) containing count state).pc = 5 * (start + chunkOffset chunk + count) := by
  have hsmall : count ≤ chunkLength chunk - 1 := by omega
  have heq : (chunkCode start chunk).take count = (chunkLead start chunk).take count := by
    rw [RawCandidateParentWordChunks.chunkLead, List.take_take, min_eq_left hsmall]
  have hno : ∀ op ∈ (chunkCode start chunk).take count, NoJump op := by
    rw [heq]
    intro op hop
    exact RawCandidateParentWordChunks.chunk_lead_noJump start chunk op (List.mem_of_mem_take hop)
  rw [RawCandidateParentWordChunks.chunk_run_prefix _ containing start hbound hcode chunk state hpc ha count hc.le,
    runOps_pc _ _ _ hno, List.length_take_of_le (by rw [RawCandidateParentWordChunks.chunk_code_length]; omega), hpc]
  omega

theorem chunk_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hf : ∀ count ≤ chunkLength chunk, RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state))
    (hx : ∀ count < chunkLength chunk, NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)
      ((chunkCode start chunk).getD count paddingOp)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  constructor
  · intro count hc
    have hr := RawCandidateParentWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
      chunk state hpc ha count hc.le
    have hp := chunk_run_pc q full containing start hbound hcode chunk state hpc ha count hc
    have hs := RawCandidateParentWordChunks.chunk_span chunk
    refine ⟨?_, chunkOffset chunk + count, by omega, ?_, ?_,
      (chunkCode start chunk).getD count paddingOp, ?_, ?_⟩
    · rw [hr]
      exact hf count hc.le
    · rw [hp]
      omega
    · rw [hr, runOps_halted, ha]
    · rw [hp, natFetch_body containing (start + chunkOffset chunk + count) (by omega), decode_encode]
      have hh := (hcode (chunkOffset chunk + count) (by omega)).trans
        (RawCandidateParentWordChunks.chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ paddingOp (by omega)] at hh
      simpa only [Nat.add_assoc] using congrArg some hh
    · rw [hr]
      exact hx count hc
  · rw [RawCandidateParentWordChunks.chunk_run_prefix _ containing start hbound hcode
      chunk state hpc ha (chunkLength chunk) le_rfl]
    exact hf _ le_rfl

omit hbound hcode in

theorem pair_point (state : NatState)
    (hp : PA06A19PrepareCompactRetention020.SafePoint q full containing (start + 105) state) :
    SafePoint q full containing start state := by
  obtain ⟨hr, localOffset, hlocal, pc, active, op, hd, hx⟩ := hp
  refine ⟨hr, 105 + localOffset, by omega, ?_, active, op, hd, ?_⟩
  · rw [pc]; omega
  · exact access_mono (rawIncidenceROM q full) 8 (linearLimit full.length q) state op
      (by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega) hx

theorem pair_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + 105)) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (RawCandidatePairScan.totalSteps full.length left.val right.val q) ∧
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing
        (RawCandidatePairScan.totalSteps full.length left.val right.val q) state) := by
  have hs := RawCandidateParentWordSafety.pair_slice containing start hbound hcode
  have hend' : Fits (indexWidth 32 full.length q) (5 * ((start + 105) + 125)) :=
    lt_of_le_of_lt (by omega) hend
  have hp := PA06A19PrepareCompactRetention020PairLoop.scan_nat_safe q full containing (start + 105) hs.1 hs.2
    left right state hpc ha hl hr hf hend'
  exact ⟨fun count hc => pair_point q full containing start _ (hp.1 count hc), hp.2⟩

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Safety


