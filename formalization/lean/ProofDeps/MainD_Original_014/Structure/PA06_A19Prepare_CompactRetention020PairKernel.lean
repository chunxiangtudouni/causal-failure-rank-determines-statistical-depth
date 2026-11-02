module

public import Structure.PA06_A19Prepare_CompactRetention020PairCore
public import Structure.PA06_A19Prepare_NodeBit015

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000

/-! The two REAL raw-incidence calls inside the original125-op PairScan.
The only new numerical interface comes from015's full-width short-path
proof. Original query correctness, program slices and path semantics are
reused. This module supplies no ord-cache/answer oracle and allocates only
the eight PairScan scratch words. It does not prove the whole loop yet. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020PairKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareCompactRetention020 (SafePoint)
open RawCandidatePairScan (programAt)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 125 ≤ containing.length)
  (hcode : ∀ position < 125, containing.getD (start + position) RawCandidatePairScanWord.paddingOp =
    (programAt start).getD position RawCandidatePairScanWord.paddingOp)

include hbound hcode

theorem kernel_safe (offset : Nat) (hoffset : offset = 27 ∨ offset = 65)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (ha : state.halted = false)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val) :
    let count := RawCandidateIncidenceWord.steps full.length candidate.val tool.val
    let result := natRun (rawIncidenceROM q full) containing count state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state count ∧
      RegistersFit (indexWidth 32 full.length q) result ∧
      RawCandidateIncidenceBlock.ReturnedActive (start + offset) state result
        (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  have hoff : offset ≤ 65 := by rcases hoffset with rfl | rfl <;> omega
  have slice := RawCandidatePairScanWord.kernel_slice containing start hbound hcode offset hoffset
  have he : Fits (indexWidth 32 full.length q) (5 * ((start + offset) + 32)) :=
    lt_of_le_of_lt (by omega) hend
  have returned := RawCandidateIncidenceBlock.query q full containing (start + offset) slice.1 (by
    intro position hp
    have hh := slice.2 position hp
    rw [List.getD_eq_getElem containing RawCandidatePairScanWord.paddingOp (by omega),
      List.getD_eq_getElem _ RawCandidatePairScanWord.paddingOp
        (by rw [RawCandidateIncidenceBlock.programAt_length]; exact hp)] at hh
    exact hh) candidate tool state hpc ha hcandidate htool
  have pathEq (count : Nat) (hc : count ≤ RawCandidateIncidenceWord.steps full.length candidate.val tool.val) :
      natRun (rawIncidenceROM q full) containing count state =
        runOps (rawIncidenceROM q full)
          ((RawCandidateIncidenceWord.pathOps (start + offset) full.length candidate.val tool.val).take count) state :=
    RawCandidateIncidenceWord.natRun_prefix_eq q full containing (start + offset) slice.1 slice.2
      candidate tool state hpc ha hcandidate htool count hc
  have registers (count : Nat) (hc : count ≤ RawCandidateIncidenceWord.steps full.length candidate.val tool.val) :
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing count state) := by
    rw [pathEq count hc]
    exact PA06A19PrepareNodeBit015.path_prefix_registersFit_wide 32 q full (by decide)
      (start + offset) candidate tool state hfit he hcandidate htool count hc
  refine ⟨?_, registers _ le_rfl, returned⟩
  intro count hc
  have pc := RawCandidateIncidenceWord.natRun_prefix_pc q full containing (start + offset) slice.1 slice.2
    candidate tool state hpc ha hcandidate htool count hc.le
  let index := (RawCandidateIncidenceWord.pathIndices full.length candidate.val tool.val).getD count 32
  have hi : index < 32 := RawCandidateIncidenceWord.path_index_lt _ _ _ _ hc
  let op := (RawCandidateIncidenceWord.pathOps (start + offset) full.length candidate.val tool.val).getD count
    RawCandidatePairScanWord.paddingOp
  refine ⟨registers count hc.le, offset + index, by omega, ?_, ?_, op, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using pc
  · rw [pathEq count hc.le, runOps_halted, ha]
  · rw [pc]
    change PackingOp.decode (natFetch containing (5 * ((start + offset) + index))) = some op
    rw [natFetch_body containing ((start + offset) + index) (by omega), decode_encode]
    have hh := (slice.2 index hi).trans (RawCandidateIncidenceWord.path_op_matches (start + offset)
      full.length candidate.val tool.val count hc)
    rw [List.getD_eq_getElem containing RawCandidatePairScanWord.paddingOp (by omega)] at hh
    exact congrArg some hh
  · rw [pathEq count hc.le]
    exact RawCandidateIncidenceWord.path_prefix_accessFits q full (start + offset) 8
      candidate tool state hcandidate htool count hc

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020PairKernel
