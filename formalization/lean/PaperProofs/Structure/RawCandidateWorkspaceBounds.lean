module

public import PaperProofs.Structure.RawCandidateWorkspaceInit
public import PaperProofs.Structure.RawTreeSerialization
public import PaperProofs.Structure.RawTreeOutputWords

/-! Numeric bounds for the existing raw-candidate workspace.  These are
word/address facts only, not actual-prefix access or allocation proofs.
The original serialized output starts at zero and overwrites heap cell 8. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceBounds

open AlgorithmClaims RawTreePreprocessingClaims RawCandidateWorkspaceInit RawTreeSerialization

/-- A common bound for the current scalar slots, all six candidate-sized
arrays, and fixed engineering offsets.  It imposes no input restriction. -/
def workspaceLimit (N q : Nat) : Nat := workspaceBase N q + 8 * candidateCount N q + 8192

theorem workspaceLimit_fits (N q : Nat) : Fits (indexWidth 16 N q) (workspaceLimit N q) := by
  apply fits_indexWidth_of_lt_power
  let base := N + q + 2
  have hbase : 2 ≤ base := by dsimp [base]; omega
  have hsquare : 4 ≤ base ^ 2 := Nat.pow_le_pow_left hbase 2
  have hpower : 16384 ≤ base ^ 14 := Nat.pow_le_pow_left hbase 14
  have hproduct : candidateCount N q * q ≤ base ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul
      (show candidateCount N q ≤ base by dsimp [candidateCount, base]; omega)
      (show q ≤ base by dsimp [base]; omega)
  have hlinear : candidateCount N q ≤ base ^ 2 := by
    have hm : candidateCount N q ≤ base := by dsimp [candidateCount, base]; omega
    have hb : base ≤ base ^ 2 := by nlinarith
    exact hm.trans hb
  calc
    workspaceLimit N q ≤ 16 * base ^ 2 + 8208 := by
      unfold workspaceLimit workspaceBase
      nlinarith
    _ < base ^ 2 * 16384 := by nlinarith
    _ ≤ base ^ 2 * base ^ 14 := Nat.mul_le_mul_left _ hpower
    _ = base ^ 16 := by rw [← pow_add]

theorem workspace_address_fits (N q address : Nat) (haddress : address ≤ workspaceLimit N q) :
    Fits (indexWidth 16 N q) address := haddress.trans_lt (workspaceLimit_fits N q)

theorem workspace_offset_fits (N q offset : Nat) (hoffset : offset ≤ 8 * candidateCount N q + 8192) :
    Fits (indexWidth 16 N q) (workspaceBase N q + offset) := by
  apply workspace_address_fits
  unfold workspaceLimit
  omega

/-- Covers card/keep/ord/inverse and later parent/degree arrays without
coupling this numeric module to any particular runtime block. -/
theorem workspace_arraySlot_fits (N q factor index : Nat) (hfactor : factor ≤ 6)
    (hindex : index ≤ candidateCount N q) :
    Fits (indexWidth 16 N q) (workspaceBase N q + candidateCount N q * factor + 4 + index) := by
  have hproduct := Nat.mul_le_mul_left (candidateCount N q) hfactor
  apply workspace_address_fits
  unfold workspaceLimit
  omega

theorem workspace_nodeCount_fits (N q : Nat) :
    Fits (indexWidth 16 N q) (workspaceBase N q + 4 + 4 * candidateCount N q) := by
  apply workspace_address_fits
  unfold workspaceLimit
  omega

theorem workspace_parentDegree_end_fits (N q : Nat) :
    Fits (indexWidth 16 N q) (workspaceBase N q + 5 + 6 * candidateCount N q) := by
  apply workspace_address_fits
  unfold workspaceLimit
  omega

theorem serialize_length_lt_workspaceBase (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (serializeROM (givenTreeROM q full)).length < workspaceBase full.length q := by
  have hlength := serialize_givenTreeROM_length_le q full hq hlaminar
  unfold workspaceBase candidateCount
  omega

theorem output_position_lt_workspaceBase (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (position : Nat)
    (hposition : position < (serializeROM (givenTreeROM q full)).length) :
    position < workspaceBase full.length q :=
  hposition.trans (serialize_length_lt_workspaceBase q full hq hlaminar)

theorem workspace_not_in_output (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (address : Nat)
    (haddress : workspaceBase full.length q ≤ address) :
    ¬ address < (serializeROM (givenTreeROM q full)).length := by
  have hlength := serialize_length_lt_workspaceBase q full hq hlaminar
  omega

/-- Physical addresses do not alias either, once the allocated cache
address is within the proved numeric bound.  Unbounded natural addresses
are deliberately not identified with unbounded physical words. -/
theorem workspace_word_ne_output (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (address position : Nat)
    (haddress : workspaceBase full.length q ≤ address)
    (hbound : address ≤ workspaceLimit full.length q)
    (hposition : position < (serializeROM (givenTreeROM q full)).length) :
    BitVec.ofNat (indexWidth 16 full.length q) address ≠
      BitVec.ofNat (indexWidth 16 full.length q) position := by
  have hp := output_position_lt_workspaceBase q full hq hlaminar position hposition
  have hfit := workspace_address_fits full.length q address hbound
  have hpfit : Fits (indexWidth 16 full.length q) position := (hp.trans_le haddress).trans hfit
  intro heq
  have heqNat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt hpfit] at heqNat
  omega

theorem eight_lt_serialize_length (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    8 < (serializeROM (givenTreeROM q full)).length := by
  obtain ⟨root, _hroot⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have ht : 0 < (prepareNormalization q full).indexed.nodes.size := (Nat.zero_le root.val).trans_lt root.isLt
  have htq : (prepareNormalization q full).indexed.nodes.size ≤
      (prepareNormalization q full).indexed.nodes.size * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (prepareNormalization q full).indexed.nodes.size hq
  rw [serializeROM_length, PhysicalROM.size, givenTreeROM_input_length, givenTreeROM_internal_length]
  omega

theorem candidateCount_lt_workspaceBase (N q : Nat) (hq : 0 < q) :
    candidateCount N q < workspaceBase N q := by
  have hproduct : candidateCount N q ≤ candidateCount N q * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (candidateCount N q) hq
  unfold workspaceBase
  nlinarith

theorem serialize_word_lt_workspaceBase (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (value : Nat)
    (hvalue : value ∈ serializeROM (givenTreeROM q full)) : value < workspaceBase full.length q := by
  have hlength := serialize_length_lt_workspaceBase q full hq hlaminar
  have hlen := serializeROM_length (givenTreeROM q full)
  have hcount := candidateCount_lt_workspaceBase full.length q hq
  simp only [serializeROM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvalue
  rcases hvalue with (((rfl | rfl | rfl) | hin) | hint) | hchild
  · exact lt_of_le_of_lt (by rw [hlen, PhysicalROM.size]; omega) hlength
  · exact lt_of_le_of_lt (by rw [hlen, PhysicalROM.size]; omega) hlength
  · exact lt_of_le_of_lt (by rw [hlen, PhysicalROM.size]; omega) hlength
  · exact (RawTreeOutputWords.givenTreeROM_word_le q full .input value hin).trans_lt hcount
  · exact (RawTreeOutputWords.givenTreeROM_word_le q full .internal value hint).trans_lt hcount
  · exact (RawTreeOutputWords.givenTreeROM_word_le q full .children value hchild).trans_lt hcount

/-- The original output necessarily replaces the old B pointer in heap8
by a different value.  Output code must recompute B or preserve it elsewhere. -/
theorem serialize_word_eight_ne_workspaceBase (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (serializeROM (givenTreeROM q full)).getD 8 0 ≠ workspaceBase full.length q := by
  have hposition := eight_lt_serialize_length q full hq
  rw [List.getD_eq_getElem _ 0 hposition]
  exact (serialize_word_lt_workspaceBase q full hq hlaminar _ (List.getElem_mem hposition)).ne

end PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceBounds
