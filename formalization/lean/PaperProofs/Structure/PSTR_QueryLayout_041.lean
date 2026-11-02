module

public import PaperProofs.Structure.PSTR_HD_StaticHeap_020

/-! Shared internal A19 query ABI. These are addresses derived from ORIGINAL
capacity/metadata, not additional caller fields. Runtime materialization of
counts, the sentinel parent array and the active header remains separate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRQueryLayout

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims

def countsBase (workspace : Nat) : Nat := workspace + 16
def parentsBase (workspace size : Nat) : Nat := countsBase workspace + size
def header (workspace size : Nat) : Nat := parentsBase workspace size + size + 1
def goodFlags (workspace size : Nat) : Nat := header workspace size + 16
def badFlags (workspace size q : Nat) : Nat := goodFlags workspace size + q + 2
def childBase (workspace size q : Nat) : Nat := badFlags workspace size q + q + 2
def endpoint (workspace size q : Nat) : Nat := childBase workspace size q + size + 3

def logicalWorkspace {q : Nat} (full : List (Finset (Fin q))) (capWords : Nat) : Nat :=
  capWords + 2 + (staticMetadata q full).length

def physicalWorkspace {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat) : Nat :=
  PSTRStaticHeap.metadataAddress q capWords bits (staticMetadata q full).length

theorem endpoint_eq (workspace size q : Nat) :
    endpoint workspace size q = workspace + 3 * size + 2 * q + 40 := by
  unfold endpoint childBase badFlags goodFlags header parentsBase countsBase
  omega

theorem physical_logical_workspace {q : Nat} (full : List (Finset (Fin q)))
    (capWords bits : Nat) :
    physicalWorkspace full capWords bits =
      physicalHeaderWords + packedCapacityWords q capWords bits +
        (logicalWorkspace full capWords - capWords) := by
  unfold physicalWorkspace PSTRStaticHeap.metadataAddress logicalWorkspace
  omega

theorem logical_suffix_word {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q) (offset : Nat) :
    logicalHeap q capWords heap (logicalWorkspace full capWords + offset) =
      (heap (BitVec.ofNat bits (physicalWorkspace full capWords bits + offset))).toNat := by
  have hl : logicalWorkspace full capWords + offset =
      capWords + (2 + (staticMetadata q full).length + offset) := by unfold logicalWorkspace; omega
  rw [hl, PSTRStaticHeap.logical_suffix heap capWords _ hq]
  unfold physicalWorkspace PSTRStaticHeap.metadataAddress
  congr 3
  omega

theorem counts_parent_header_disjoint (workspace size : Nat) :
    workspace + 16 = countsBase workspace ∧
      countsBase workspace + size = parentsBase workspace size ∧
      parentsBase workspace size + size < header workspace size ∧
      workspace + 15 < countsBase workspace := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold header
    omega
  · unfold countsBase
    omega

theorem read_bounds (workspace size : Nat) :
    header workspace size < header workspace size + 4 ∧
      header workspace size + 1 < header workspace size + 4 ∧
      countsBase workspace + size ≤ header workspace size + 4 ∧
      parentsBase workspace size + size < header workspace size + 4 := by
  unfold header parentsBase countsBase
  omega

theorem flags_bounds (workspace size q : Nat) :
    header workspace size + 4 ≤ goodFlags workspace size ∧
      header workspace size + 4 < badFlags workspace size q ∧
      header workspace size + 7 < childBase workspace size q := by
  unfold childBase badFlags goodFlags
  omega

theorem flags_disjoint (workspace size q : Nat) (left right : Fin (q + 2)) :
    goodFlags workspace size + left.val ≠ badFlags workspace size q + right.val := by
  have hl := left.isLt
  have hr := right.isLt
  unfold badFlags
  omega

theorem endpoint_index64 {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat)
    (hq : 0 < q) (hl : LaminarSchedule full) :
    endpoint (physicalWorkspace full capWords bits) (treeSize q full) q ≤
      physicalHeaderWords + packedCapacityWords q capWords bits +
        64 * (full.length + q + treeSize q full + 1) := by
  rw [endpoint_eq]
  unfold physicalWorkspace PSTRStaticHeap.metadataAddress
  rw [PSTRStaticLayout.metadata_length q full hq, PSTRStaticLayout.edgeCount_eq q full hq hl]
  simp only [treeSize, ne_of_gt hq, ite_false, physicalHeaderWords]
  have hsub := Nat.sub_le (prepareNormalization q full).indexed.nodes.size 1
  omega

theorem endpoint_index_factor {q : Nat} (full : List (Finset (Fin q)))
    (capWords bits indexFactor : Nat) (hq : 0 < q) (hl : LaminarSchedule full) (hi : 64 ≤ indexFactor) :
    endpoint (physicalWorkspace full capWords bits) (treeSize q full) q ≤
      physicalHeaderWords + packedCapacityWords q capWords bits +
        indexFactor * (full.length + q + treeSize q full + 1) := by
  have hm := Nat.mul_le_mul_right (full.length + q + treeSize q full + 1) hi
  exact (endpoint_index64 full capWords bits hq hl).trans (Nat.add_le_add_left hm _)

end PaperProofs.Structure.LaminarTree.PSTRQueryLayout
