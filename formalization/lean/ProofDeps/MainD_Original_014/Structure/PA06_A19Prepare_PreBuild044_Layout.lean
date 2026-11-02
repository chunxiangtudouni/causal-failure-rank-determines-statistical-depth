module

public import Structure.PA06_A19Prepare_RawSequence043
public import Structure.PA06_A19Prepare_ChildrenCache023_Word
public import Structure.PA06_A19Prepare_ClearVM045

set_option autoImplicit false
set_option warningAsError true

/-! Candidate only. This module has not been compiled by its author.
All four segments execute in the same containing program, with an arbitrary
tail. The actual instruction boundaries are 1444,1588,1617,1639. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild044

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims

abbrev bits (q : Nat) (full : List (Finset (Fin q))) := indexWidth 32 full.length q
abbrev capacity (q : Nat) (full : List (Finset (Fin q))) :=
  capacityWords 8192 full.length q (treeSize q full)
abbrev packedWords (q : Nat) (full : List (Finset (Fin q))) :=
  packedCapacityWords q (capacity q full) (bits q full)
abbrev controlBase (q : Nat) (full : List (Finset (Fin q))) :=
  PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full) (packedWords q full)
abbrev allocation (q : Nat) (full : List (Finset (Fin q))) :=
  PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)

def suffix (tail : List PackingOp) : List PackingOp :=
  PA06A19PrepareChildrenCache023.programAt 1444 ++
    PA06A19PrepareClearVM045.programAt 1588 ++ tail

def program (tail : List PackingOp) : List PackingOp :=
  PA06A19PrepareRawSequence043.program (suffix tail)

def rawFront (tail : List PackingOp) : List PackingOp :=
  PA06A19PrepareRawSequence043.front (suffix tail) ++
    PA06A19PrepareRuntimeLayout026.sequence 1310

def clearFront (tail : List PackingOp) : List PackingOp :=
  rawFront tail ++ PA06A19PrepareChildrenCache023.programAt 1444

theorem rawFront_length (tail : List PackingOp) : (rawFront tail).length = 1444 := by
  simp only [rawFront, List.length_append, PA06A19PrepareRawSequence043.front_length,
    PA06A19PrepareRuntimeLayout026.sequence_length]

theorem clearFront_length (tail : List PackingOp) : (clearFront tail).length = 1588 := by
  simp only [clearFront, List.length_append, rawFront_length,
    PA06A19PrepareChildrenCache023.programAt_length]

theorem raw_layout (tail : List PackingOp) : rawFront tail ++ suffix tail = program tail := by
  have h := PA06A19PrepareRawSequence043.program_layout (suffix tail)
  rw [PA06A19PrepareRawSequence043.front_length] at h
  simpa only [rawFront, program, List.append_assoc] using h

theorem cache_layout (tail : List PackingOp) :
    rawFront tail ++ PA06A19PrepareChildrenCache023.programAt (rawFront tail).length ++
      (PA06A19PrepareClearVM045.programAt 1588 ++ tail) = program tail := by
  rw [rawFront_length]
  simpa only [suffix, List.append_assoc] using raw_layout tail

theorem clear_layout (tail : List PackingOp) :
    clearFront tail ++ PA06A19PrepareClearVM045.programAt (clearFront tail).length ++ tail = program tail := by
  rw [clearFront_length]
  simpa only [clearFront, rawFront_length, List.append_assoc] using cache_layout tail

theorem program_length (tail : List PackingOp) : (program tail).length = 1639 + tail.length := by
  simp only [program, PA06A19PrepareRawSequence043.program_length, suffix,
    List.length_append, PA06A19PrepareChildrenCache023.programAt_length,
    PA06A19PrepareClearVM045.programAt_length]
  omega

theorem cache_code (tail : List PackingOp) :
    PA06A19PrepareChildrenCache023.CodeAt (program tail) 1444 := by
  have h := PA06A19PrepareChildrenCache023.append_code (rawFront tail)
    (PA06A19PrepareClearVM045.programAt 1588 ++ tail)
  rw [cache_layout, rawFront_length] at h
  exact h

theorem prepared_size (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    treeSize q full = PA06A19PrepareChildrenCache023.preparedSize q full := by
  simp only [treeSize, Nat.ne_of_gt hq, ite_false]

theorem children_controlBase (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PrepareChildrenCache023.actualControlBase q full = controlBase q full := by
  simp only [PA06A19PrepareChildrenCache023.actualControlBase,
    PA06A19PrepareChildrenCache023.actualPackedWords, controlBase, packedWords, capacity,
    bits, prepared_size q full hq]

theorem children_allocation (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PrepareChildrenCache023.actualAllocation q full = allocation q full := by
  simp only [PA06A19PrepareChildrenCache023.actualAllocation,
    PA06A19PrepareChildrenCache023.actualPackedWords, allocation,
    prepared_size q full hq, PA06A19PrepareControlBank017.allocation,
    PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass,
    PA06A19PrepareRuntimeHeader019.heapWords]
  omega

def clockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  PA06A19PrepareCompactCandidates007.parentClockBound q full +
    PA06A19PrepareRawHeader039Body.headerClock full.length q +
    PA06A19PrepareRuntimeLayout026.sequenceClock full.length q +
    PA06A19PrepareChildrenCache023.totalSteps q full +
    PA06A19PrepareClearVM045.clock full.length q (treeSize q full)

end PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild044
