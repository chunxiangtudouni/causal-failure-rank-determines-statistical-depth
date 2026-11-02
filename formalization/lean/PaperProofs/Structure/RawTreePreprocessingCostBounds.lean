module

public import PaperProofs.Structure.RawTreePreprocessingNat
public import PaperProofs.Structure.RawCandidateWorkspaceBounds
public import PaperProofs.Structure.RawTreePreprocessingCodeBounds

/-! Full-program allocation, footprint, and numeric charging bounds.
The trace estimate includes ROM/code loading, heap initialization, and HALT.
It does not establish prefix access safety or word-execution correctness. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingCostBounds

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateWorkspaceInit
  RawCandidateWorkspaceBounds

def heapWords (N q : Nat) : Nat := workspaceLimit N q

theorem program_length : RawTreePreprocessingNat.program.length = 2089 := by
  rw [← RawTreePreprocessingNat.footer_program, List.length_append,
    RawTreePreprocessingNat.footerFront_length, RawTreePreprocessingNat.childrenStart_eq,
    RawTreeOutputFinalizeRAM.program_length]

theorem code_length : (packingCode RawTreePreprocessingNat.program).length = 10450 := by
  rw [packingCode_length, program_length]

theorem program_eq_codeProgram :
    RawTreePreprocessingNat.program = RawTreePreprocessingCodeBounds.program := by
  unfold RawTreePreprocessingNat.program RawTreePreprocessingNat.tail
  rw [RawTreePreprocessingNat.childrenStart_eq]
  rfl

theorem code_wordsFit (N q : Nat) :
    WordsFit (indexWidth 16 N q) (packingCode RawTreePreprocessingNat.program) := by
  rw [program_eq_codeProgram]
  exact RawTreePreprocessingCodeBounds.wordsFit N q

theorem heapWords_fits (N q : Nat) : Fits (indexWidth 16 N q) (heapWords N q) :=
  workspaceLimit_fits N q

theorem cache_address_lt_heapWords (N q address : Nat)
    (haddress : address ≤ workspaceBase N q + 5 + 6 * candidateCount N q) :
    address < heapWords N q := by
  unfold heapWords workspaceLimit
  omega

theorem output_length_lt_heapWords (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    (serializeROM (givenTreeROM q full)).length < heapWords full.length q := by
  have h := serialize_length_lt_workspaceBase q full hq hl
  unfold heapWords workspaceLimit
  omega

/-- The actual ROM+code+allocated heap size in the original word width.
This numeric statement has no oracle, answer, or execution premise. -/
theorem footprint_fits (q : Nat) (full : List (Finset (Fin q))) :
    Fits (indexWidth 16 full.length q)
      ((rawIncidenceROM q full).size + heapWords full.length q +
        (packingCode RawTreePreprocessingNat.program).length) := by
  rw [rawIncidenceROM_size, code_length]
  apply fits_indexWidth_of_lt_power
  let base := full.length + q + 2
  have hb : 2 ≤ base := by dsimp only [base]; omega
  have hsq : 4 ≤ base ^ 2 := Nat.pow_le_pow_left hb 2
  have hpower : 16384 ≤ base ^ 14 := Nat.pow_le_pow_left hb 14
  have hprod : candidateCount full.length q * q ≤ base ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul
      (show candidateCount full.length q ≤ base by dsimp only [candidateCount, base]; omega)
      (show q ≤ base by dsimp only [base]; omega)
  have hlinear : candidateCount full.length q ≤ base ^ 2 := by
    have hmb : candidateCount full.length q ≤ base := by dsimp only [candidateCount, base]; omega
    have hbs : base ≤ base ^ 2 := by nlinarith
    exact hmb.trans hbs
  have hraw : full.length * q ≤ base ^ 2 := by
    have hnm : full.length ≤ candidateCount full.length q := by unfold candidateCount; omega
    exact (Nat.mul_le_mul_right q hnm).trans hprod
  calc
    full.length * q + 2 + heapWords full.length q + 10450 ≤ 17 * base ^ 2 + 18660 := by
      unfold heapWords workspaceLimit workspaceBase
      nlinarith
    _ < base ^ 2 * 16384 := by nlinarith
    _ ≤ base ^ 2 * base ^ 14 := Nat.mul_le_mul_left _ hpower
    _ = base ^ 16 := by rw [← pow_add]

/-- Once an actual execution has the proved instruction count, this
charges its whole dynamic trace and every initialization/loading word.
The step bound alone is not asserted to prove safety or correct output. -/
theorem totalCost_le {bits : Nat} (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (steps : Nat) (heap : BitVec bits → BitVec bits)
    (hsteps : steps ≤ 16384 * treeWork full.length q) :
    totalCost (heapWords full.length q) (rawIncidenceROM q full)
      RawTreePreprocessingNat.program steps heap ≤ 262144 * treeWork full.length q := by
  let M := full.length + q + 1
  let W := treeWork full.length q
  have hm : 1 ≤ M := by dsimp only [M]; omega
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM2W : M ^ 2 ≤ W := Nat.le_mul_of_pos_right _ hq
  have hunit : 1 ≤ W := hm.trans (hM2.trans hM2W)
  have hM : M ≤ W := hM2.trans hM2W
  have hMq : M * q ≤ W := Nat.mul_le_mul_right q hM2
  have hNq : full.length * q ≤ W :=
    Nat.mul_le_mul_right q ((show full.length ≤ M by dsimp only [M]; omega).trans hM2)
  have hheap : heapWords full.length q ≤ 8224 * W := by
    change 8 * M * q + 16 + 8 * M + 8192 ≤ _
    nlinarith
  have htrace := packingDynamicTrace_length_le (rawIncidenceROM q full)
    RawTreePreprocessingNat.program steps (packingInitial heap)
  unfold totalCost
  rw [rawIncidenceROM_size, code_length]
  change full.length * q + 2 + 10450 + heapWords full.length q + 8 + _ ≤ 262144 * W
  change steps ≤ 16384 * W at hsteps
  omega

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingCostBounds
