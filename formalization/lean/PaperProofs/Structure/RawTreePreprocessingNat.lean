module

public import PaperProofs.Structure.RawCandidateTreePrefix
public import PaperProofs.Structure.RawCandidateSerializationAssembly
public import PaperProofs.Structure.RawIncidenceCostBounds
import Mathlib.Tactic.Linarith

/-! A single fixed raw-incidence program constructs the complete serialized
tree, restores its output registers, and executes HALT.  This proves natural
address execution and its instruction bound.  Physical word refinement,
all-prefix access safety, and loading/allocation/trace cost remain separate
obligations in A06.FullClaims. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingNat

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreeSerialization

def childrenStart : Nat := RawCandidateTreePrefix.inputStart + 443

def tail : List PackingOp :=
  RawCandidateSerializedChildrenRAM.programAt childrenStart ++ RawTreeOutputFinalizeRAM.program

/-- Chosen before any dimensions or incidence bits. -/
def program : List PackingOp := RawCandidateTreePrefix.program tail

def front : List PackingOp := RawCandidateTreePrefix.serializedFront tail

def footerFront : List PackingOp :=
  front ++ RawCandidateSerializedChildrenRAM.programAt childrenStart

theorem childrenStart_eq : childrenStart = 1649 := by
  rw [childrenStart, RawCandidateTreePrefix.inputStart_eq]

theorem front_length : front.length = childrenStart :=
  RawCandidateTreePrefix.serializedFront_length tail

theorem children_program :
    front ++ RawCandidateSerializedChildrenRAM.programAt front.length ++
      RawTreeOutputFinalizeRAM.program = program := by
  rw [front_length]
  exact RawCandidateTreePrefix.serializedProgram_eq tail

theorem footerFront_length : footerFront.length = childrenStart + 427 := by
  simp only [footerFront, List.length_append, front_length,
    RawCandidateSerializedChildrenRAM.programAt_length]

theorem footer_program : footerFront ++ RawTreeOutputFinalizeRAM.program = program := by
  simpa only [footerFront, front_length] using children_program

structure Output (q : Nat) (full : List (Finset (Fin q))) (result : NatState) : Prop where
  halted : result.halted = true
  accepted : result.register .value = 1
  nodes : result.register .old = (prepareNormalization q full).indexed.nodes.size
  length : result.register .fresh = (serializeROM (givenTreeROM q full)).length
  words : ∀ position < (serializeROM (givenTreeROM q full)).length,
    result.heap position = (serializeROM (givenTreeROM q full)).getD position 0

def successClockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  RawCandidateTreePrefix.prefixClockBound q full +
    RawCandidateSerializedChildrenRun.totalSteps q full + 14

/-- Every intermediate table and every output word is produced by this
same actual run; the only input assumptions are positive q and laminarity. -/
theorem succeeds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) :
    ∃ steps ≤ successClockBound q full,
      Output q full (natRun (rawIncidenceROM q full) program steps natInitial) := by
  obtain ⟨first, hfirst, entry⟩ := RawCandidateTreePrefix.serialized_entry tail q full hq hl
  let before := natRun (rawIncidenceROM q full) program first natInitial
  have hpc : before.pc = 5 * front.length := by
    rw [front_length]
    exact entry.ready.pc
  have hc := RawCandidateSerializedChildrenRun.serialize_append q full hq hl front
    RawTreeOutputFinalizeRAM.program before entry.children_input hpc entry.ready.active
  rw [children_program] at hc
  let childSteps := RawCandidateSerializedChildrenRun.totalSteps q full
  let after := natRun (rawIncidenceROM q full) program childSteps before
  have hw := RawCandidateSerializationAssembly.serialized_words q full hq hl _ before after
    entry.written hc
  have hfooterpc : after.pc = 5 * footerFront.length := by
    rw [footerFront_length, ← front_length]
    exact hc.pc
  have hf := RawCandidateSerializationAssembly.finalize q full hq hl footerFront after
    hc.input.headers hw hfooterpc hc.active
  rw [footer_program] at hf
  dsimp only at hf
  have hrun : natRun (rawIncidenceROM q full) program 14 after =
      natRun (rawIncidenceROM q full) program (first + childSteps + 14) natInitial := by
    simp only [after, before, natRun_add]
  refine ⟨first + childSteps + 14, ?_, ?_⟩
  · unfold successClockBound
    dsimp only [childSteps]
    omega
  · rw [← hrun]
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

def constructorTail : List PackingOp :=
  RawCandidateRetentionRAM.programAt RawCandidateMetadataPrefix.retentionStart ++
    (RawCandidateOrderingRAM.programAt RawCandidateMetadataPrefix.orderingStart ++
      (RawCandidateParentRAM.programAt RawCandidateTreePrefix.parentStart ++
        RawCandidateSerializedInputRAM.programAt RawCandidateTreePrefix.inputStart ++ tail))

theorem program_eq_constructor :
    program = RawCandidateConstructorPrefix.program constructorTail := rfl

/-- Nonlaminar inputs take the real dispatcher rejection branch and HALT. -/
theorem rejects (q : Nat) (full : List (Finset (Fin q))) (hl : ¬ LaminarSchedule full) :
    ∃ steps ≤ checkerSteps full.length q + 2,
      (natRun (rawIncidenceROM q full) program steps natInitial).halted = true ∧
      (natRun (rawIncidenceROM q full) program steps natInitial).register .value = 0 := by
  rw [program_eq_constructor]
  exact RawCandidateConstructorPrefix.rejects constructorTail q full hl

theorem successClockBound_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    successClockBound q full ≤ 16384 * treeWork full.length q := by
  let M := full.length + q + 1
  let t := (prepareNormalization q full).indexed.nodes.size
  let W := treeWork full.length q
  have hm : 1 ≤ M := by dsimp only [M]; omega
  have ht : t ≤ M := prepared_indexed_size_le q full
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM2W : M ^ 2 ≤ W := by
    change M ^ 2 ≤ M ^ 2 * q
    exact Nat.le_mul_of_pos_right _ hq
  have hMW : M ≤ W := hM2.trans hM2W
  have hunit : 1 ≤ W := hm.trans hMW
  have hplus : q + 1 ≤ 2 * q := by omega
  have hsquare : (M + 1) ^ 2 ≤ 4 * M ^ 2 := by nlinarith
  have htsquare : (t + 1) ^ 2 ≤ 4 * M ^ 2 := by
    exact (Nat.pow_le_pow_left (by omega : t + 1 ≤ M + 1) 2).trans hsquare
  have hproduct : (t + 1) * (M + 1) ≤ 4 * M ^ 2 := by
    calc
      _ ≤ (M + 1) * (M + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = (M + 1) ^ 2 := by ring
      _ ≤ _ := hsquare
  have hc : checkerSteps full.length q ≤ 144 * W := checkerSteps_le _ _ hq
  have hr : RawCandidateRetentionRAM.totalSteps full.length q ≤ 1024 * W := by
    calc
      _ ≤ 512 * M ^ 2 * (q + 1) := RawCandidateRetentionRAM.totalSteps_le _ _
      _ ≤ 512 * M ^ 2 * (2 * q) := Nat.mul_le_mul_left _ hplus
      _ = 1024 * W := by dsimp only [W, treeWork, M]; ring
  have ho : RawCandidateOrderingRAM.totalSteps M ≤ 1320 * W := by
    calc
      _ ≤ 330 * (M + 1) ^ 2 := RawCandidateOrderingRAM.totalSteps_quadratic M
      _ ≤ 330 * (4 * M ^ 2) := Nat.mul_le_mul_left _ hsquare
      _ = 1320 * M ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hM2W
  have hp : 512 * (t + 1) * (M + 1) * (q + 1) ≤ 4096 * W := by
    calc
      _ = 512 * ((t + 1) * (M + 1)) * (q + 1) := by ring
      _ ≤ 512 * (4 * M ^ 2) * (2 * q) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hproduct) hplus
      _ = 4096 * W := by dsimp only [W, treeWork, M]; ring
  have hNq : full.length * q ≤ W :=
    Nat.mul_le_mul_right q ((show full.length ≤ M by dsimp only [M]; omega).trans hM2)
  have htq : t * q ≤ W := Nat.mul_le_mul_right q (ht.trans hM2)
  have hi : 256 * (full.length * q + t * q + t + 1) ≤ 1024 * W := by
    have htw := ht.trans hMW
    omega
  have hs : RawCandidateSerializedChildrenRun.totalSteps q full ≤ 2048 * W := by
    calc
      _ ≤ 512 * (t + 1) ^ 2 := RawCandidateSerializedChildrenRun.totalSteps_le q full
      _ ≤ 512 * (4 * M ^ 2) := Nat.mul_le_mul_left _ htsquare
      _ = 2048 * M ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hM2W
  change checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q +
    RawCandidateOrderingRAM.totalSteps M + 512 * (t + 1) * (M + 1) * (q + 1) +
      256 * (full.length * q + t * q + t + 1) +
        RawCandidateSerializedChildrenRun.totalSteps q full + 14 ≤ 16384 * W
  omega

/-- Complete raw-input correctness and O((N+q+1)^2 q) instruction count
for the natural-address interpreter.  This is not the physical-word,
access, and total-cost assertion `RawTreePreprocessingClaims.FullClaims`. -/
theorem raw_preprocessing (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    ∃ steps ≤ 16384 * treeWork full.length q,
      let result := natRun (rawIncidenceROM q full) program steps natInitial
      result.halted = true ∧ result.register .value ≤ 1 ∧
        (result.register .value = 1 ↔ LaminarSchedule full) ∧
        (LaminarSchedule full → Output q full result) := by
  by_cases hl : LaminarSchedule full
  · obtain ⟨steps, hsteps, output⟩ := succeeds q full hq hl
    refine ⟨steps, hsteps.trans (successClockBound_le q full hq),
      output.halted, ?_, ?_, fun _ => output⟩
    · rw [output.accepted]
    · exact ⟨fun _ => hl, fun _ => output.accepted⟩
  · obtain ⟨steps, hsteps, hhalted, hvalue⟩ := rejects q full hl
    have hchecker := checkerSteps_le full.length q hq
    have hunit : 1 ≤ treeWork full.length q := by
      unfold treeWork
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : 1 ≤ full.length + q + 1) 2) hq
    refine ⟨steps, by omega, hhalted, ?_, ?_, fun h => False.elim (hl h)⟩
    · rw [hvalue]; omega
    · rw [hvalue]
      simp only [Nat.zero_ne_one, false_iff]
      exact hl

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingNat
