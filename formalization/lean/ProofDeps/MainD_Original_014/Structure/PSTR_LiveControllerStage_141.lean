module

public import Structure.PSTR_LiveControllerScripts_140
public import Structure.PSTR_UniformHeadsClaims_126

/-! Final ORIGINAL claim adapters, still requiring the real uniform raw
preprocessor obligation below. This file neither constructs that program
nor asserts its existence. No field is added to the original caller or
Implementation. The actual live/heads programs are the frozen1514/1490
programs; all uses of heads start at the SAME actual prepared heap.

SOURCE ONLY until the parent's coherent MAIN037 view is frozen. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRLiveControllerStage

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020
open PaperProofs.Common.Native.CompactPrice

def spaceConstant : Nat := 16393

/-- Chosen BEFORE q/full/used, with every original scalar constant shared. -/
def jointConstant (preprocessingConstant : Nat) : Nat :=
  max (max preprocessingConstant 32768) (max 30000 spaceConstant)

theorem preprocessing_le_joint (preprocessingConstant : Nat) :
    preprocessingConstant ≤ jointConstant preprocessingConstant :=
  (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)

theorem live_le_joint (preprocessingConstant : Nat) :
    32768 ≤ jointConstant preprocessingConstant :=
  (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)

theorem heads_le_joint (preprocessingConstant : Nat) :
    30000 ≤ jointConstant preprocessingConstant :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem space_le_joint (preprocessingConstant : Nat) :
    spaceConstant ≤ jointConstant preprocessingConstant :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem joint_pos (preprocessingConstant : Nat) : 0 < jointConstant preprocessingConstant := by
  have h := live_le_joint preprocessingConstant
  omega

/-- Reuse the existing persistent-table bound; only the original bitmap
and8192(t+1) capacity scratch are added. No new layout assumption occurs. -/
theorem capacity_le_work (N q t : Nat) (hq : 0 < q) (ht : 0 < t) :
    capacityWords 8192 N q t ≤ spaceConstant * work N q t := by
  have table := (PA17MetadataAssembly003.tableWords_le_capacityWords N q t).trans
    (PA17MetadataAssembly003.capacityWords_le N q t ht)
  have qt : q ≤ work N q t := by
    calc
      q ≤ (N + 1) * (q + 1) := by nlinarith
      _ ≤ (N + 1) * (q + 1) * t := Nat.le_mul_of_pos_right _ ht
      _ = work N q t := rfl
  have tt : t ≤ work N q t :=
    Nat.le_mul_of_pos_left t (Nat.mul_pos (by omega) (by omega))
  have scratch : 8192 * (t + 1) ≤ 16384 * work N q t := by
    calc
      _ ≤ 8192 * (2 * t) := Nat.mul_le_mul_left _ (by omega)
      _ = 16384 * t := by ring
      _ ≤ 16384 * work N q t := Nat.mul_le_mul_left _ tt
  calc
    capacityWords 8192 N q t = tableWords N q t + q + 8192 * (t + 1) := by
      simp only [capacityWords, ne_of_gt hq, ite_false]
    _ ≤ 8 * work N q t + work N q t + 16384 * work N q t :=
      Nat.add_le_add (Nat.add_le_add table qt) scratch
    _ = spaceConstant * work N q t := by
      unfold spaceConstant
      ring

theorem original_space {q : Nat} (full : List (Finset (Fin q))) :
    capacity full * CapacityBits.width q ≤
      spaceConstant * work full.length q (treeSize q full) * Nat.clog 2 (q + 2) := by
  by_cases hq : q = 0
  · subst q
    simp only [capacity, capacityWords, ↓reduceIte, Nat.zero_mul, Nat.zero_le]
  · have positive : 0 < q := Nat.pos_of_ne_zero hq
    have ht : 0 < treeSize q full := by
      simp only [treeSize, hq, ite_false]
      obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
      exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
    have width : CapacityBits.width q ≤ Nat.clog 2 (q + 2) :=
      Nat.clog_mono_right 2 (by omega)
    exact Nat.mul_le_mul (capacity_le_work full.length q (treeSize q full) positive ht) width

/-- The exact STILL OPEN raw-preprocessor proof obligation. There is ONE
fixed program outside all original inputs, genuine zero-heap Word execution
and the original charged totalCost. In particular no tree/table/answer is
supplied by the caller. This definition is not a proof that such P exists. -/
def RawPreprocessorObligation (preprocessingConstant : Nat) (preprocessor : List PackingOp) : Prop :=
  ∀ (q : Nat) (full : List (Finset (Fin q))), LaminarSchedule full → ∀ used : Finset (Fin q),
    let empty : BitVec (wordBits full) → BitVec (wordBits full) := fun _ => BitVec.ofNat (wordBits full) 0
    let source := controllerInput q full used
    ∃ steps : Nat,
      DynamicRunCorrect (allocatedWords full) source preprocessor steps empty ∧
      totalCost (allocatedWords full) source preprocessor steps empty ≤
        preprocessingConstant * preprocessingWork full.length q (treeSize q full) ∧
      HeapRepresents q full (capacity full) ⟨0, used, false⟩
        (packingRun source preprocessor steps (packingInitial empty)).heap

theorem raw_preprocessor_mono {small large : Nat} (preprocessor : List PackingOp)
    (hconstant : small ≤ large) (raw : RawPreprocessorObligation small preprocessor) :
    RawPreprocessorObligation large preprocessor := by
  intro q full hl used
  obtain ⟨steps, dynamic, cost, represented⟩ := raw q full hl used
  exact ⟨steps, dynamic, cost.trans (Nat.mul_le_mul_right _ hconstant), represented⟩

/-- Conditional assembly only. The unconstructed real uniform preprocessor
is the substantive premise; all live/script and space obligations are proved. -/
theorem machine_of_actual_preprocessor (preprocessingConstant : Nat) (preprocessor live : List PackingOp)
    (_hLive : live = PSTRLiveControllerCode.program)
    (raw : RawPreprocessorObligation preprocessingConstant preprocessor) : MachineControllerClaims := by
  subst live
  refine ⟨jointConstant preprocessingConstant, 32, 8192, 8192, preprocessor,
    PSTRLiveControllerCode.program, joint_pos preprocessingConstant,
    by decide, by decide, by decide, ?_⟩
  intro q full hl used
  let empty : BitVec (wordBits full) → BitVec (wordBits full) := fun _ => BitVec.ofNat (wordBits full) 0
  obtain ⟨steps, dynamic, cost, represented⟩ := raw q full hl used
  let prepared := packingRun (controllerInput q full used) preprocessor steps (packingInitial empty)
  refine ⟨steps, dynamic, ?_, ?_, represented, ?_, ?_⟩
  · exact cost.trans (Nat.mul_le_mul_right _ (preprocessing_le_joint preprocessingConstant))
  · exact (original_space full).trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (space_le_joint preprocessingConstant)))
  · intro configuration heap rep command allowed
    obtain ⟨count, call⟩ := PSTRLiveController.original_calls full hl configuration heap rep command allowed
    exact ⟨count, PSTRCommandPrefixes.call_mono_constant full PSTRLiveControllerCode.program
      configuration command count heap (live_le_joint preprocessingConstant) call⟩
  · intro commands script
    obtain ⟨counts, length, run, charged⟩ := PSTRLiveController.actual_script full hl used commands script prepared.heap represented
    refine ⟨counts, length, PSTRCommandPrefixes.run_mono_constant full PSTRLiveControllerCode.program
      ⟨0, used, false⟩ commands counts prepared.heap (live_le_joint preprocessingConstant) run, ?_⟩
    exact charged.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 2 (live_le_joint preprocessingConstant))))

/-- The SAME actual preSteps/built.heap is fed directly into the frozen
1490-op heads run. No independent reconstruction or query oracle appears. -/
theorem heads_of_actual_preprocessor (preprocessingConstant : Nat) (preprocessor : List PackingOp)
    (implementation : PaperProofs.Common.Native.CompactPrice.Implementation)
    (hPreprocessor : implementation.preprocessor = preprocessor)
    (hHeads : implementation.heads = PSTRUniformHeads.program)
    (raw : RawPreprocessorObligation preprocessingConstant preprocessor) :
    HeadExtractionClaims (jointConstant preprocessingConstant) 32 8192 implementation := by
  intro q full hl used
  rw [hPreprocessor, hHeads]
  obtain ⟨preSteps, preDynamic, preCost, represented⟩ := raw q full hl used
  let empty : BitVec (wordBits full) → BitVec (wordBits full) := fun _ => BitVec.ofNat (wordBits full) 0
  let built := packingRun (controllerInput q full used) preprocessor preSteps (packingInitial empty)
  obtain ⟨headSteps, _upper, headDynamic, headCost, output⟩ :=
    PSTRUniformHeads.actual_heads full hl used built.heap represented
  refine ⟨preSteps, headSteps, preDynamic, ?_, represented, headDynamic, ?_, output⟩
  · exact preCost.trans (Nat.mul_le_mul_right _ (preprocessing_le_joint preprocessingConstant))
  · exact headCost.trans (Nat.mul_le_mul_right _ (heads_le_joint preprocessingConstant))

theorem heads_mono_constant {small large wordFactor scratchFactor : Nat}
    (implementation : PaperProofs.Common.Native.CompactPrice.Implementation) (hconstant : small ≤ large)
    (claims : HeadExtractionClaims small wordFactor scratchFactor implementation) :
    HeadExtractionClaims large wordFactor scratchFactor implementation := by
  intro q full hl used
  obtain ⟨preSteps, headSteps, preDynamic, preCost, represented, headDynamic, headCost, output⟩ := claims q full hl used
  exact ⟨preSteps, headSteps, preDynamic, preCost.trans (Nat.mul_le_mul_right _ hconstant),
    represented, headDynamic, headCost.trans (Nat.mul_le_mul_right _ hconstant), output⟩

/-- All programs and the common constant precede every original raw input.
This remains conditional on the real raw preprocessor proof, not on new
caller data or implementation fields. It does not close original FullClaims. -/
theorem machine_and_heads_of_actual_preprocessor (preprocessingConstant : Nat) (preprocessor : List PackingOp)
    (implementation : PaperProofs.Common.Native.CompactPrice.Implementation)
    (hPreprocessor : implementation.preprocessor = preprocessor)
    (hLive : implementation.live = PSTRLiveControllerCode.program)
    (hHeads : implementation.heads = PSTRUniformHeads.program)
    (raw : RawPreprocessorObligation preprocessingConstant preprocessor) :
    MachineControllerClaims ∧ HeadExtractionClaims (jointConstant preprocessingConstant) 32 8192 implementation :=
  ⟨machine_of_actual_preprocessor preprocessingConstant preprocessor implementation.live hLive raw,
    heads_of_actual_preprocessor preprocessingConstant preprocessor implementation hPreprocessor hHeads raw⟩

end PaperProofs.Structure.LaminarTree.PSTRLiveControllerStage
