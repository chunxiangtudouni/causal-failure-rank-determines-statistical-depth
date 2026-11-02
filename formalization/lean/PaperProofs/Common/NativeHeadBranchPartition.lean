module

public import PaperProofs.Common.NativeHeadContinuation
public import PaperProofs.Common.EntryContinuationPartition

/-!
Actual next-entry records have an exhaustive measurable public head-branch
partition. The same correct/allocated/fatal mechanisms as NativeBellmanLower
are applied directly to recordEvent, without assuming a larger historyGate
is all first entry. The countable sum uses the real clock-indexed future
charge and keeps paths that never reach the next stage outside this event.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Function

namespace PaperProofs.Common.Native.NativeHeadBranchPartition

open EntryContinuationPartition

variable {I : Instance} {Seed : Type*}

def goodRecords (head : I.Stage) : Set (Record I) := {record | HeadCorrectStartup head record.2}
def badRecords (head : I.Stage) : Set (Record I) := (goodRecords head)ᶜ
def allocatedRecords (head : I.Stage) : Set (Record I) :=
  {record | ¬ HeadCorrectStartup head record.2 ∧ record.2.commitments ≠ []}
def missedRecords (head : I.Stage) : Set (Record I) :=
  {record | ¬ HeadCorrectStartup head record.2 ∧ record.2.commitments = []}

theorem record_classes_exhaustive (head : I.Stage) (record : Record I) :
    record ∈ goodRecords head ∨ record ∈ allocatedRecords head ∨ record ∈ missedRecords head := by
  classical
  by_cases hc : HeadCorrectStartup head record.2
  · exact Or.inl hc
  · by_cases he : record.2.commitments = []
    · exact Or.inr (Or.inr ⟨hc, he⟩)
    · exact Or.inr (Or.inl ⟨hc, he⟩)

theorem badRecords_eq_allocated_union_missed (head : I.Stage) :
    badRecords head = allocatedRecords head ∪ missedRecords head := by
  classical
  ext record
  simp only [badRecords, goodRecords, allocatedRecords, missedRecords, Set.mem_compl_iff,
    Set.mem_ofPred_eq, Set.mem_union]
  tauto

theorem mem_selectedGate_iff (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (records : Set (Record I)) (sample : Seed × input.World) :
    sample ∈ selectedGate input C mode accounting rule next gate records ↔
      ∃ record ∈ records, sample ∈ indexedEvent input C mode accounting rule next gate record := by
  constructor
  · intro hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    exact ⟨record.val, record.property, hr⟩
  · rintro ⟨record, hr, hs⟩
    exact Set.mem_iUnion.mpr ⟨⟨record, hr⟩, hs⟩

theorem selectedGate_subset_reach (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (records : Set (Record I)) :
    selectedGate input C mode accounting rule next gate records ⊆ reachGate input C mode accounting rule next gate := by
  intro sample hs
  obtain ⟨record, _, hr⟩ := (mem_selectedGate_iff input C mode accounting rule next gate records sample).mp hs
  rw [← iUnion_indexedEvent_eq_reachGate input C mode accounting rule next gate]
  exact Set.mem_iUnion.mpr ⟨record, hr⟩

theorem selectedGate_disjoint (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (left right : Set (Record I)) (hd : Disjoint left right) :
    Disjoint (selectedGate input C mode accounting rule next gate left) (selectedGate input C mode accounting rule next gate right) := by
  apply Set.disjoint_left.mpr
  intro sample hl hr
  obtain ⟨l, hleft, hle⟩ := (mem_selectedGate_iff input C mode accounting rule next gate left sample).mp hl
  obtain ⟨r, hright, hre⟩ := (mem_selectedGate_iff input C mode accounting rule next gate right sample).mp hr
  have heq := recordEvent_unique input C mode accounting rule next gate sample l r hle hre
  exact Set.disjoint_left.mp hd hleft (by rw [heq]; exact hright)

theorem good_bad_gate_partition (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next head : I.Stage) (gate : Set Seed) :
    reachGate input C mode accounting rule next gate =
      selectedGate input C mode accounting rule next gate (goodRecords head) ∪
      selectedGate input C mode accounting rule next gate (badRecords head) := by
  classical
  apply Set.Subset.antisymm
  · intro sample hs
    rw [← iUnion_indexedEvent_eq_reachGate input C mode accounting rule next gate] at hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    by_cases hc : record ∈ goodRecords head
    · exact Or.inl ((mem_selectedGate_iff input C mode accounting rule next gate _ sample).mpr ⟨record, hc, hr⟩)
    · exact Or.inr ((mem_selectedGate_iff input C mode accounting rule next gate _ sample).mpr ⟨record, hc, hr⟩)
  · rintro sample (hs | hs)
    · exact selectedGate_subset_reach input C mode accounting rule next gate _ hs
    · exact selectedGate_subset_reach input C mode accounting rule next gate _ hs

theorem good_bad_gates_disjoint (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next head : I.Stage) (gate : Set Seed) :
    Disjoint (selectedGate input C mode accounting rule next gate (goodRecords head))
      (selectedGate input C mode accounting rule next gate (badRecords head)) :=
  selectedGate_disjoint input C mode accounting rule next gate _ _ (by
    apply Set.disjoint_left.mpr
    intro record hc hb
    exact hb hc)

variable [MeasurableSpace Seed]

theorem measurableSet_selectedGate (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (next : I.Stage)
    (gate : Set Seed) (hgate : MeasurableSet gate) (records : Set (Record I)) :
    MeasurableSet (selectedGate input C mode accounting rule next gate records) :=
  MeasurableSet.iUnion (fun record : records =>
    measurableSet_recordEvent input C mode accounting rule hm next record.val.1 record.val.2 gate hgate)

private theorem optionBool_wrong_of_ne (value : Option Bool) (truth : Bool)
    (hnone : value ≠ none) (hcorrect : value ≠ some truth) : value = some (!truth) := by
  cases value with
  | none => exact (hnone rfl).elim
  | some bit => cases truth <;> cases bit <;> simp_all

theorem record_good_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : I.Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (hc : HeadCorrectStartup head startup) (price : ℝ) :
    ENNReal.ofReal (input.goodPenaltyReal head R price) *
      input.seededWorldLaw ν (recordEvent input C .uncapped accounting policy.val.rule next n startup gate) ≤
      ∫⁻ sample in recordEvent input C .uncapped accounting policy.val.rule next n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample ∂input.seededWorldLaw ν := by
  classical
  let E := recordEvent input C .uncapped accounting policy.val.rule next n startup gate
  by_cases he : E.Nonempty
  · obtain ⟨sample, hs⟩ := he
    have hf := recordEvent_firstEntry input C .uncapped accounting policy.val.rule next n startup gate sample hs
    have hentry : FirstEntryAt input C .uncapped accounting policy.val.rule 1 n sample := hnext ▸ hf.1
    have hw := firstEntry_one_head_written input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n hentry
    obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample n
    have hcorrect := (headCorrectStartup_iff input C hC.1 .uncapped accounting policy.val.rule sample.1 _ _ hp head hw).mp
      (by rw [hf.2]; exact hc)
    have hempty := firstEntry_one_correct_no_commitments input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n hentry hcorrect
    have hcomm : startup.committedTools = ∅ := by
      rw [← hf.2]
      simp only [publicStartup, Startup.committedTools, hempty, List.map_nil, List.toFinset_nil]
    have hb := entry_record_continuation_lower input C hC accounting R policy ν next n startup gate hgate (ENNReal.ofReal price)
    rw [hcomm, Finset.sdiff_empty] at hb
    simpa only [StatisticalInput.goodPenaltyReal, hhead, Nat.zero_add, hnext, ofReal_healthyPenaltyReal] using hb
  · have hz : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    change ENNReal.ofReal (input.goodPenaltyReal head R price) * input.seededWorldLaw ν E ≤ _
    rw [hz, measure_empty, mul_zero]
    exact bot_le

theorem record_allocated_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : I.Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (a : Commitment I) (ha : a ∈ startup.commitments) (price : ℝ) :
    ENNReal.ofReal (input.badPenaltyReal head R price) *
      input.seededWorldLaw ν (recordEvent input C .uncapped accounting policy.val.rule next n startup gate) ≤
      ∫⁻ sample in recordEvent input C .uncapped accounting policy.val.rule next n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample ∂input.seededWorldLaw ν := by
  classical
  let E := recordEvent input C .uncapped accounting policy.val.rule next n startup gate
  by_cases he : E.Nonempty
  · obtain ⟨sample, hs⟩ := he
    have hf := recordEvent_firstEntry input C .uncapped accounting policy.val.rule next n startup gate sample hs
    have hentry : FirstEntryAt input C .uncapped accounting policy.val.rule 1 n sample := hnext ▸ hf.1
    have ham : a ∈ (run input C .uncapped accounting policy.val.rule sample n).ledger.commitments := by
      change a ∈ (publicStartup (run input C .uncapped accounting policy.val.rule sample n)).commitments
      rw [hf.2]
      exact ha
    obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample n
    have ht := prefix_commitments_usable input C accounting policy.val.rule R policy.property sample.1 _ _ hp a ham
    have hs := firstEntry_one_commitment_stage input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n hentry a ham
    rw [hs] at ht
    have hsingle := firstEntry_one_committedTools_singleton input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n hentry a ham
    have hcomm : startup.committedTools = {a.tool} := by rw [← hf.2]; exact hsingle
    have hv : ENNReal.ofReal (input.badPenaltyReal head R price) ≤
        input.healthyPenalty next.val (R \ startup.committedTools) (ENNReal.ofReal price) := by
      rw [hnext, hcomm, Finset.sdiff_singleton_eq_erase]
      have hb := ENNReal.ofReal_le_ofReal (badPenaltyReal_le_tool input head R price a.tool (Finset.mem_inter.mpr ⟨ht.2, ht.1⟩))
      simpa only [hhead, Nat.zero_add, ofReal_healthyPenaltyReal] using hb
    exact (mul_le_mul_left hv _).trans
      (entry_record_continuation_lower input C hC accounting R policy ν next n startup gate hgate (ENNReal.ofReal price))
  · have hz : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    change ENNReal.ofReal (input.badPenaltyReal head R price) * input.seededWorldLaw ν E ≤ _
    rw [hz, measure_empty, mul_zero]
    exact bot_le

theorem record_missed_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : I.Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (hc : ¬ HeadCorrectStartup head startup) (hempty : startup.commitments = []) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (input.badPenaltyReal head R price) *
      input.seededWorldLaw ν (recordEvent input C .uncapped accounting policy.val.rule next n startup gate) ≤
      ∫⁻ sample in recordEvent input C .uncapped accounting policy.val.rule next n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample ∂input.seededWorldLaw ν := by
  rw [← setLIntegral_const]
  apply setLIntegral_mono' (measurableSet_recordEvent input C .uncapped accounting policy.val.rule policy.val.measurable_rule next n startup gate hgate)
  intro sample hs
  have hf := recordEvent_firstEntry input C .uncapped accounting policy.val.rule next n startup gate sample hs
  have hentry : FirstEntryAt input C .uncapped accounting policy.val.rule 1 n sample := hnext ▸ hf.1
  have hw := firstEntry_one_head_written input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n hentry
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample n
  have hwrong : (run input C .uncapped accounting policy.val.rule sample n).ledger.written head =
      some (!(run input C .uncapped accounting policy.val.rule sample n).ledger.truth head) := by
    apply optionBool_wrong_of_ne _ _ hw
    intro hcorrect
    apply hc
    rw [← hf.2]
    exact (headCorrectStartup_iff input C hC.1 .uncapped accounting policy.val.rule sample.1 _ _ hp head hw).mpr hcorrect
  have hno : (run input C .uncapped accounting policy.val.rule sample n).ledger.commitments = [] := by
    change (publicStartup (run input C .uncapped accounting policy.val.rule sample n)).commitments = []
    rw [hf.2, hempty]
  have hfailure := wrong_unallocated_behind_cursor_failure input C hC.2 .uncapped accounting policy.val.rule
    policy.val.legal sample n head (by rw [hf.1.1, hnext, hhead]; exact Nat.zero_lt_one) hwrong
    (by intro a ha; rw [hno] at ha; cases ha)
  have hb := ENNReal.ofReal_le_ofReal (input.penalty_successor_order head R price hprice).2.2
  exact hb.trans (original_failure_penalty_le_comparison input C .uncapped accounting policy.val.rule sample n (ENNReal.ofReal price) hfailure)

theorem record_branch_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : I.Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (headEntryContinuationReal input head R price startup) *
      input.seededWorldLaw ν (recordEvent input C .uncapped accounting policy.val.rule next n startup gate) ≤
      ∫⁻ sample in recordEvent input C .uncapped accounting policy.val.rule next n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample ∂input.seededWorldLaw ν := by
  classical
  by_cases hc : HeadCorrectStartup head startup
  · simpa only [headEntryContinuationReal, hc, ↓reduceIte] using
      record_good_lower input C hC accounting R policy ν head next hhead hnext n startup gate hgate hc price
  · by_cases he : startup.commitments = []
    · simpa only [headEntryContinuationReal, hc, ↓reduceIte] using
        record_missed_lower input C hC accounting R policy ν head next hhead hnext n startup gate hgate hc he price hprice
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil startup.commitments he
      simpa only [headEntryContinuationReal, hc, ↓reduceIte] using
        record_allocated_lower input C hC accounting R policy ν head next hhead hnext n startup gate hgate a ha price

noncomputable def entryBranchWeight (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) : Seed × input.World → ℝ≥0∞ :=
  pieces input C mode accounting rule next
    (fun record _ => ENNReal.ofReal (headEntryContinuationReal input head R price record.2))

omit [MeasurableSpace Seed] in
theorem entryBranchWeight_on_good (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (gate : Set Seed) (sample : Seed × input.World)
    (hs : sample ∈ selectedGate input C mode accounting rule next gate (goodRecords head)) :
    entryBranchWeight input C mode accounting rule next head R price sample = ENNReal.ofReal (input.goodPenaltyReal head R price) := by
  classical
  obtain ⟨record, hc, hr⟩ := (mem_selectedGate_iff input C mode accounting rule next gate _ sample).mp hs
  have hcorrect : HeadCorrectStartup head record.2 := hc
  have hw := pieces_on_record input C mode accounting rule next
    (fun record _ => ENNReal.ofReal (headEntryContinuationReal input head R price record.2)) gate record sample hr
  simpa only [entryBranchWeight, headEntryContinuationReal, hcorrect, ↓reduceIte] using hw

omit [MeasurableSpace Seed] in
theorem entryBranchWeight_on_bad (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (gate : Set Seed) (sample : Seed × input.World)
    (hs : sample ∈ selectedGate input C mode accounting rule next gate (badRecords head)) :
    entryBranchWeight input C mode accounting rule next head R price sample = ENNReal.ofReal (input.badPenaltyReal head R price) := by
  classical
  obtain ⟨record, hc, hr⟩ := (mem_selectedGate_iff input C mode accounting rule next gate _ sample).mp hs
  have hcorrect : ¬ HeadCorrectStartup head record.2 := hc
  have hw := pieces_on_record input C mode accounting rule next
    (fun record _ => ENNReal.ofReal (headEntryContinuationReal input head R price record.2)) gate record sample hr
  simpa only [entryBranchWeight, headEntryContinuationReal, hcorrect, ↓reduceIte] using hw

theorem measurable_entryBranchWeight (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (next head : I.Stage) (R : Finset I.Tool) (price : ℝ) :
    Measurable (entryBranchWeight input C mode accounting rule next head R price) :=
  measurable_pieces input C mode accounting rule hm next _ (fun _ => measurable_const)

/-- Summing all actual clock/snapshot records charges the continuation once.
No entry-a.s. or successful-history conditioning is inserted. -/
theorem weighted_arrival_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : I.Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (gate : Set Seed) (hgate : MeasurableSet gate) (price : ℝ) (hprice : 0 ≤ price) :
    (∫⁻ sample in reachGate input C .uncapped accounting policy.val.rule next gate,
      entryBranchWeight input C .uncapped accounting policy.val.rule next head R price sample ∂input.seededWorldLaw ν) ≤
      ∫⁻ sample in reachGate input C .uncapped accounting policy.val.rule next gate,
        entryContinuationCharge input C .uncapped accounting policy.val.rule next (ENNReal.ofReal price) sample ∂input.seededWorldLaw ν := by
  unfold entryBranchWeight entryContinuationCharge
  rw [lintegral_pieces_eq_tsum input C .uncapped accounting policy.val.rule policy.val.measurable_rule next gate hgate,
    lintegral_pieces_eq_tsum input C .uncapped accounting policy.val.rule policy.val.measurable_rule next gate hgate]
  apply ENNReal.tsum_le_tsum
  intro record
  rw [setLIntegral_const]
  exact record_branch_lower input C hC accounting R policy ν head next hhead hnext record.1 record.2 gate hgate price hprice

/-- The original Gg/Gb weighted mass lower bound on ALL actual arrivals.
The wrong/unallocated part is paid by the original failure penalty, while
genuine allocations remove their actual tool. The right side retains actual
future observations and one original task-failure penalty. -/
theorem good_bad_arrival_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : I.Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (gate : Set Seed) (hgate : MeasurableSet gate) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (input.goodPenaltyReal head R price) *
        input.seededWorldLaw ν (selectedGate input C .uncapped accounting policy.val.rule next gate (goodRecords head)) +
      ENNReal.ofReal (input.badPenaltyReal head R price) *
        input.seededWorldLaw ν (selectedGate input C .uncapped accounting policy.val.rule next gate (badRecords head)) ≤
      ∫⁻ sample in reachGate input C .uncapped accounting policy.val.rule next gate,
        entryContinuationCharge input C .uncapped accounting policy.val.rule next (ENNReal.ofReal price) sample ∂input.seededWorldLaw ν := by
  let μ := input.seededWorldLaw ν
  let good := selectedGate input C .uncapped accounting policy.val.rule next gate (goodRecords head)
  let bad := selectedGate input C .uncapped accounting policy.val.rule next gate (badRecords head)
  let weight := entryBranchWeight input C .uncapped accounting policy.val.rule next head R price
  have hgood : MeasurableSet good := measurableSet_selectedGate input C .uncapped accounting policy.val.rule policy.val.measurable_rule next gate hgate _
  have hbad : MeasurableSet bad := measurableSet_selectedGate input C .uncapped accounting policy.val.rule policy.val.measurable_rule next gate hgate _
  have hg : (∫⁻ sample in good, weight sample ∂μ) = ENNReal.ofReal (input.goodPenaltyReal head R price) * μ good := by
    calc
      _ = ∫⁻ _sample in good, ENNReal.ofReal (input.goodPenaltyReal head R price) ∂μ := by
        apply setLIntegral_congr_fun hgood
        intro sample hs
        exact entryBranchWeight_on_good input C .uncapped accounting policy.val.rule next head R price gate sample hs
      _ = _ := setLIntegral_const _ _
  have hb : (∫⁻ sample in bad, weight sample ∂μ) = ENNReal.ofReal (input.badPenaltyReal head R price) * μ bad := by
    calc
      _ = ∫⁻ _sample in bad, ENNReal.ofReal (input.badPenaltyReal head R price) ∂μ := by
        apply setLIntegral_congr_fun hbad
        intro sample hs
        exact entryBranchWeight_on_bad input C .uncapped accounting policy.val.rule next head R price gate sample hs
      _ = _ := setLIntegral_const _ _
  have hsplit : (∫⁻ sample in reachGate input C .uncapped accounting policy.val.rule next gate, weight sample ∂μ) =
      (∫⁻ sample in good, weight sample ∂μ) + ∫⁻ sample in bad, weight sample ∂μ := by
    rw [good_bad_gate_partition input C .uncapped accounting policy.val.rule next head gate]
    exact lintegral_union hbad (good_bad_gates_disjoint input C .uncapped accounting policy.val.rule next head gate)
  change ENNReal.ofReal (input.goodPenaltyReal head R price) * μ good +
    ENNReal.ofReal (input.badPenaltyReal head R price) * μ bad ≤ _
  rw [← hg, ← hb, ← hsplit]
  exact weighted_arrival_lower input C hC accounting R policy ν head next hhead hnext gate hgate price hprice

omit [MeasurableSpace Seed] in
theorem goodGate_eq_reach_local_correct (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head next : I.Stage)
    (hhead : head.val = 0) (hnext : next.val = 1) (gate : Set Seed) :
    selectedGate input C .uncapped accounting rule next gate (goodRecords head) =
      reachGate input C .uncapped accounting rule next gate ∩
      {sample | headExitDecision input head rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head} := by
  ext sample
  constructor
  · intro hs
    obtain ⟨record, hc, hr⟩ := (mem_selectedGate_iff input C .uncapped accounting rule next gate _ sample).mp hs
    have hf := recordEvent_firstEntry input C .uncapped accounting rule next record.1 record.2 gate sample hr
    have he : FirstEntryAt input C .uncapped accounting rule 1 record.1 sample := hnext ▸ hf.1
    refine ⟨selectedGate_subset_reach input C .uncapped accounting rule next gate _ hs, ?_⟩
    apply (firstEntry_one_local_correct_iff input C hearly accounting rule hlegal head hhead sample record.1 he).mp
    rw [hf.2]
    exact hc
  · rintro ⟨hs, hc⟩
    rw [← iUnion_indexedEvent_eq_reachGate input C .uncapped accounting rule next gate] at hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    have hf := recordEvent_firstEntry input C .uncapped accounting rule next record.1 record.2 gate sample hr
    have he : FirstEntryAt input C .uncapped accounting rule 1 record.1 sample := hnext ▸ hf.1
    apply (mem_selectedGate_iff input C .uncapped accounting rule next gate _ sample).mpr
    refine ⟨record, ?_, hr⟩
    have hh := (firstEntry_one_local_correct_iff input C hearly accounting rule hlegal head hhead sample record.1 he).mpr hc
    change HeadCorrectStartup head record.2
    rw [← hf.2]
    exact hh

omit [MeasurableSpace Seed] in
theorem badGate_eq_reach_local_wrong (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head next : I.Stage)
    (hhead : head.val = 0) (hnext : next.val = 1) (gate : Set Seed) :
    selectedGate input C .uncapped accounting rule next gate (badRecords head) =
      reachGate input C .uncapped accounting rule next gate ∩
      {sample | headExitDecision input head rule sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head} := by
  ext sample
  constructor
  · intro hs
    obtain ⟨record, hc, hr⟩ := (mem_selectedGate_iff input C .uncapped accounting rule next gate _ sample).mp hs
    have hf := recordEvent_firstEntry input C .uncapped accounting rule next record.1 record.2 gate sample hr
    have he : FirstEntryAt input C .uncapped accounting rule 1 record.1 sample := hnext ▸ hf.1
    refine ⟨selectedGate_subset_reach input C .uncapped accounting rule next gate _ hs, ?_⟩
    intro hl
    apply hc
    change HeadCorrectStartup head record.2
    rw [← hf.2]
    exact (firstEntry_one_local_correct_iff input C hearly accounting rule hlegal head hhead sample record.1 he).mpr hl
  · rintro ⟨hs, hc⟩
    rw [← iUnion_indexedEvent_eq_reachGate input C .uncapped accounting rule next gate] at hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    have hf := recordEvent_firstEntry input C .uncapped accounting rule next record.1 record.2 gate sample hr
    have he : FirstEntryAt input C .uncapped accounting rule 1 record.1 sample := hnext ▸ hf.1
    apply (mem_selectedGate_iff input C .uncapped accounting rule next gate _ sample).mpr
    refine ⟨record, ?_, hr⟩
    intro hh
    apply hc
    apply (firstEntry_one_local_correct_iff input C hearly accounting rule hlegal head hhead sample record.1 he).mp
    rw [hf.2]
    exact hh

omit [MeasurableSpace Seed] in
theorem selectedGate_union (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (left right : Set (Record I)) :
    selectedGate input C mode accounting rule next gate (left ∪ right) =
      selectedGate input C mode accounting rule next gate left ∪ selectedGate input C mode accounting rule next gate right := by
  ext sample
  simp only [mem_selectedGate_iff, Set.mem_union]
  constructor
  · rintro ⟨record, hl | hr, hs⟩
    · exact Or.inl ⟨record, hl, hs⟩
    · exact Or.inr ⟨record, hr, hs⟩
  · rintro (⟨record, hr, hs⟩ | ⟨record, hr, hs⟩)
    · exact ⟨record, Or.inl hr, hs⟩
    · exact ⟨record, Or.inr hr, hs⟩

omit [MeasurableSpace Seed] in
theorem three_branch_gate_partition (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next head : I.Stage) (gate : Set Seed) :
    reachGate input C mode accounting rule next gate =
      selectedGate input C mode accounting rule next gate (goodRecords head) ∪
      (selectedGate input C mode accounting rule next gate (allocatedRecords head) ∪
       selectedGate input C mode accounting rule next gate (missedRecords head)) := by
  rw [good_bad_gate_partition input C mode accounting rule next head gate,
    badRecords_eq_allocated_union_missed, selectedGate_union]

omit [MeasurableSpace Seed] in
theorem three_branch_gates_pairwise (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next head : I.Stage) (gate : Set Seed) :
    Disjoint (selectedGate input C mode accounting rule next gate (goodRecords head))
      (selectedGate input C mode accounting rule next gate (allocatedRecords head)) ∧
    Disjoint (selectedGate input C mode accounting rule next gate (goodRecords head))
      (selectedGate input C mode accounting rule next gate (missedRecords head)) ∧
    Disjoint (selectedGate input C mode accounting rule next gate (allocatedRecords head))
      (selectedGate input C mode accounting rule next gate (missedRecords head)) := by
  refine ⟨selectedGate_disjoint input C mode accounting rule next gate _ _ ?_,
    selectedGate_disjoint input C mode accounting rule next gate _ _ ?_,
    selectedGate_disjoint input C mode accounting rule next gate _ _ ?_⟩
  · apply Set.disjoint_left.mpr
    intro record hc ha
    exact ha.1 hc
  · apply Set.disjoint_left.mpr
    intro record hc hm
    exact hm.1 hc
  · apply Set.disjoint_left.mpr
    intro record ha hm
    exact ha.2 hm.2

end PaperProofs.Common.Native.NativeHeadBranchPartition
