module

public import PaperProofs.Common.RestrictedHistorySuffixBridge

/-!
Actual first-entry records, their countable partition, and R-restricted
continuation lower bounds. No user-supplied partition, first-entry premise,
posterior kernel, Bellman theorem, or finite-bill assumption is used.
Unreached paths are kept outside the arrival event, rather than declared
successful. The charge at an arrival is the original future observation
charge plus the original single eventual-failure penalty.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Function

namespace PaperProofs.Common.Native.EntryContinuationPartition

variable {I : Instance} {Seed : Type*}

abbrev Record (I : Instance) := ℕ × Startup I

def recordEvent (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) : Set (Seed × input.World) :=
  {sample | sample.1 ∈ gate ∧ entryStartupAt input C mode accounting rule next n sample = some startup}

def indexedEvent (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (record : Record I) : Set (Seed × input.World) :=
  recordEvent input C mode accounting rule next record.1 record.2 gate

def reachGate (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) : Set (Seed × input.World) :=
  {sample | sample.1 ∈ gate ∧ ∃ n, (run input C mode accounting rule sample n).cursor = next.val}

theorem recordEvent_firstEntry (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) (sample : Seed × input.World)
    (hs : sample ∈ recordEvent input C mode accounting rule next n startup gate) :
    FirstEntryAt input C mode accounting rule next.val n sample ∧
      publicStartup (run input C mode accounting rule sample n) = startup :=
  (entryStartupAt_some_iff input C mode accounting rule next n sample startup).mp hs.2

theorem firstEntry_unique (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (sample : Seed × input.World) (n m : ℕ)
    (hn : FirstEntryAt input C mode accounting rule next.val n sample)
    (hm : FirstEntryAt input C mode accounting rule next.val m sample) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact False.elim (hm.2 n h hn.1)
  · exact h
  · exact False.elim (hn.2 m h hm.1)

theorem recordEvent_unique (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (sample : Seed × input.World) (left right : Record I)
    (hl : sample ∈ indexedEvent input C mode accounting rule next gate left)
    (hr : sample ∈ indexedEvent input C mode accounting rule next gate right) : left = right := by
  have hleft := recordEvent_firstEntry input C mode accounting rule next left.1 left.2 gate sample hl
  have hright := recordEvent_firstEntry input C mode accounting rule next right.1 right.2 gate sample hr
  have hn := firstEntry_unique input C mode accounting rule next sample left.1 right.1 hleft.1 hright.1
  apply Prod.ext hn
  exact hleft.2.symm.trans (by simpa only [hn] using hright.2)

theorem indexedEvent_pairwiseDisjoint (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage) (gate : Set Seed) :
    Pairwise (Disjoint on indexedEvent input C mode accounting rule next gate) := by
  intro left right hne
  apply Set.disjoint_left.mpr
  intro sample hl hr
  exact hne (recordEvent_unique input C mode accounting rule next gate sample left right hl hr)

theorem iUnion_indexedEvent_eq_reachGate (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage) (gate : Set Seed) :
    (⋃ record : Record I, indexedEvent input C mode accounting rule next gate record) =
      reachGate input C mode accounting rule next gate := by
  classical
  ext sample
  constructor
  · intro hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    exact ⟨hr.1, record.1, (recordEvent_firstEntry input C mode accounting rule next _ _ gate sample hr).1.1⟩
  · rintro ⟨hg, he⟩
    let n := Nat.find he
    let startup := publicStartup (run input C mode accounting rule sample n)
    apply Set.mem_iUnion.mpr
    refine ⟨(n, startup), hg, ?_⟩
    apply (entryStartupAt_some_iff input C mode accounting rule next n sample startup).mpr
    exact ⟨⟨Nat.find_spec he, fun k hk => Nat.find_min he hk⟩, rfl⟩

variable [MeasurableSpace Seed]

theorem measurableSet_recordEvent (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (next : I.Stage)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate) :
    MeasurableSet (recordEvent input C mode accounting rule next n startup gate) :=
  (measurable_fst hgate).inter ((measurable_entryStartupAt input C mode accounting rule hm next n) (measurableSet_singleton _))

theorem measurableSet_reachGate (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (next : I.Stage) (gate : Set Seed) (hgate : MeasurableSet gate) :
    MeasurableSet (reachGate input C mode accounting rule next gate) := by
  rw [← iUnion_indexedEvent_eq_reachGate input C mode accounting rule next gate]
  exact MeasurableSet.iUnion (fun record : Record I => measurableSet_recordEvent input C mode accounting rule hm next record.1 record.2 gate hgate)

theorem lintegral_eq_tsum_entry_records (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (next : I.Stage) (gate : Set Seed) (hgate : MeasurableSet gate)
    (μ : Measure (Seed × input.World)) (f : Seed × input.World → ℝ≥0∞) :
    (∫⁻ sample in reachGate input C mode accounting rule next gate, f sample ∂μ) =
      ∑' record : Record I, ∫⁻ sample in indexedEvent input C mode accounting rule next gate record, f sample ∂μ := by
  rw [← iUnion_indexedEvent_eq_reachGate input C mode accounting rule next gate]
  exact lintegral_iUnion
    (fun record : Record I => measurableSet_recordEvent input C mode accounting rule hm next record.1 record.2 gate hgate)
    (indexedEvent_pairwiseDisjoint input C mode accounting rule next gate) f

theorem measure_eq_tsum_entry_records (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (next : I.Stage) (gate : Set Seed) (hgate : MeasurableSet gate) (μ : Measure (Seed × input.World)) :
    μ (reachGate input C mode accounting rule next gate) =
      ∑' record : Record I, μ (indexedEvent input C mode accounting rule next gate record) := by
  simpa only [setLIntegral_const, one_mul] using
    lintegral_eq_tsum_entry_records input C mode accounting rule hm next gate hgate μ (fun _ => 1)

/-- This event contains first entry by its actual record, so no external
FirstEntryAt premise is needed. R is the original available set; every
saved commitment, including pending old corrections, stays occupied. -/
theorem entry_record_continuation_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (penalty : ℝ≥0∞) :
    input.healthyPenalty next.val (R \ startup.committedTools) penalty *
      input.seededWorldLaw ν (recordEvent input C .uncapped accounting policy.val.rule next n startup gate) ≤
      ∫⁻ sample in recordEvent input C .uncapped accounting policy.val.rule next n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n penalty sample ∂input.seededWorldLaw ν := by
  let E := recordEvent input C .uncapped accounting policy.val.rule next n startup gate
  let μ := input.seededWorldLaw ν
  let record := entrySeedStartupAt input C .uncapped accounting policy.val.rule next n
  let η := μ.map record
  let A : Set (Seed × Option (Startup I)) := gate ×ˢ {some startup}
  let D : Set ((Seed × Option (Startup I)) × (input.freshSuffix next.val).World) := A ×ˢ Set.univ
  let joint := fun sample : Seed × input.World => (record sample, input.restrictFreshWorld next.val sample.2)
  let targetPolicy := replayedSuffixRestrictedPolicy input next.val accounting policy.val.rule policy.val.measurable_rule R startup
  let F := fun pair : (Seed × Option (Startup I)) × (input.freshSuffix next.val).World =>
    runPenaltyCharge (input.freshSuffix next.val) (currentRelaxedContract (I.freshSuffix next.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next.val)) targetPolicy.val.rule penalty (pair.1.1, pair.2)
  have hmrecord : Measurable record := measurable_entrySeedStartupAt input C .uncapped accounting policy.val.rule policy.val.measurable_rule next n
  have hmA : MeasurableSet A := hgate.prod (measurableSet_singleton _)
  have hmD : MeasurableSet D := hmA.prod MeasurableSet.univ
  have hmE : MeasurableSet E := measurableSet_recordEvent input C .uncapped accounting policy.val.rule policy.val.measurable_rule next n startup gate hgate
  have hmjoint : Measurable joint := hmrecord.prodMk ((input.measurable_restrictFreshWorld next.val).comp measurable_snd)
  have hmF : Measurable F := (measurable_runPenaltyCharge _ _ _ _ _ targetPolicy.val.measurable_rule penalty).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmap : μ.map joint = η.prod (input.freshSuffix next.val).worldLaw :=
    entrySeedStartupAt_jointFreshSuffixLaw input C .uncapped accounting policy.val ν next n
  have hE : E = record ⁻¹' A := by ext sample; rfl
  have hpre : joint ⁻¹' D = E := by
    rw [hE]
    ext sample
    simp only [joint, D, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hmass : η A = μ E := by rw [Measure.map_apply hmrecord hmA, ← hE]
  have hrow (r : Seed × Option (Startup I)) :
      input.healthyPenalty next.val (R \ startup.committedTools) penalty ≤ ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw :=
    healthyPenalty_le_restrictedSuffix_dirac input next.val accounting policy.val.rule policy.val.measurable_rule R startup r.1 penalty
  change input.healthyPenalty next.val (R \ startup.committedTools) penalty * μ E ≤ _
  calc
    _ = input.healthyPenalty next.val (R \ startup.committedTools) penalty * η A := by rw [hmass]
    _ = ∫⁻ _r in A, input.healthyPenalty next.val (R \ startup.committedTools) penalty ∂η := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in A, ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw ∂η := lintegral_mono hrow
    _ = ∫⁻ pair in D, F pair ∂η.prod (input.freshSuffix next.val).worldLaw := by
      rw [setLIntegral_prod F hmF.aemeasurable, Measure.restrict_univ]
    _ = ∫⁻ sample in E, F (joint sample) ∂μ := by
      rw [← hmap, setLIntegral_map hmD hmF hmjoint, hpre]
    _ ≤ ∫⁻ sample in E, historyComparisonCharge input C .uncapped accounting policy.val.rule n penalty sample ∂μ := by
      apply setLIntegral_mono' hmE
      intro sample hs
      have he := recordEvent_firstEntry input C .uncapped accounting policy.val.rule next n startup gate sample hs
      have h := replayedSuffixRestricted_penaltyCharge_le input C hC accounting policy.val.rule
        policy.val.measurable_rule policy.val.legal R policy.property sample next.val n he.1 penalty
      dsimp only at h
      rw [he.2] at h
      exact h

/-- The unique actual arrival chooses the appropriate clock-indexed
function. No arrival yields zero. This is a proved record decomposition,
not a supplied continuation-cost or partition oracle. -/
noncomputable def pieces (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (f : Record I → Seed × input.World → ℝ≥0∞) (sample : Seed × input.World) : ℝ≥0∞ :=
  ∑' record : Record I, (indexedEvent input C mode accounting rule next Set.univ record).indicator (f record) sample

omit [MeasurableSpace Seed] in
theorem pieces_on_record (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (f : Record I → Seed × input.World → ℝ≥0∞) (gate : Set Seed)
    (record : Record I) (sample : Seed × input.World)
    (hs : sample ∈ indexedEvent input C mode accounting rule next gate record) :
    pieces input C mode accounting rule next f sample = f record sample := by
  classical
  have hm : sample ∈ indexedEvent input C mode accounting rule next Set.univ record := ⟨Set.mem_univ _, hs.2⟩
  unfold pieces
  calc
    _ = (indexedEvent input C mode accounting rule next Set.univ record).indicator (f record) sample := by
      apply tsum_eq_single record
      intro other hne
      apply Set.indicator_of_notMem
      intro hh
      exact hne (recordEvent_unique input C mode accounting rule next Set.univ sample other record hh hm)
    _ = f record sample := Set.indicator_of_mem hm _

omit [MeasurableSpace Seed] in
theorem pieces_zero_of_no_entry (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (f : Record I → Seed × input.World → ℝ≥0∞) (sample : Seed × input.World)
    (h : ¬ ∃ n, (run input C mode accounting rule sample n).cursor = next.val) :
    pieces input C mode accounting rule next f sample = 0 := by
  classical
  unfold pieces
  calc
    _ = ∑' _record : Record I, (0 : ℝ≥0∞) := by
      apply tsum_congr
      intro record
      apply Set.indicator_of_notMem
      intro hs
      exact h ⟨record.1, (recordEvent_firstEntry input C mode accounting rule next record.1 record.2 Set.univ sample hs).1.1⟩
    _ = 0 := tsum_zero

theorem measurable_pieces (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (next : I.Stage)
    (f : Record I → Seed × input.World → ℝ≥0∞) (hf : ∀ record, Measurable (f record)) :
    Measurable (pieces input C mode accounting rule next f) := by
  classical
  unfold pieces
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun entries => entries.measurable_fun_sum fun record _ =>
    (hf record).indicator (measurableSet_recordEvent input C mode accounting rule hm next record.1 record.2 Set.univ MeasurableSet.univ)

theorem lintegral_pieces_eq_tsum (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (next : I.Stage)
    (gate : Set Seed) (hgate : MeasurableSet gate) (μ : Measure (Seed × input.World))
    (f : Record I → Seed × input.World → ℝ≥0∞) :
    (∫⁻ sample in reachGate input C mode accounting rule next gate,
      pieces input C mode accounting rule next f sample ∂μ) =
      ∑' record : Record I, ∫⁻ sample in indexedEvent input C mode accounting rule next gate record,
        f record sample ∂μ := by
  rw [lintegral_eq_tsum_entry_records input C mode accounting rule hm next gate hgate]
  apply tsum_congr
  intro record
  apply setLIntegral_congr_fun (measurableSet_recordEvent input C mode accounting rule hm next record.1 record.2 gate hgate)
  intro sample hs
  exact pieces_on_record input C mode accounting rule next f gate record sample hs

noncomputable def entryContinuationCharge (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (penalty : ℝ≥0∞) : Seed × input.World → ℝ≥0∞ :=
  pieces input C mode accounting rule next (fun record => historyComparisonCharge input C mode accounting rule record.1 penalty)

theorem measurable_entryContinuationCharge (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (next : I.Stage) (penalty : ℝ≥0∞) : Measurable (entryContinuationCharge input C mode accounting rule next penalty) :=
  measurable_pieces input C mode accounting rule hm next _
    (fun record => measurable_historyComparisonCharge input C mode accounting rule hm record.1 penalty)

theorem tsum_entry_continuation_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (gate : Set Seed) (hgate : MeasurableSet gate) (penalty : ℝ≥0∞) :
    (∑' record : Record I, input.healthyPenalty next.val (R \ record.2.committedTools) penalty *
      input.seededWorldLaw ν (indexedEvent input C .uncapped accounting policy.val.rule next gate record)) ≤
      ∫⁻ sample in reachGate input C .uncapped accounting policy.val.rule next gate,
        entryContinuationCharge input C .uncapped accounting policy.val.rule next penalty sample ∂input.seededWorldLaw ν := by
  change _ ≤ ∫⁻ sample in reachGate input C .uncapped accounting policy.val.rule next gate,
    pieces input C .uncapped accounting policy.val.rule next _ sample ∂input.seededWorldLaw ν
  rw [lintegral_pieces_eq_tsum input C .uncapped accounting policy.val.rule policy.val.measurable_rule next gate hgate]
  apply ENNReal.tsum_le_tsum
  intro record
  exact entry_record_continuation_lower input C hC accounting R policy ν next record.1 record.2 gate hgate penalty

/-- Any selection of the actual countable records can be used for good/bad
branch summation. Selection depends on the public clock/snapshot only. -/
def selectedGate (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (records : Set (Record I)) : Set (Seed × input.World) :=
  ⋃ record : records, indexedEvent input C mode accounting rule next gate record.val

omit [MeasurableSpace Seed] in
theorem selectedGate_pairwiseDisjoint (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (gate : Set Seed) (records : Set (Record I)) :
    Pairwise (Disjoint on (fun record : records => indexedEvent input C mode accounting rule next gate record.val)) := by
  intro left right hne
  exact indexedEvent_pairwiseDisjoint input C mode accounting rule next gate
    (fun h : left.val = right.val => hne (Subtype.ext h))

theorem lintegral_selected_pieces_eq_tsum (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (next : I.Stage)
    (gate : Set Seed) (hgate : MeasurableSet gate) (records : Set (Record I)) (μ : Measure (Seed × input.World))
    (f : Record I → Seed × input.World → ℝ≥0∞) :
    (∫⁻ sample in selectedGate input C mode accounting rule next gate records,
      pieces input C mode accounting rule next f sample ∂μ) =
      ∑' record : records, ∫⁻ sample in indexedEvent input C mode accounting rule next gate record.val,
        f record.val sample ∂μ := by
  unfold selectedGate
  rw [lintegral_iUnion (s := fun record : records => indexedEvent input C mode accounting rule next gate record.val)
    (fun record : records => measurableSet_recordEvent input C mode accounting rule hm next record.val.1 record.val.2 gate hgate)
    (selectedGate_pairwiseDisjoint input C mode accounting rule next gate records)]
  apply tsum_congr
  intro record
  apply setLIntegral_congr_fun (measurableSet_recordEvent input C mode accounting rule hm next record.val.1 record.val.2 gate hgate)
  intro sample hs
  exact pieces_on_record input C mode accounting rule next f gate record.val sample hs

theorem selected_measure_eq_tsum (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (next : I.Stage)
    (gate : Set Seed) (hgate : MeasurableSet gate) (records : Set (Record I)) (μ : Measure (Seed × input.World)) :
    μ (selectedGate input C mode accounting rule next gate records) =
      ∑' record : records, μ (indexedEvent input C mode accounting rule next gate record.val) := by
  unfold selectedGate
  exact measure_iUnion (selectedGate_pairwiseDisjoint input C mode accounting rule next gate records)
    (fun record : records => measurableSet_recordEvent input C mode accounting rule hm next record.val.1 record.val.2 gate hgate)

theorem tsum_selected_continuation_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (gate : Set Seed) (hgate : MeasurableSet gate) (records : Set (Record I)) (penalty : ℝ≥0∞) :
    (∑' record : records, input.healthyPenalty next.val (R \ record.val.2.committedTools) penalty *
      input.seededWorldLaw ν (indexedEvent input C .uncapped accounting policy.val.rule next gate record.val)) ≤
      ∫⁻ sample in selectedGate input C .uncapped accounting policy.val.rule next gate records,
        entryContinuationCharge input C .uncapped accounting policy.val.rule next penalty sample ∂input.seededWorldLaw ν := by
  change _ ≤ ∫⁻ sample in selectedGate input C .uncapped accounting policy.val.rule next gate records,
    pieces input C .uncapped accounting policy.val.rule next _ sample ∂input.seededWorldLaw ν
  rw [lintegral_selected_pieces_eq_tsum input C .uncapped accounting policy.val.rule policy.val.measurable_rule next gate hgate records]
  apply ENNReal.tsum_le_tsum
  intro record
  exact entry_record_continuation_lower input C hC accounting R policy ν next record.val.1 record.val.2 gate hgate penalty

end PaperProofs.Common.Native.EntryContinuationPartition
