module

public import PaperProofs.Paid.PDROC_ExactRepresentation_001
public import PaperProofs.Common.ReferenceGlobalCost
public import PaperProofs.Paid.PDROC_OverlayInterface_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

/-- Conditional risk assembly for the free-to-paid overlay. The outstanding
input is an a.e. pathwise success implication from the decoded complete
virtual history, not a risk inequality or a policy qualification. -/
theorem overlay_risk_le_of_sourceHistoryLaw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data)
    (hdom : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw νactual,
      MarkedCompletedSuccess ((P.shadowCompletedHistory fee hfee C accounting actual.rule data sample).map markedHistory) →
        runSuccess (P.input fee hfee) C.val .uncapped accounting actual.rule sample) :
    risk (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      risk (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource := by
  have hma : Measurable (fun sample : SimSeed × (P.input fee hfee).World =>
      (data.sourceSeed sample.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)) :=
    (hm.1.comp measurable_fst).prodMk hlaw.1
  have hms : Measurable (fun sample : SourceSeed × (P.input 0 (by norm_num)).World =>
      (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)) :=
    measurable_fst.prodMk (measurable_completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting
      source.rule source.measurable_rule)
  have hhistoryLaw :
      ((P.input fee hfee).seededWorldLaw νactual).map
        (P.shadowCompletedHistory fee hfee C accounting actual.rule data) =
      ((P.input 0 (by norm_num)).seededWorldLaw νsource).map
        (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule) := by
    have h := congrArg (fun μ => μ.map (Prod.snd : SourceSeed × EntryHistory P.sharedInstance → _)) hlaw.2.2
    rw [Measure.map_map measurable_snd hma, Measure.map_map measurable_snd hms] at h
    exact h
  let bad : Set (EntryHistory P.sharedInstance) :=
    {history | ¬ MarkedCompletedSuccess (history.map markedHistory)}
  have hbad : MeasurableSet bad := (Set.to_countable _).measurableSet
  unfold risk
  calc
    _ ≤ ((P.input fee hfee).seededWorldLaw νactual)
        ((P.shadowCompletedHistory fee hfee C accounting actual.rule data) ⁻¹' bad) := by
      apply measure_mono_ae
      filter_upwards [hdom] with sample hs
      exact fun hfail hgood => hfail (hs hgood)
    _ = (((P.input fee hfee).seededWorldLaw νactual).map
        (P.shadowCompletedHistory fee hfee C accounting actual.rule data)) bad :=
      (Measure.map_apply hlaw.1 hbad).symm
    _ = (((P.input 0 (by norm_num)).seededWorldLaw νsource).map
        (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule)) bad := by
      rw [hhistoryLaw]
    _ = _ := by
      rw [Measure.map_apply
        (measurable_completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule source.measurable_rule) hbad]
      congr 1
      ext sample
      exact (not_congr (runSuccess_iff_markedCompleted (P.input 0 (by norm_num)) C.val C.property.1.1
        .uncapped accounting source.rule source.legal sample)).symm

/-- Both actual fee components include every path. Their separate bounds
combine directly in ENNReal, including infinite source observation bills. -/
theorem overlay_fullBill_le_of_components
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (hobs : expectedObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource + P.overlayObservationIncrement fee)
    (hcorr : P.expectedActualCorrectionBill fee hfee C .uncapped accounting actual.rule νactual ≤ P.overlayCorrectionAmount fee) :
    expectedBill (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource +
        P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee := by
  rw [paid_expectedBill_eq_observation_add_correction P fee hfee C .uncapped accounting actual νactual]
  exact add_le_add hobs hcorr

end PDROC

namespace PDROC

universe u v w

/-- Every auxiliary record at a fixed actual entry belongs to exactly one
cell. This disjointness uses the real entry history, not a semantic range. -/
theorem overlay_recordCells_pairwiseDisjoint
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v}
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) (stage : P.sharedInstance.Stage) :
    Pairwise (fun r r' : AuxiliaryRecord => Disjoint
      (P.recordCell fee hfee C accounting rule data stage r Set.univ)
      (P.recordCell fee hfee C accounting rule data stage r' Set.univ)) := by
  intro r r' hne
  apply Set.disjoint_left.mpr
  rintro sample ⟨entry, he, _, hr⟩ ⟨entry', he', _, hr'⟩
  have hh : entry = entry' := Option.some.inj (he.symm.trans he')
  subst entry'
  exact hne (hr.symm.trans hr')

/-- A disjoint countable family of record gates has total probability at
most one, including abandonment and never-entered complements. -/
theorem overlay_recordCell_mass_sum_le_one {X : Type u} [MeasurableSpace X]
    {Record : Type w} [Countable Record] (μ : Measure X) [IsProbabilityMeasure μ]
    (cell : Record → Set X) (hc : ∀ r, MeasurableSet (cell r))
    (hd : Pairwise (fun r r' => Disjoint (cell r) (cell r'))) :
    (∑' r, μ (cell r)) ≤ 1 := by
  rw [← measure_iUnion hd hc]
  exact prob_le_one

/-- Conditional-on-record error estimates imply an all-path stage error
bound once the genuine Native error event is covered a.e. by writing cells. -/
theorem overlay_error_probability_le_of_cells {X : Type u} [MeasurableSpace X]
    {Record : Type w} [Countable Record] (μ : Measure X) [IsProbabilityMeasure μ]
    (cell : Record → Set X) (hc : ∀ r, MeasurableSet (cell r))
    (hd : Pairwise (fun r r' => Disjoint (cell r) (cell r')))
    (E : Set X) (hcover : E ≤ᵐ[μ] ⋃ r, cell r ∩ E) (p : ℝ≥0∞)
    (hlocal : ∀ r, μ (cell r ∩ E) ≤ p * μ (cell r)) : μ E ≤ p := by
  calc
    μ E ≤ μ (⋃ r, cell r ∩ E) := measure_mono_ae hcover
    _ ≤ ∑' r, μ (cell r ∩ E) := measure_iUnion_le _
    _ ≤ ∑' r, p * μ (cell r) := ENNReal.tsum_le_tsum hlocal
    _ = p * ∑' r, μ (cell r) := ENNReal.tsum_mul_left
    _ ≤ p * 1 := mul_le_mul_right (overlay_recordCell_mass_sum_le_one μ cell hc hd) p
    _ = p := mul_one p

/-- Exact full stage charge from an a.e. pointwise writing-cell partition
and exact cell charges. The partition is an explicit Native obligation. -/
theorem overlay_observation_integral_eq_cell_prices {X : Type u} [MeasurableSpace X]
    {Record : Type w} [Countable Record] (μ : Measure X)
    (cell : Record → Set X) (hc : ∀ r, MeasurableSet (cell r))
    (f : X → ℝ≥0∞) (hf : Measurable f) (price : Record → ℝ≥0∞)
    (hpartition : f =ᵐ[μ] fun x => ∑' r, (cell r).indicator f x)
    (hlocal : ∀ r, (∫⁻ x, (cell r).indicator f x ∂μ) = price r * μ (cell r)) :
    (∫⁻ x, f x ∂μ) = ∑' r, price r * μ (cell r) := by
  rw [lintegral_congr_ae hpartition, lintegral_tsum (fun r => (hf.indicator (hc r)).aemeasurable)]
  exact tsum_congr hlocal

/-- The local `g(min(p,p_f)) ≤ g(p)+g(p_f)` estimate costs one additive
increment per stage, without normalizing a gate or converting infinity. -/
theorem overlay_observation_increment_le_of_cell_prices {X : Type u} [MeasurableSpace X]
    {Record : Type w} [Countable Record] (μ : Measure X) [IsProbabilityMeasure μ]
    (cell : Record → Set X) (hc : ∀ r, MeasurableSet (cell r))
    (hd : Pairwise (fun r r' => Disjoint (cell r) (cell r')))
    (price baseline : Record → ℝ≥0∞) (increment : ℝ≥0∞)
    (hlocal : ∀ r, price r ≤ baseline r + increment) :
    (∑' r, price r * μ (cell r)) ≤ (∑' r, baseline r * μ (cell r)) + increment := by
  calc
    _ ≤ ∑' r, (baseline r + increment) * μ (cell r) :=
      ENNReal.tsum_le_tsum (fun r => mul_le_mul_left (hlocal r) _)
    _ = (∑' r, baseline r * μ (cell r)) + increment * ∑' r, μ (cell r) := by
      simp_rw [add_mul]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ (∑' r, baseline r * μ (cell r)) + increment * 1 :=
      add_le_add le_rfl (mul_le_mul_right (overlay_recordCell_mass_sum_le_one μ cell hc hd) increment)
    _ = _ := by rw [mul_one]

end PDROC

namespace PDROC

universe u v

theorem overlay_actualOrdinaryDecision_of_no_entry
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hfee).World)
    (hnone : entryHistory (P.input fee hfee) C.val .uncapped accounting actual.rule stage sample = none) :
    P.actualOrdinaryDecision fee hfee C .uncapped accounting actual.rule sample stage = none := by
  have hw (n : ℕ) : (run (P.input fee hfee) C.val .uncapped accounting actual.rule sample n).ledger.written stage = none :=
    (run_cursorInvariant (P.input fee hfee) C.val .uncapped accounting actual.rule actual.legal sample n).future_written stage
      (run_cursor_lt_of_no_entry (P.input fee hfee) C.val .uncapped accounting actual.rule actual.legal sample stage hnone n)
  classical
  simp [PaperProofs.Paid.Parameters.actualOrdinaryDecision, hw]

/-- All-path actual stage error probability is bounded by p_f. The only
simulation inputs are the original actual stage realization and complete
record-cell identities; neither risk nor fee conclusions are assumed. -/
theorem overlay_actualWriteError_probability_le
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (ν : Measure SimSeed) [IsProbabilityMeasure ν]
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlayDraft.OverlaySimulatorData P.sharedInstance SourceSeed SimSeed)
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting ν actual.rule data)
    (hcells : OverlayDraft.OverlayRecordCells P fee hfee C accounting ν actual.rule data)
    (stage : P.sharedInstance.Stage) :
    (P.input fee hfee).seededWorldLaw ν {sample | P.actualWriteError fee hfee C accounting actual.rule stage sample} ≤
      ENNReal.ofReal (P.overlayError fee) := by
  classical
  let WritingRecord := {record : AuxiliaryRecord // ∃ decision, record.decision = some decision}
  let μ := (P.input fee hfee).seededWorldLaw ν
  let cell : WritingRecord → Set (SimSeed × (P.input fee hfee).World) := fun r =>
    P.recordCell fee hfee C accounting actual.rule data.toRecordSimulatorData stage r.val Set.univ
  let E := {sample | P.actualWriteError fee hfee C accounting actual.rule stage sample}
  have hcell (r : WritingRecord) : MeasurableSet (cell r) := by
    obtain ⟨decision, hd⟩ := r.property
    exact (hcells stage r.val decision hd Set.univ MeasurableSet.univ).1
  have hdisjoint : Pairwise (fun r r' : WritingRecord => Disjoint (cell r) (cell r')) := by
    intro r r' hne
    exact overlay_recordCells_pairwiseDisjoint P fee hfee C accounting actual.rule data.toRecordSimulatorData stage
      (fun h => hne (Subtype.ext h))
  have hcover : E ≤ᵐ[μ] ⋃ r, cell r ∩ E := by
    filter_upwards [hstage] with sample hs herror
    cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting actual.rule stage sample with
    | none =>
      have hn := overlay_actualOrdinaryDecision_of_no_entry P fee hfee C accounting actual stage sample he
      change P.actualOrdinaryDecision fee hfee C .uncapped accounting actual.rule sample stage = some _ at herror
      rw [hn] at herror
      cases herror
    | some entry =>
      let record := data.record sample.1 stage entry
      cases hd : record.decision with
      | none =>
        have hh := hs stage entry he
        change (match record.decision with | none => _ | some _ => _) at hh
        rw [hd] at hh
        change P.actualOrdinaryDecision fee hfee C .uncapped accounting actual.rule sample stage = some _ at herror
        rw [hh.1] at herror
        cases herror
      | some decision =>
        apply Set.mem_iUnion.mpr
        refine ⟨⟨record, decision, hd⟩, ?_⟩
        exact ⟨⟨entry, he, Set.mem_univ _, rfl⟩, herror⟩
  apply overlay_error_probability_le_of_cells μ cell hcell hdisjoint E hcover (ENNReal.ofReal (P.overlayError fee))
  intro r
  obtain ⟨decision, hd⟩ := r.property
  have heq := (hcells stage r.val decision hd Set.univ MeasurableSet.univ).2.2.2.1
  change μ (cell r ∩ E) = ENNReal.ofReal (P.overlayRecordTarget fee r.val) * μ (cell r) at heq
  rw [heq]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_right _ _)) _

end PDROC

namespace PDROC

universe u v

/-- Every actual execution has a different stage and a genuine erroneous
actual write. This prefix bound includes payments on every failing path. -/
theorem overlay_prefixExecutionCount_le_errors
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (sample : Seed × (P.input fee hfee).World) (n : ℕ) :
    ((run (P.input fee hfee) C.val .uncapped accounting actual.rule sample n).ledger.executions.length : ℝ≥0∞) ≤
      ∑ stage : P.sharedInstance.Stage,
        {sample | P.actualWriteError fee hfee C accounting actual.rule stage sample}.indicator
          (fun _ => (1 : ℝ≥0∞)) sample := by
  classical
  let L := (run (P.input fee hfee) C.val .uncapped accounting actual.rule sample n).ledger
  let errors := Finset.univ.filter (fun stage => P.actualWriteError fee hfee C accounting actual.rule stage sample)
  have hwf := run_ledgerWellFormed (P.input fee hfee) C.val .uncapped accounting actual.rule actual.legal sample n
  have hsub : (L.executions.map (·.handle.stage)).toFinset ⊆ errors := by
    intro stage hm
    obtain ⟨execution, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hg := hwf.genuine execution he
    rw [run_truth (P.input fee hfee) C.val .uncapped accounting actual.rule actual.legal sample n] at hg
    exact actualOrdinaryDecision_of_written P fee hfee C .uncapped accounting actual.rule actual.legal
      sample n execution.handle.stage _ hg.1
  have hcount : L.executions.length ≤ errors.card := by
    have h := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hwf.execution_stages, List.length_map] at h
    exact h
  calc
    (L.executions.length : ℝ≥0∞) ≤ (errors.card : ℝ≥0∞) := by exact_mod_cast hcount
    _ = _ := by
      simp only [errors, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
        Set.indicator_apply, Set.mem_ofPred_eq]
      apply Finset.sum_congr rfl
      intro stage _
      split_ifs <;> norm_num

/-- The full correction bill is the supremum of actual prefix payments,
not a bill conditioned on completion or success. -/
theorem overlay_runActualCorrectionBill_le_errors
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (sample : Seed × (P.input fee hfee).World) :
    P.runActualCorrectionBill fee hfee C .uncapped accounting actual.rule sample ≤
      (∑ stage : P.sharedInstance.Stage,
        {sample | P.actualWriteError fee hfee C accounting actual.rule stage sample}.indicator
          (fun _ => (1 : ℝ≥0∞)) sample) * ENNReal.ofReal (fee : ℝ) := by
  unfold PaperProofs.Paid.Parameters.runActualCorrectionBill
  apply iSup_le
  intro n
  rw [paid_correctionBill_eq_count]
  exact mul_le_mul_left (overlay_prefixExecutionCount_le_errors P fee hfee C accounting actual sample n) _

/-- Complete all-path correction budget from actual-stage and record-cell
identities. There is no nonreturn-null, finite-ET or successful-path premise. -/
theorem overlay_expectedActualCorrectionBill_le
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (ν : Measure SimSeed) [IsProbabilityMeasure ν]
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlayDraft.OverlaySimulatorData P.sharedInstance SourceSeed SimSeed)
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting ν actual.rule data)
    (hcells : OverlayDraft.OverlayRecordCells P fee hfee C accounting ν actual.rule data) :
    P.expectedActualCorrectionBill fee hfee C .uncapped accounting actual.rule ν ≤ P.overlayCorrectionAmount fee := by
  let μ := (P.input fee hfee).seededWorldLaw ν
  let E := fun stage => {sample | P.actualWriteError fee hfee C accounting actual.rule stage sample}
  have hE (stage : P.sharedInstance.Stage) : MeasurableSet (E stage) :=
    (hcells stage ⟨[], some false⟩ false rfl Set.univ MeasurableSet.univ).2.1
  have hi : (∫⁻ sample, ∑ stage : P.sharedInstance.Stage, (E stage).indicator (fun _ => (1 : ℝ≥0∞)) sample ∂μ) =
      ∑ stage : P.sharedInstance.Stage, μ (E stage) := by
    rw [lintegral_finsetSum _ (fun stage _ => measurable_const.indicator (hE stage))]
    apply Finset.sum_congr rfl
    intro stage _
    exact lintegral_indicator_one (hE stage)
  have hsum : (∑ stage : P.sharedInstance.Stage, μ (E stage)) ≤
      (P.certificate.stages : ℝ≥0∞) * ENNReal.ofReal (P.overlayError fee) := by
    have hn : Fintype.card P.sharedInstance.Stage = P.certificate.stages := by
      change Fintype.card (Fin P.sharedInstance.stageCount) = _
      rw [Fintype.card_fin, P.stageCount_eq]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun stage _ =>
      overlay_actualWriteError_probability_le P fee hfee C accounting ν actual data hstage hcells stage)
    simpa only [Finset.sum_const, Finset.card_univ, hn, nsmul_eq_mul] using h
  unfold PaperProofs.Paid.Parameters.expectedActualCorrectionBill
  calc
    _ ≤ ∫⁻ sample, (∑ stage : P.sharedInstance.Stage,
          (E stage).indicator (fun _ => (1 : ℝ≥0∞)) sample) * ENNReal.ofReal (fee : ℝ) ∂μ :=
      lintegral_mono (overlay_runActualCorrectionBill_le_errors P fee hfee C accounting actual)
    _ = (∑ stage : P.sharedInstance.Stage, μ (E stage)) * ENNReal.ofReal (fee : ℝ) := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hi]
    _ ≤ ((P.certificate.stages : ℝ≥0∞) * ENNReal.ofReal (P.overlayError fee)) * ENNReal.ofReal (fee : ℝ) :=
      mul_le_mul_left hsum _
    _ = P.overlayCorrectionAmount fee := by
      unfold PaperProofs.Paid.Parameters.overlayCorrectionAmount
      rw [ENNReal.ofReal_mul (by exact_mod_cast hfee)]
      ring

end PDROC

namespace PDROC

universe u v

abbrev OverlayWritingRecord := {record : AuxiliaryRecord // ∃ decision, record.decision = some decision}

noncomputable def overlay_runRecordValue
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v}
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) (stage : P.sharedInstance.Stage)
    (value : AuxiliaryRecord → SimSeed × (P.input fee hfee).World → ℝ≥0∞)
    (sample : SimSeed × (P.input fee hfee).World) : ℝ≥0∞ :=
  match entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample with
  | none => 0
  | some entry =>
      let record := data.record sample.1 stage entry
      match record.decision with
      | none => 0
      | some _ => value record sample

/-- Pointwise record partition, before any expectation or performance bound. -/
theorem overlay_runRecordValue_eq_tsum
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v}
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) (stage : P.sharedInstance.Stage)
    (value : AuxiliaryRecord → SimSeed × (P.input fee hfee).World → ℝ≥0∞)
    (sample : SimSeed × (P.input fee hfee).World) :
    overlay_runRecordValue P fee hfee C accounting rule data stage value sample =
      ∑' r : OverlayWritingRecord,
        (P.recordCell fee hfee C accounting rule data stage r.val Set.univ).indicator (value r.val) sample := by
  classical
  cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample with
  | none =>
    have hnot (r : OverlayWritingRecord) : sample ∉ P.recordCell fee hfee C accounting rule data stage r.val Set.univ := by
      rintro ⟨entry, hentry, _, _⟩
      rw [he] at hentry
      cases hentry
    simp only [overlay_runRecordValue, he, Set.indicator_of_notMem (hnot _), tsum_zero]
  | some entry =>
    let record := data.record sample.1 stage entry
    have hmem_iff (r : OverlayWritingRecord) :
        sample ∈ P.recordCell fee hfee C accounting rule data stage r.val Set.univ ↔ record = r.val := by
      constructor
      · rintro ⟨other, hother, _, hr⟩
        have hh : other = entry := Option.some.inj (hother.symm.trans he)
        subst other
        exact hr
      · intro hr
        exact ⟨entry, he, Set.mem_univ _, hr⟩
    cases hd : (data.record sample.1 stage entry).decision with
    | none =>
      have hnot (r : OverlayWritingRecord) : sample ∉ P.recordCell fee hfee C accounting rule data stage r.val Set.univ := by
        intro hm
        have hr := (hmem_iff r).mp hm
        obtain ⟨decision, hdecision⟩ := r.property
        rw [← hr, hd] at hdecision
        cases hdecision
      simp only [overlay_runRecordValue, he, hd, Set.indicator_of_notMem (hnot _), tsum_zero]
    | some decision =>
      let r : OverlayWritingRecord := ⟨record, decision, hd⟩
      rw [tsum_eq_single r]
      · simp only [overlay_runRecordValue, he, hd]
        rw [Set.indicator_of_mem ((hmem_iff r).mpr rfl)]
      · intro other hne
        apply Set.indicator_of_notMem
        intro hm
        exact hne (Subtype.ext ((hmem_iff other).mp hm).symm)

/-- The selected-record potential has exactly its unnormalized cell-price
integral; all never-entered and abandonment branches are retained at zero. -/
theorem overlay_runRecordPrice_integral
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SimSeed]
    (ν : Measure SimSeed) (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) (stage : P.sharedInstance.Stage)
    (price : AuxiliaryRecord → ℝ≥0∞)
    (hmeas : ∀ r : OverlayWritingRecord, MeasurableSet
      (P.recordCell fee hfee C accounting rule data stage r.val Set.univ)) :
    (∫⁻ sample, overlay_runRecordValue P fee hfee C accounting rule data stage (fun record _ => price record) sample
      ∂(P.input fee hfee).seededWorldLaw ν) =
      ∑' r : OverlayWritingRecord, price r.val *
        (P.input fee hfee).seededWorldLaw ν (P.recordCell fee hfee C accounting rule data stage r.val Set.univ) := by
  simp_rw [overlay_runRecordValue_eq_tsum]
  rw [lintegral_tsum (fun r => (measurable_const.indicator (hmeas r)).aemeasurable)]
  apply tsum_congr
  intro r
  exact lintegral_indicator_const (hmeas r) _

/-- Stage observations are supported on writing records. Nonreturn and
failure charges are not removed; this uses the actual stage witness. -/
theorem overlay_stageObservation_eq_runRecordValue_of_none_zero
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SimSeed]
    (ν : Measure SimSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (stage : P.sharedInstance.Stage)
    (hzero : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting actual.rule stage sample = some entry →
        (data.record sample.1 stage entry).decision = none →
          P.paidRunReviewCount fee hfee C .uncapped accounting actual.rule sample stage = 0) :
    (P.stageObservationBill fee hfee C accounting actual.rule stage) =ᵐ[(P.input fee hfee).seededWorldLaw ν]
      overlay_runRecordValue P fee hfee C accounting actual.rule data stage
        (fun _ => P.stageObservationBill fee hfee C accounting actual.rule stage) := by
  filter_upwards [hzero] with sample hs
  cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting actual.rule stage sample with
  | none =>
    rw [overlay_runRecordValue, he]
    rw [stageObservationBill_eq_runStageObservationBill]
    exact runStageObservationBill_zero_of_no_entry (P.input fee hfee) C.val .uncapped accounting
      actual.rule actual.legal stage sample he
  | some entry =>
    let record := data.record sample.1 stage entry
    cases hd : (data.record sample.1 stage entry).decision with
    | none =>
      have hz := hs entry he hd
      simp only [overlay_runRecordValue, he, hd]
      unfold PaperProofs.Paid.Parameters.stageObservationBill
      rw [hz]
      simp
    | some decision => simp only [overlay_runRecordValue, he, hd]

theorem overlay_stageObservation_eq_runRecordValue
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (ν : Measure SimSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlayDraft.OverlaySimulatorData P.sharedInstance SourceSeed SimSeed)
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting ν actual.rule data)
    (stage : P.sharedInstance.Stage) :
    (P.stageObservationBill fee hfee C accounting actual.rule stage) =ᵐ[(P.input fee hfee).seededWorldLaw ν]
      overlay_runRecordValue P fee hfee C accounting actual.rule data.toRecordSimulatorData stage
        (fun _ => P.stageObservationBill fee hfee C accounting actual.rule stage) := by
  apply overlay_stageObservation_eq_runRecordValue_of_none_zero P fee hfee C accounting ν actual
    data.toRecordSimulatorData stage
  filter_upwards [hstage] with sample hs entry he hd
  have hh := hs stage entry he
  change (match (data.record sample.1 stage entry).decision with | none => _ | some _ => _) at hh
  rw [hd] at hh
  exact hh.2

end PDROC

namespace PDROC

universe u v

def overlayHistoryStageLevel {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage) : ℕ :=
  ((historyObservations history stage).map (fun symbol => if symbol = 1 then (1 : ℤ) else -1)).sum.natAbs

/-- A nonnegative analytical potential decoded from the full completed
history. Its none value is not an actual bill or a nonreturn-cost convention. -/
noncomputable def overlayHistoryStagePrice (P : Parameters) (stage : P.sharedInstance.Stage) :
    EntryHistory P.sharedInstance → ℝ≥0∞
  | none => 0
  | some history => if (historyWritten history stage).isSome = true then
      ENNReal.ofReal (P.binarySymmetric.endpointCharge (overlayHistoryStageLevel history stage) : ℝ) else 0

theorem overlayHistoryStageLevel_eq_recordLevel {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (record : AuxiliaryRecord)
    (hword : record.observations.map Fin.val = historyObservations history stage) :
    overlayHistoryStageLevel history stage = record.level := by
  unfold overlayHistoryStageLevel AuxiliaryRecord.level AuxiliaryRecord.score
  rw [← hword, List.map_map]
  rfl

/-- Complete original-record alignment identifies every selected writing
potential with its full shadow-history potential. Unentered stages may
only add nonnegative shadow potential, so no future-entry converse is used. -/
theorem overlay_runRecordPrice_le_shadowHistoryPrice
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (ν : Measure SimSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (halign : P.SourceRecordAlignment fee hfee C accounting ν actual.rule data)
    (hnone : (P.input fee hfee).seededWorldLaw ν {sample |
      completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} = 0)
    (stage : P.sharedInstance.Stage) :
    (fun sample => overlay_runRecordValue P fee hfee C accounting actual.rule data stage
      (fun record _ => ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ)) sample) ≤ᵐ[
        (P.input fee hfee).seededWorldLaw ν]
      (fun sample => overlayHistoryStagePrice P stage (P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)) := by
  have hae : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample ≠ none := by
    apply ae_iff.mpr
    simpa only [not_not] using hnone
  filter_upwards [halign, hae] with sample hs hh
  cases hc : completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample with
  | none => exact (hh hc).elim
  | some history =>
    cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting actual.rule stage sample with
    | none =>
      simp only [overlay_runRecordValue, he]
      exact zero_le
    | some entry =>
      let record := data.record sample.1 stage entry
      have hrecord := hs history hc stage entry he
      have hword := hrecord.2.2.2.1
      have hdecision := hrecord.2.2.2.2
      have hlevel := overlayHistoryStageLevel_eq_recordLevel (data.shadow sample.1 history) stage record hword
      cases hd : (data.record sample.1 stage entry).decision with
      | none =>
        simp only [overlay_runRecordValue, he, hd]
        exact zero_le
      | some decision =>
        have hw : historyWritten (data.shadow sample.1 history) stage = some decision := hdecision.symm.trans hd
        simp only [overlay_runRecordValue, he, hd, PaperProofs.Paid.Parameters.shadowCompletedHistory,
          hc, Option.map_some, overlayHistoryStagePrice, hw, Option.isSome_some, ↓reduceIte, hlevel]
        exact le_rfl

/-- The original complete source-history law transports this analytical
potential exactly, retaining the same source seed and entire history law. -/
theorem overlay_historyStagePrice_integral_eq_source
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data)
    (stage : P.sharedInstance.Stage) :
    (∫⁻ sample, overlayHistoryStagePrice P stage (P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)
        ∂(P.input fee hfee).seededWorldLaw νactual) =
      ∫⁻ sample, overlayHistoryStagePrice P stage
        (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)
        ∂(P.input 0 (by norm_num)).seededWorldLaw νsource := by
  have hma : Measurable (fun sample : SimSeed × (P.input fee hfee).World =>
      (data.sourceSeed sample.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)) :=
    (hm.1.comp measurable_fst).prodMk hlaw.1
  have hms : Measurable (fun sample : SourceSeed × (P.input 0 (by norm_num)).World =>
      (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)) :=
    measurable_fst.prodMk (measurable_completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting
      source.rule source.measurable_rule)
  let project := fun pair : SourceSeed × EntryHistory P.sharedInstance => overlayHistoryStagePrice P stage pair.2
  have hmp : Measurable project := (measurable_of_countable (overlayHistoryStagePrice P stage)).comp measurable_snd
  have h := congrArg (fun μ => ∫⁻ pair, project pair ∂μ) hlaw.2.2
  rw [lintegral_map hmp hma, lintegral_map hmp hms] at h
  exact h

end PDROC

namespace PDROC

universe u v

/-- D06's already proved boundary-cell cost is exactly its selected-record
endpoint potential. This helper is reusable without a concrete simulator. -/
theorem overlay_boundary_stageObservation_eq_recordPotential
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (ν : Measure SimSeed) (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hstage : P.BoundaryStageRealization fee hfee C accounting ν actual.rule data)
    (hcells : P.BoundaryRecordCells fee hfee C accounting ν actual.rule data)
    (stage : P.sharedInstance.Stage) :
    (∫⁻ sample, P.stageObservationBill fee hfee C accounting actual.rule stage sample ∂(P.input fee hfee).seededWorldLaw ν) =
      ∫⁻ sample, overlay_runRecordValue P fee hfee C accounting actual.rule data stage
        (fun record _ => ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ)) sample
        ∂(P.input fee hfee).seededWorldLaw ν := by
  let μ := (P.input fee hfee).seededWorldLaw ν
  let cell := fun r : OverlayWritingRecord => P.recordCell fee hfee C accounting actual.rule data stage r.val Set.univ
  have hc (r : OverlayWritingRecord) : MeasurableSet (cell r) := by
    obtain ⟨decision, hd⟩ := r.property
    exact (hcells stage r.val decision hd Set.univ MeasurableSet.univ).1
  have hf : Measurable (P.stageObservationBill fee hfee C accounting actual.rule stage) := by
    have hfun : P.stageObservationBill fee hfee C accounting actual.rule stage =
        runStageObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule stage := by
      funext sample
      exact stageObservationBill_eq_runStageObservationBill P fee hfee C accounting actual.rule stage sample
    rw [hfun]
    exact measurable_runStageObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule actual.measurable_rule stage
  have hz : ∀ᵐ sample ∂μ, ∀ entry,
      entryHistory (P.input fee hfee) C.val .uncapped accounting actual.rule stage sample = some entry →
        (data.record sample.1 stage entry).decision = none →
          P.paidRunReviewCount fee hfee C .uncapped accounting actual.rule sample stage = 0 := by
    filter_upwards [hstage] with sample hs entry he hd
    have hh := hs stage entry he
    change (match (data.record sample.1 stage entry).decision with | none => _ | some _ => _) at hh
    rw [hd] at hh
    exact hh.2
  have hp := overlay_stageObservation_eq_runRecordValue_of_none_zero P fee hfee C accounting ν actual data stage hz
  have hpartition : (P.stageObservationBill fee hfee C accounting actual.rule stage) =ᵐ[μ]
      (fun sample => ∑' r : OverlayWritingRecord, (cell r).indicator (P.stageObservationBill fee hfee C accounting actual.rule stage) sample) := by
    filter_upwards [hp] with sample hs
    exact hs.trans (overlay_runRecordValue_eq_tsum P fee hfee C accounting actual.rule data stage
      (fun _ => P.stageObservationBill fee hfee C accounting actual.rule stage) sample)
  calc
    _ = ∑' r : OverlayWritingRecord,
        ENNReal.ofReal (P.binarySymmetric.endpointCharge r.val.level : ℝ) * μ (cell r) := by
      apply overlay_observation_integral_eq_cell_prices μ cell hc _ hf _ hpartition
      intro r
      obtain ⟨decision, hd⟩ := r.property
      exact (hcells stage r.val decision hd Set.univ MeasurableSet.univ).2.1
    _ = _ := (overlay_runRecordPrice_integral P fee hfee C accounting ν actual.rule data stage
      (fun record => ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ)) hc).symm

/-- The concrete old D06 fold does not invent a write at an unentered
stage. Hence its complete-history potential and selected-record potential
coincide a.e.; this is a reuse of the frozen D06 construction. -/
theorem overlay_simulator_historyPotential_eq_recordPotential
    (P : Parameters) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (stage : P.sharedInstance.Stage) :
    (fun sample => overlayHistoryStagePrice P stage
      (P.shadowCompletedHistory 0 (by norm_num) C accounting
        (simulatorPolicy P 0 (by norm_num) C accounting source).rule (simulatorData P 0 (by norm_num) source.rule) sample)) =ᵐ[
          (P.input 0 (by norm_num)).seededWorldLaw (simulatorSeedLaw P ν)]
      (fun sample => overlay_runRecordValue P 0 (by norm_num) C accounting
        (simulatorPolicy P 0 (by norm_num) C accounting source).rule (simulatorData P 0 (by norm_num) source.rule) stage
        (fun record _ => ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ)) sample) := by
  let actual := simulatorPolicy P 0 (by norm_num) C accounting source
  let data := simulatorData P 0 (by norm_num) source.rule
  have hrep := simulatorBoundaryRepresentation P 0 (by norm_num) C accounting source ν hfinite
  have halign := hrep.2.2.1
  have hnone := hrep.2.2.2.2.2.2.2.1
  have hae : ∀ᵐ sample ∂(P.input 0 (by norm_num)).seededWorldLaw (simulatorSeedLaw P ν),
      completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule sample ≠ none := by
    apply ae_iff.mpr
    simpa only [not_not] using hnone
  filter_upwards [halign, hae] with sample hs hn
  change overlayHistoryStagePrice P stage (P.shadowCompletedHistory 0 (by norm_num) C accounting actual.rule data sample) =
    overlay_runRecordValue P 0 (by norm_num) C accounting actual.rule data stage
      (fun record _ => ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ)) sample
  cases hh : completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule sample with
  | none => exact (hn hh).elim
  | some history =>
    cases he : entryHistory (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule stage sample with
    | none =>
      obtain ⟨n, hhalt, _, hhistory⟩ := (completedHistory_some_iff (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule sample history).mp hh
      obtain ⟨k, _, hp⟩ := run_has_prefix (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule actual.legal sample n
      have hw := prefix_historyWritten (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule sample.1 _ _ hp stage
      rw [hhistory] at hw
      have hledger := (run_cursorInvariant (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule actual.legal sample n).future_written stage
        (run_cursor_lt_of_no_entry (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule actual.legal sample stage he n)
      have hactual : historyWritten history stage = none := hw.trans hledger
      have hshadow := ((simulatorReplay_sameProjection (simulatorSeedDraw P 0 (by norm_num) source.rule) sample.1 history).2.2.2.1 stage).mp hactual
      change historyWritten (data.shadow sample.1 history) stage = none at hshadow
      simp only [PaperProofs.Paid.Parameters.shadowCompletedHistory, hh, Option.map_some,
        overlayHistoryStagePrice, hshadow, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        overlay_runRecordValue, he]
    | some entry =>
      let record := data.record sample.1 stage entry
      have hr := hs history hh stage entry he
      have hl := overlayHistoryStageLevel_eq_recordLevel (data.shadow sample.1 history) stage record hr.2.2.2.1
      have hd := hr.2.2.2.2
      change record.decision = historyWritten (data.shadow sample.1 history) stage at hd
      cases hdecision : (data.record sample.1 stage entry).decision with
      | none =>
        have hw : historyWritten (data.shadow sample.1 history) stage = none := hd.symm.trans hdecision
        simp only [PaperProofs.Paid.Parameters.shadowCompletedHistory, hh, Option.map_some,
          overlayHistoryStagePrice, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          overlay_runRecordValue, he, hdecision]
      | some decision =>
        have hw : historyWritten (data.shadow sample.1 history) stage = some decision := hd.symm.trans hdecision
        simp only [PaperProofs.Paid.Parameters.shadowCompletedHistory, hh, Option.map_some,
          overlayHistoryStagePrice, hw, Option.isSome_some, ↓reduceIte,
          overlay_runRecordValue, he, hdecision, hl]
        rfl

/-- The complete source-history endpoint potential is bounded by the
original all-path source observation bill, using the already closed D06.
The sole finiteness assumption is the original full source bill. -/
theorem overlay_sourceHistoryPotential_le_observation
    (P : Parameters) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    (∑ stage : P.sharedInstance.Stage, ∫⁻ sample, overlayHistoryStagePrice P stage
      (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)
      ∂(P.input 0 (by norm_num)).seededWorldLaw ν) ≤
        expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν := by
  let actual := simulatorPolicy P 0 (by norm_num) C accounting source
  let data := simulatorData P 0 (by norm_num) source.rule
  have hrep := simulatorBoundaryRepresentation P 0 (by norm_num) C accounting source ν hfinite
  have hstage (stage : P.sharedInstance.Stage) :
      (∫⁻ sample, overlayHistoryStagePrice P stage
        (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)
        ∂(P.input 0 (by norm_num)).seededWorldLaw ν) =
      ∫⁻ sample, P.stageObservationBill 0 (by norm_num) C accounting actual.rule stage sample
        ∂(P.input 0 (by norm_num)).seededWorldLaw (simulatorSeedLaw P ν) := by
    rw [← overlay_historyStagePrice_integral_eq_source P 0 (by norm_num) C accounting ν (simulatorSeedLaw P ν)
      source actual data hrep.1 hrep.2.2.2.1 stage]
    rw [lintegral_congr_ae (overlay_simulator_historyPotential_eq_recordPotential P C accounting source ν hfinite stage)]
    exact (overlay_boundary_stageObservation_eq_recordPotential P 0 (by norm_num) C accounting
      (simulatorSeedLaw P ν) actual data hrep.2.2.2.2.1 hrep.2.2.2.2.2.1 stage).symm
  calc
    _ = ∑ stage : P.sharedInstance.Stage, ∫⁻ sample, P.stageObservationBill 0 (by norm_num) C accounting actual.rule stage sample
        ∂(P.input 0 (by norm_num)).seededWorldLaw (simulatorSeedLaw P ν) := Finset.sum_congr rfl (fun stage _ => hstage stage)
    _ = expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule (simulatorSeedLaw P ν) := by
      simp_rw [stageObservationBill_eq_runStageObservationBill]
      exact (expectedObservationBill_eq_sum_stage (P.input 0 (by norm_num)) C.val .uncapped accounting actual.rule
        actual.legal actual.measurable_rule (simulatorSeedLaw P ν)).symm
    _ ≤ _ := simulator_observation_le_source P 0 (by norm_num) C accounting source ν hfinite

end PDROC

namespace PDROC

universe u v

/-- Full source-history law transfers a.s. return from the original
finite-full-bill free source. No extra finite-ET assumption is introduced. -/
theorem overlay_completedHistory_none_zero_of_sourceHistoryLaw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) [IsProbabilityMeasure νsource] (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource ≠ ⊤) :
    (P.input fee hfee).seededWorldLaw νactual {sample |
      completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} = 0 := by
  have hma : Measurable (fun sample : SimSeed × (P.input fee hfee).World =>
      (data.sourceSeed sample.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)) :=
    (hm.1.comp measurable_fst).prodMk hlaw.1
  have hms : Measurable (fun sample : SourceSeed × (P.input 0 (by norm_num)).World =>
      (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)) :=
    measurable_fst.prodMk (measurable_completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting
      source.rule source.measurable_rule)
  have h := congrArg (fun μ => μ (Set.univ ×ˢ {(none : EntryHistory P.sharedInstance)})) hlaw.2.2
  have hs : MeasurableSet (Set.univ ×ˢ {(none : EntryHistory P.sharedInstance)} : Set (SourceSeed × EntryHistory P.sharedInstance)) :=
    MeasurableSet.univ.prod (measurableSet_singleton none)
  rw [Measure.map_apply hma hs, Measure.map_apply hms hs] at h
  have heq : (P.input fee hfee).seededWorldLaw νactual {sample |
        completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} =
      (P.input 0 (by norm_num)).seededWorldLaw νsource {sample |
        completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample = none} := by
    convert h using 1 <;> congr 1 <;> ext sample <;>
      simp [PaperProofs.Paid.Parameters.shadowCompletedHistory]
  rw [heq]
  exact paid_finiteExpectedBill_completedHistory P 0 (by norm_num) C.val .uncapped accounting source νsource hfinite

/-- Per-stage all-path observation increment. Only the explicitly proved
history law, source-record alignment, actual stage experiment and record
cells are used; the baseline potential is decoded from the original source. -/
theorem overlay_stageObservation_le_sourcePotential_add
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) [IsProbabilityMeasure νsource]
    (νactual : Measure SimSeed) [IsProbabilityMeasure νactual]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlayDraft.OverlaySimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data.toRecordSimulatorData)
    (halign : P.SourceRecordAlignment fee hfee C accounting νactual actual.rule data.toRecordSimulatorData)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data.toRecordSimulatorData)
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting νactual actual.rule data)
    (hcells : OverlayDraft.OverlayRecordCells P fee hfee C accounting νactual actual.rule data)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource ≠ ⊤)
    (stage : P.sharedInstance.Stage) :
    (∫⁻ sample, P.stageObservationBill fee hfee C accounting actual.rule stage sample ∂(P.input fee hfee).seededWorldLaw νactual) ≤
      (∫⁻ sample, overlayHistoryStagePrice P stage
        (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)
        ∂(P.input 0 (by norm_num)).seededWorldLaw νsource) + P.binarySymmetric.rocPrice (P.overlayError fee) := by
  let μ := (P.input fee hfee).seededWorldLaw νactual
  let cell := fun r : OverlayWritingRecord =>
    P.recordCell fee hfee C accounting actual.rule data.toRecordSimulatorData stage r.val Set.univ
  have hc (r : OverlayWritingRecord) : MeasurableSet (cell r) := by
    obtain ⟨decision, hd⟩ := r.property
    exact (hcells stage r.val decision hd Set.univ MeasurableSet.univ).1
  have hdisjoint : Pairwise (fun r r' : OverlayWritingRecord => Disjoint (cell r) (cell r')) := by
    intro r r' hne
    exact overlay_recordCells_pairwiseDisjoint P fee hfee C accounting actual.rule data.toRecordSimulatorData stage
      (fun h => hne (Subtype.ext h))
  have hf : Measurable (P.stageObservationBill fee hfee C accounting actual.rule stage) := by
    have hfun : P.stageObservationBill fee hfee C accounting actual.rule stage =
        runStageObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule stage := by
      funext sample
      exact stageObservationBill_eq_runStageObservationBill P fee hfee C accounting actual.rule stage sample
    rw [hfun]
    exact measurable_runStageObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule actual.measurable_rule stage
  have hp := overlay_stageObservation_eq_runRecordValue P fee hfee C accounting νactual actual data hstage stage
  have hpartition : (P.stageObservationBill fee hfee C accounting actual.rule stage) =ᵐ[μ]
      (fun sample => ∑' r : OverlayWritingRecord, (cell r).indicator (P.stageObservationBill fee hfee C accounting actual.rule stage) sample) := by
    filter_upwards [hp] with sample hs
    exact hs.trans (overlay_runRecordValue_eq_tsum P fee hfee C accounting actual.rule data.toRecordSimulatorData stage
      (fun _ => P.stageObservationBill fee hfee C accounting actual.rule stage) sample)
  have hlocal (r : OverlayWritingRecord) : P.binarySymmetric.rocPrice (P.overlayRecordTarget fee r.val) ≤
      ENNReal.ofReal (P.binarySymmetric.endpointCharge r.val.level : ℝ) + P.binarySymmetric.rocPrice (P.overlayError fee) := by
    unfold PaperProofs.Paid.Parameters.overlayRecordTarget
    rcases le_total (P.recordPosteriorError r.val) (P.overlayError fee) with hle | hge
    · rw [min_eq_left hle]
      change P.binarySymmetric.rocPrice (P.binarySymmetric.endpointError r.val.level : ℝ) ≤ _
      rw [P.binarySymmetric.rocPrice_endpoint]
      exact le_self_add
    · rw [min_eq_right hge]
      exact le_add_self
  have hnone := overlay_completedHistory_none_zero_of_sourceHistoryLaw P fee hfee C accounting νsource νactual
    source actual data.toRecordSimulatorData hm hlaw hfinite
  calc
    _ = ∑' r : OverlayWritingRecord, P.binarySymmetric.rocPrice (P.overlayRecordTarget fee r.val) * μ (cell r) := by
      apply overlay_observation_integral_eq_cell_prices μ cell hc _ hf _ hpartition
      intro r
      obtain ⟨decision, hd⟩ := r.property
      exact (hcells stage r.val decision hd Set.univ MeasurableSet.univ).2.2.2.2.2.2
    _ ≤ (∑' r : OverlayWritingRecord, ENNReal.ofReal (P.binarySymmetric.endpointCharge r.val.level : ℝ) * μ (cell r)) +
        P.binarySymmetric.rocPrice (P.overlayError fee) :=
      overlay_observation_increment_le_of_cell_prices μ cell hc hdisjoint _ _ _ hlocal
    _ = (∫⁻ sample, overlay_runRecordValue P fee hfee C accounting actual.rule data.toRecordSimulatorData stage
        (fun record _ => ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ)) sample ∂μ) +
          P.binarySymmetric.rocPrice (P.overlayError fee) := by
      rw [overlay_runRecordPrice_integral P fee hfee C accounting νactual actual.rule data.toRecordSimulatorData stage _ hc]
    _ ≤ (∫⁻ sample, overlayHistoryStagePrice P stage
        (P.shadowCompletedHistory fee hfee C accounting actual.rule data.toRecordSimulatorData sample) ∂μ) +
          P.binarySymmetric.rocPrice (P.overlayError fee) :=
      add_le_add (lintegral_mono_ae (overlay_runRecordPrice_le_shadowHistoryPrice P fee hfee C accounting νactual
        actual data.toRecordSimulatorData halign hnone stage)) le_rfl
    _ = _ := by
      rw [overlay_historyStagePrice_integral_eq_source P fee hfee C accounting νsource νactual source actual
        data.toRecordSimulatorData hm hlaw stage]

/-- The original observation increment, with all original input finiteness
and intermediate representation conditions stated explicitly. -/
theorem overlay_expectedObservationBill_le
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) [IsProbabilityMeasure νsource]
    (νactual : Measure SimSeed) [IsProbabilityMeasure νactual]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlayDraft.OverlaySimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data.toRecordSimulatorData)
    (halign : P.SourceRecordAlignment fee hfee C accounting νactual actual.rule data.toRecordSimulatorData)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data.toRecordSimulatorData)
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting νactual actual.rule data)
    (hcells : OverlayDraft.OverlayRecordCells P fee hfee C accounting νactual actual.rule data)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource ≠ ⊤) :
    expectedObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource + P.overlayObservationIncrement fee := by
  have hn : Fintype.card P.sharedInstance.Stage = P.certificate.stages := by
    change Fintype.card (Fin P.sharedInstance.stageCount) = _
    rw [Fintype.card_fin, P.stageCount_eq]
  rw [expectedObservationBill_eq_sum_stage (P.input fee hfee) C.val .uncapped accounting actual.rule
    actual.legal actual.measurable_rule νactual]
  simp_rw [← stageObservationBill_eq_runStageObservationBill P fee hfee C accounting actual.rule]
  calc
    _ ≤ ∑ stage : P.sharedInstance.Stage,
        ((∫⁻ sample, overlayHistoryStagePrice P stage
          (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)
          ∂(P.input 0 (by norm_num)).seededWorldLaw νsource) + P.binarySymmetric.rocPrice (P.overlayError fee)) := by
      apply Finset.sum_le_sum
      intro stage _
      exact overlay_stageObservation_le_sourcePotential_add P fee hfee C accounting νsource νactual source actual data
        hm halign hlaw hstage hcells hfinite stage
    _ = (∑ stage : P.sharedInstance.Stage, ∫⁻ sample, overlayHistoryStagePrice P stage
        (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)
        ∂(P.input 0 (by norm_num)).seededWorldLaw νsource) + P.overlayObservationIncrement fee := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hn, nsmul_eq_mul]
      rfl
    _ ≤ _ := add_le_add (overlay_sourceHistoryPotential_le_observation P C accounting source νsource hfinite) le_rfl

end PDROC
