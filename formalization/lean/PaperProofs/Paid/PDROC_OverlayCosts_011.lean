module

public import PaperProofs.Paid.PDROC_OverlayCosts_010
public import PaperProofs.Common.NativeBellmanSuccessLift

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

def overlayResolvedCompleted (P : Parameters) : EntryHistory P.sharedInstance → Prop
  | none => False
  | some history => .stopped ∈ history ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance history stage = true

/-- Genuine successful source completions have an ordinary stop and fully
resolved stage histories, with serials supplied by actual Native prefixes. -/
theorem overlay_success_completedHistory_resolved
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hfee).World) (history : List (VisibleEvent P.sharedInstance))
    (hh : completedHistory (P.input fee hfee) C.val mode accounting policy.rule sample = some history)
    (hs : runSuccess (P.input fee hfee) C.val mode accounting policy.rule sample) :
    .stopped ∈ history ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance history stage = true := by
  obtain ⟨n, hhalt, _, hhistory⟩ := (completedHistory_some_iff (P.input fee hfee) C.val mode accounting policy.rule sample history).mp hh
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val mode accounting policy.rule policy.legal sample n
  have hsuccess := (runSuccess_iff_halted_success (P.input fee hfee) C.val mode accounting policy.rule sample n hhalt).mp hs
  have hwf := prefix_ledgerWellFormed (P.input fee hfee) C.val mode accounting policy.rule sample.1 _ _ hp
  constructor
  · have hlast := prefix_halted_not_abandoned_last_stopped (P.input fee hfee) C.val mode accounting policy.rule
      sample.1 _ _ hp hhalt hsuccess.2.1
    have hm : VisibleEvent.stopped ∈ (run (P.input fee hfee) C.val mode accounting policy.rule sample n).history :=
      List.mem_of_mem_getLast? (by rw [hlast]; rfl)
    rwa [hhistory] at hm
  · intro stage
    have hcorrect := hsuccess.2.2.2 stage
    have hwritten : (run (P.input fee hfee) C.val mode accounting policy.rule sample n).ledger.written stage ≠ none := by
      rcases hcorrect with hc | ⟨execution, he, hstage⟩
      · rw [hc]; simp
      · have hg := hwf.genuine execution he
        rw [hstage] at hg
        rw [hg.1]; simp
    obtain ⟨bit, hbit⟩ := Option.ne_none_iff_exists.mp hwritten
    have hbit' := hbit.symm
    obtain ⟨time, htime⟩ := prefix_early_written_reported (P.input fee hfee) C.val C.property.1.1 mode accounting
      policy.rule sample.1 _ _ hp stage hwritten
    have hw := prefix_historyWrite (P.input fee hfee) C.val mode accounting policy.rule sample.1 _ _ hp stage
    have hr := prefix_historyReport_early (P.input fee hfee) C.val C.property.1.1 mode accounting policy.rule sample.1 _ _ hp stage
    have hx := prefix_historyExecutions (P.input fee hfee) C.val mode accounting policy.rule sample.1 _ _ hp
    rw [hhistory] at hw hr hx
    rw [hbit'] at hw
    rw [htime] at hr
    simp only [PaperProofs.Paid.Parameters.historyStageResolved, hw, hr, Option.map_some,
      beq_self_eq_true, Bool.true_and]
    rcases hcorrect with hc | ⟨execution, he, hstage⟩
    · have heq : bit = (run (P.input fee hfee) C.val mode accounting policy.rule sample n).ledger.truth stage :=
        Option.some.inj (hbit'.symm.trans hc)
      simp [heq]
    · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      right
      rw [hx, List.any_map, List.any_eq_true]
      refine ⟨execution, he, ?_⟩
      have hg := hwf.genuine execution he
      simp only [Function.comp_apply, hstage, beq_self_eq_true, Bool.true_and]
      exact beq_iff_eq.mpr (by simpa only [hstage] using hg.2)

/-- Complete source-history law transports this countable history-support
fact without an RCP or a semantic range assumption on the private seed. -/
theorem overlay_shadowMarkedSuccess_resolved
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw νactual,
      MarkedCompletedSuccess ((P.shadowCompletedHistory fee hfee C accounting actual.rule data sample).map markedHistory) →
        overlayResolvedCompleted P (P.shadowCompletedHistory fee hfee C accounting actual.rule data sample) := by
  have hma : Measurable (fun sample : SimSeed × (P.input fee hfee).World =>
      (data.sourceSeed sample.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)) :=
    (hm.1.comp measurable_fst).prodMk hlaw.1
  have hms : Measurable (fun sample : SourceSeed × (P.input 0 (by norm_num)).World =>
      (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)) :=
    measurable_fst.prodMk (measurable_completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting
      source.rule source.measurable_rule)
  let good := fun history : EntryHistory P.sharedInstance =>
    MarkedCompletedSuccess (history.map markedHistory) → overlayResolvedCompleted P history
  have hgood : MeasurableSet {pair : SourceSeed × EntryHistory P.sharedInstance | good pair.2} :=
    ((Set.to_countable {history | good history}).measurableSet).preimage measurable_snd
  have hsource : ∀ sample : SourceSeed × (P.input 0 (by norm_num)).World,
      good (completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample) := by
    intro sample hs
    have hsuccess := (runSuccess_iff_markedCompleted (P.input 0 (by norm_num)) C.val C.property.1.1
      .uncapped accounting source.rule source.legal sample).mpr hs
    cases hh : completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample with
    | none => simp only [hh, Option.map_none, MarkedCompletedSuccess] at hs
    | some history =>
      exact overlay_success_completedHistory_resolved P 0 (by norm_num) C .uncapped accounting source sample history hh hsuccess
  have hs : ∀ᵐ pair ∂(((P.input 0 (by norm_num)).seededWorldLaw νsource).map
      (fun sample => (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample))), good pair.2 :=
    (ae_map_iff hms.aemeasurable hgood).mpr (ae_of_all _ hsource)
  rw [← hlaw.2.2] at hs
  exact (ae_map_iff hma.aemeasurable hgood).mp hs

/-- Original D14 prefix success domination and full source law imply the
required risk comparison. Every intermediate hypothesis is a representation
field; no new risk or finite-ET premise remains. -/
theorem overlay_risk_le_of_prefix_success_domination
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data)
    (hdom : ∀ sample n,
      let virtual := data.shadow sample.1 (run (P.input fee hfee) C.val .uncapped accounting actual.rule sample n).history
      (.stopped ∈ virtual ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance virtual stage = true) →
        runSuccess (P.input fee hfee) C.val .uncapped accounting actual.rule sample) :
    risk (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      risk (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource := by
  apply overlay_risk_le_of_sourceHistoryLaw P fee hfee C accounting νsource νactual source actual data hm hlaw
  filter_upwards [overlay_shadowMarkedSuccess_resolved P fee hfee C accounting νsource νactual source actual data hm hlaw] with sample hs hmarked
  have hresolved := hs hmarked
  cases hh : completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample with
  | none =>
    simp only [PaperProofs.Paid.Parameters.shadowCompletedHistory, hh, Option.map_none, MarkedCompletedSuccess] at hmarked
  | some history =>
    obtain ⟨n, _, _, hhistory⟩ := (completedHistory_some_iff (P.input fee hfee) C.val .uncapped accounting actual.rule sample history).mp hh
    apply hdom sample n
    rw [hhistory]
    simpa only [PaperProofs.Paid.Parameters.shadowCompletedHistory, hh, Option.map_some, overlayResolvedCompleted] using hresolved

end PDROC

