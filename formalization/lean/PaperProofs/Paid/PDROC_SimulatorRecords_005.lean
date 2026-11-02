module

public import PaperProofs.Paid.PDROC_SimulatorRecords_004
public import PaperProofs.Paid.PDROC_EndpointFinite_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
/-- The concrete source word and decision align with the entire final shadow,
including the immediate nonwriting termination branch. -/
theorem simulator_sourceRecordAlignment_pointwise (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    ∀ history, completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (seed, world) = some history →
      ∀ stage entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) stage (seed, world) = some entry →
        historyCursor ((simulatorData P fee hfee source).shadow seed entry) = stage.val ∧
        historyObservations ((simulatorData P fee hfee source).shadow seed entry) stage = [] ∧
        historyWrite ((simulatorData P fee hfee source).shadow seed entry) stage = none ∧
        ((simulatorData P fee hfee source).record seed stage entry).observations.map Fin.val =
          historyObservations ((simulatorData P fee hfee source).shadow seed history) stage ∧
        ((simulatorData P fee hfee source).record seed stage entry).decision =
          historyWritten ((simulatorData P fee hfee source).shadow seed history) stage := by
  intro history hh stage entry he
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  have hl := simulatorRule_legal P fee hfee C accounting source
  have hf := simulator_entry_shadow_fresh P fee hfee C accounting source (seed, world) stage entry he
  obtain ⟨start, hc, hbefore, hentry⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage (seed, world) entry).mp he
  let s := run input C.val .uncapped accounting actual (seed, world) start
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start (seed, world) := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl (seed, world) stage.val start he'
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) start
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual seed _ _ hp stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  have hvo : historyObservations (simulatorShadow P fee hfee source seed s.history) stage = [] := by
    change historyObservations (simulatorShadow P fee hfee source seed
      (run input C.val .uncapped accounting actual (seed, world) start).history) stage = []
    rw [hentry]
    exact hf.2.1
  let record := (simulatorData P fee hfee source).record seed stage entry
  have hrecord : record = simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed s.history)) := by
    change simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed entry)) = _
    rw [hentry]
  have hview : simulatorPortView (simulatorShadow P fee hfee source seed history) stage =
      (record.observations.map Fin.val, record.decision) := by
    cases hd : record.decision with
    | none =>
      have hn : (simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
          (simulatorShadow P fee hfee source seed s.history))).decision = none := hrecord ▸ hd
      have hv := simulator_none_record_shadow_completed P fee hfee C accounting source seed world history hh
        start s stage rfl ha hc hw hn
      rw [← hrecord] at hv
      simpa only [hd] using hv
    | some decision =>
      cases hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) with
      | none =>
        have hn : record.decision = none := by rw [hrecord, hdraw]; rfl
        rw [hn] at hd
        cases hd
      | some draw =>
        have hrec : record = draw.record := by rw [hrecord, hdraw]; rfl
        have hd' : draw.record.decision = some decision := hrec ▸ hd
        obtain ⟨n, hn⟩ := hfinite stage draw.record.level (seed.2.2 stage)
        have hv := simulator_writing_record_shadow_completed P fee hfee C accounting source seed world history hh
          start s stage draw decision rfl ha hc hw hr ho hvo hdraw hd' n hn
        simpa only [hrec, hd'] using hv
  exact ⟨hf.1, hf.2.1, hf.2.2, (congrArg Prod.fst hview).symm, (congrArg Prod.snd hview).symm⟩

/-- The original D06 SourceRecordAlignment is closed for the actual simulator,
with no source-history-law or finite-source-charge premise. -/
theorem simulatorSourceRecordAlignment (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure (SimulatorSeed P Seed)) [IsProbabilityMeasure ν] :
    P.SourceRecordAlignment fee hfee C accounting ν (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source) := by
  filter_upwards [allEndpoints_finite_seededWorld P fee hfee ν] with sample hs
  exact simulator_sourceRecordAlignment_pointwise P fee hfee C accounting source sample.1 sample.2 hs

end PDROC


