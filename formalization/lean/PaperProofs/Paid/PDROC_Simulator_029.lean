module

public import PaperProofs.Paid.PDROC_Simulator_028

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem simulator_entry_record_report_completed (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (history : List (VisibleEvent P.sharedInstance))
    (hh : completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (seed, world) = some history)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage (seed, world) = some entry)
    (record : AuxiliaryRecord)
    (hselected : (simulatorData P fee hfee source).record seed stage entry = record)
    (decision : Bool) (hd : record.decision = some decision) :
    (historyReport (simulatorShadow P fee hfee source seed history) stage).map Prod.fst =
      some (recordVirtualTruth P record ((P.input fee hfee).truthAt world stage)
        (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  have hl := simulatorRule_legal P fee hfee C accounting source
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
  have hrecord : record = simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed s.history)) := by
    rw [← hselected]
    change simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed entry)) = _
    rw [hentry]
  cases hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) with
  | none =>
    have hn : record.decision = none := by rw [hrecord, hdraw]; rfl
    rw [hn] at hd
    cases hd
  | some draw =>
    have hrec : record = draw.record := by rw [hrecord, hdraw]; rfl
    have hd' : draw.record.decision = some decision := hrec ▸ hd
    obtain ⟨n, hn⟩ := hfinite stage draw.record.level (seed.2.2 stage)
    have hv := simulator_writing_record_report_completed P fee hfee C accounting source seed world history hh
      start s stage draw decision rfl ha hc hw hr ho hdraw hd' n hn
    simpa only [hrec] using hv

/-- This identifies the original virtual-posterior cell event with the
actual fresh endpoint/truth event. The sole path conditions are real entry,
the selected writing record, finite endpoints, and genuine completion. -/
theorem simulator_virtualPosterior_event_iff (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (hreturns : ∃ history, completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (seed, world) = some history)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage (seed, world) = some entry)
    (record : AuxiliaryRecord)
    (hselected : (simulatorData P fee hfee source).record seed stage entry = record)
    (decision : Bool) (hd : record.decision = some decision) :
    (∃ history,
      P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source)
        (simulatorData P fee hfee source) (seed, world) = some history ∧
      (historyReport history stage).map Prod.fst = some (!record.orientation)) ↔
    recordVirtualTruth P record ((P.input fee hfee).truthAt world stage)
      (seed.2.2 stage, worldTapes (P.input fee hfee) world stage) ≠ record.orientation := by
  obtain ⟨history, hh⟩ := hreturns
  have hreport := simulator_entry_record_report_completed P fee hfee C accounting source seed world hfinite
    history hh stage entry he record hselected decision hd
  have hshadow : P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source) (seed, world) = some (simulatorShadow P fee hfee source seed history) := by
    simp only [PaperProofs.Paid.Parameters.shadowCompletedHistory, hh, Option.map_some, simulatorData]
  rw [hshadow]
  simp only [Option.some.injEq, exists_eq_left', hreport]
  cases recordVirtualTruth P record ((P.input fee hfee).truthAt world stage)
    (seed.2.2 stage, worldTapes (P.input fee hfee) world stage) <;> cases record.orientation <;> decide

end PDROC
