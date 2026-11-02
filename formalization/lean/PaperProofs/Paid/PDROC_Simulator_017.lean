module

public import PaperProofs.Paid.PDROC_Simulator_016
public import PaperProofs.Common.HistorySuffixRun

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Pointwise realization of every original D06 record, on the event where
all concrete integer endpoint tests return. That event is independently
almost sure by D04 and does not restrict the source policy. -/
theorem simulator_boundaryStage_pointwise (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    ∀ stage entry,
      entryHistory (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) stage (seed, world) = some entry →
      let record := (simulatorData P fee hfee source).record seed stage entry
      match record.decision with
      | none => P.actualOrdinaryDecision fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage = none ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage = 0
      | some decision =>
          let test := P.binarySymmetric.rocEndpointTest record.level
          let tape := worldTapes (P.input fee hfee) world stage
          ∃ n : ℕ, test.rule.stop (seed.2.2 stage) tape = (n : ℕ∞) ∧
            P.paidRunReviewCount fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage = (n : ℕ∞) ∧
            P.actualOrdinaryDecision fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage =
              some (Bool.xor decision (Bool.xor record.orientation (test.rule.decision (seed.2.2 stage) tape))) := by
  intro stage entry he
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  have hl := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨start, hc, hbefore, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage (seed, world) entry).mp he
  let s := run input C.val .uncapped accounting actual (seed, world) start
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start (seed, world) := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl (seed, world) stage.val start he'
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨k, _hk, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) start
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual seed _ _ hp stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  let record := (simulatorData P fee hfee source).record seed stage entry
  have hrecord : record = simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed s.history)) := by
    change simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed entry)) = _
    rw [hh]
  change match record.decision with | none => _ | some decision => _
  cases hd : record.decision with
  | none =>
    have hn : (simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
        (simulatorShadow P fee hfee source seed s.history))).decision = none := hrecord ▸ hd
    exact simulator_none_record_observables P fee hfee C accounting source seed world start s stage rfl ha hc hw hr hn
  | some decision =>
    cases hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) with
    | none =>
      have hnone : record.decision = none := by
        rw [hrecord, hdraw]
        rfl
      rw [hnone] at hd
      cases hd
    | some draw =>
      have hrec : record = draw.record := by
        rw [hrecord, hdraw]
        rfl
      have hd' : draw.record.decision = some decision := hrec ▸ hd
      obtain ⟨n, hn⟩ := hfinite stage draw.record.level (seed.2.2 stage)
      have hobs := simulator_writing_record_observables_at_stop P fee hfee C accounting source seed world start s stage draw decision
        rfl ha hc hw hr ho hdraw hd' n hn
      change ∃ n : ℕ, (P.binarySymmetric.rocEndpointTest record.level).rule.stop (seed.2.2 stage)
          (worldTapes input world stage) = (n : ℕ∞) ∧
        P.paidRunReviewCount fee hfee C .uncapped accounting actual (seed, world) stage = (n : ℕ∞) ∧
        P.actualOrdinaryDecision fee hfee C .uncapped accounting actual (seed, world) stage =
          some (Bool.xor decision (Bool.xor record.orientation
            ((P.binarySymmetric.rocEndpointTest record.level).rule.decision (seed.2.2 stage)
              (worldTapes input world stage))))
      rw [hrec]
      exact ⟨n, hn, hobs.2, hobs.1⟩

end PDROC
