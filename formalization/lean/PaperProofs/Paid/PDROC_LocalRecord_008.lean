module
public import PaperProofs.Paid.PDROC_LocalRecord_007

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u

/-- Exact ORIGINAL stage charge, transported through the actual suffix
replay. Cofinality keeps infinite costs and all failing paths. -/
theorem replayedSuffix_stageBill_eq {I : Instance} {Seed : Type u}
    (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first : I.Stage) (start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first.val start sample) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let fixed := guardedReplayRule (I := I.freshSuffix first.val) startup.availableTools
      (replayedSuffixCandidate first.val accounting rule startup)
    runStageObservationBill (input.freshSuffix first.val) (currentRelaxedContract _) .uncapped
      (zeroNormalAccounting _) fixed (I.freshHead first) (sample.1, input.restrictFreshWorld first.val sample.2) =
      runStageObservationBill input C mode accounting rule first sample := by
  let startup := publicStartup (run input C mode accounting rule sample start)
  let fixed := guardedReplayRule (I := I.freshSuffix first.val) startup.availableTools
    (replayedSuffixCandidate first.val accounting rule startup)
  let targetAt := fun k => run (input.freshSuffix first.val) (currentRelaxedContract _) .uncapped
    (zeroNormalAccounting _) fixed (sample.1, input.restrictFreshWorld first.val sample.2) k
  let clock := replaySourceClock input C mode accounting rule sample first.val start
  let g := fun n => ENNReal.ofReal (input.fees.observation first : ℝ) *
    ((run input C mode accounting rule sample n).ledger.reviews first : ℝ≥0∞)
  have hmono : Monotone g := fun a b hab =>
    mul_le_mul_right (ENat.toENNReal_mono (run_reviews_mono input C mode accounting rule hlegal sample first hab)) _
  have hstage : suffixStageOf first.val first (le_refl first.val) = I.freshHead first := by
    apply Fin.ext
    simp only [suffixStageOf, Instance.freshHead, Nat.sub_self]
  have hfee : (input.freshSuffix first.val).fees.observation (I.freshHead first) = input.fees.observation first := by
    change ((input.freshSuffix first.val).experiment (I.freshHead first)).observationFee = (input.experiment first).observationFee
    rw [StatisticalInput.freshSuffix_experiment, Instance.freshStageLift_freshHead]
  have hprefix (k : ℕ) : ENNReal.ofReal ((input.freshSuffix first.val).fees.observation (I.freshHead first) : ℝ) *
      ((targetAt k).ledger.reviews (I.freshHead first) : ℝ≥0∞) = g (clock k) := by
    have hview := (replayedSuffix_fullRun input C hearly hcurrent mode accounting rule hlegal sample first.val start hentry k).1
    have hr := hview.reviews first (le_refl first.val)
    rw [hstage] at hr
    rw [hfee, hr]
  change (⨆ k, ENNReal.ofReal ((input.freshSuffix first.val).fees.observation (I.freshHead first) : ℝ) *
    ((targetAt k).ledger.reviews (I.freshHead first) : ℝ≥0∞)) = ⨆ n, g n
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [hprefix]
    exact le_iSup g (clock k)
  · apply iSup_le
    intro n
    have hcofinal : g n ≤ g (clock n) := by
      rcases replaySourceClock_grows_or_halted input C mode accounting rule sample first.val start n with hbound | hhalt
      · exact hmono ((Nat.le_add_left n start).trans hbound)
      · by_cases hle : n ≤ clock n
        · exact hmono hle
        · obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hle)
          change n = clock n + extra at he
          unfold g
          conv_lhs => rw [he, run_after_halt input C mode accounting rule sample (clock n) hhalt extra]
    have hsup := le_iSup (fun k => ENNReal.ofReal ((input.freshSuffix first.val).fees.observation (I.freshHead first) : ℝ) *
      ((targetAt k).ledger.reviews (I.freshHead first) : ℝ≥0∞)) n
    exact hcofinal.trans ((hprefix n).symm.le.trans hsup)

private theorem observationCharge_transport_eq {E F : PaperProofs.Statistics.BinaryExperiment}
    {Seed : Type u} [MeasurableSpace Seed] (h : E = F) (test : E.AdmissibleRule Seed)
    (seed : Seed) (tape : E.Tape) :
    F.observationCharge ((h ▸ test).rule.stop seed (h ▸ tape)) = E.observationCharge (test.rule.stop seed tape) := by
  cases h
  rfl

section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The real first-entry local source test buys exactly the ORIGINAL stage's
entire observation bill, not its whole future bill. Thus sums over stages
count each actual review exactly once, including abandonment and infinity. -/
theorem sourceEntryTest_observationCharge_eq_stageBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hfee).World) (first : P.sharedInstance.Stage) (start : ℕ)
    (hentry : FirstEntryAt (P.input fee hfee) C.val mode accounting source.rule first.val start sample) :
    P.binarySymmetric.experiment.observationCharge
      ((sourceEntryTest P fee hfee first accounting source.rule source.measurable_rule).rule.stop
        (sample.1, publicStartup (run (P.input fee hfee) C.val mode accounting source.rule sample start))
        (sourceEntryTape P fee hfee first ((P.input fee hfee).restrictFreshWorld first.val sample.2))) =
      runStageObservationBill (P.input fee hfee) C.val mode accounting source.rule first sample := by
  let startup := publicStartup (run (P.input fee hfee) C.val mode accounting source.rule sample start)
  let fresh := (P.input fee hfee).restrictFreshWorld first.val sample.2
  let input := (P.input fee hfee).freshSuffix first.val
  let head := P.sharedInstance.freshHead first
  let rule := sourceEntryReplayRule P first accounting source.rule
  let rawTest := nativeHeadTest input head rule
    (measurable_sourceEntryReplayRule P first accounting source.rule source.measurable_rule)
  have htransport := observationCharge_transport_eq (sourceEntryExperiment_eq P fee hfee first) rawTest
    (sample.1, startup) (worldTapes input fresh head)
  change P.binarySymmetric.experiment.observationCharge
    ((sourceEntryTest P fee hfee first accounting source.rule source.measurable_rule).rule.stop
      (sample.1, startup) (sourceEntryTape P fee hfee first fresh)) = _ at htransport
  rw [htransport]
  let fixed := guardedReplayRule (I := P.sharedInstance.freshSuffix first.val) startup.availableTools
    (replayedSuffixCandidate first.val accounting source.rule startup)
  change (input.experiment head).observationCharge (headExitStop input head fixed sample.1 (worldTapes input fresh head)) = _
  rw [nativeHead_observationCharge_eq_stageBill input (currentRelaxedContract _) (zeroNormalAccounting _)
    fixed (guardedReplayRule_legal input (currentRelaxedContract _) rfl rfl (zeroNormalAccounting _)
      startup.availableTools _) head rfl (sample.1, fresh)]
  exact replayedSuffix_stageBill_eq (P.input fee hfee) C.val C.property.1.1 C.property.1.2
    mode accounting source.rule source.legal sample first start hentry

end
end PDROC


