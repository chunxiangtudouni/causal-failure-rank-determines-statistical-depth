module
public import PaperProofs.Paid.PDROC_LocalRecord_003
public import PaperProofs.Common.HistorySuffixCharge

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u v

/-- Interpreters are invariant under any change of seed representation that
preserves the chosen actions on every visible history. -/
theorem run_eq_of_seed_actions {I : Instance} {SeedA : Type u} {SeedB : Type v}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (ruleA : PolicyRule I SeedA) (ruleB : PolicyRule I SeedB)
    (seedA : SeedA) (seedB : SeedB) (world : input.World)
    (heq : ∀ history, ruleA seedA history = ruleB seedB history) (n : ℕ) :
    run input C mode accounting ruleA (seedA, world) n =
      run input C mode accounting ruleB (seedB, world) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, heq]

theorem runObservationBill_eq_of_seed_actions {I : Instance} {SeedA : Type u} {SeedB : Type v}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (ruleA : PolicyRule I SeedA) (ruleB : PolicyRule I SeedB)
    (seedA : SeedA) (seedB : SeedB) (world : input.World)
    (heq : ∀ history, ruleA seedA history = ruleB seedB history) :
    runObservationBill input C mode accounting ruleA (seedA, world) =
      runObservationBill input C mode accounting ruleB (seedB, world) := by
  unfold runObservationBill
  congr 1
  funext n
  rw [run_eq_of_seed_actions input C mode accounting ruleA ruleB seedA seedB world heq n]

theorem futureObservationBill_le_full {I : Instance} {Seed : Type u}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (start : ℕ) (sample : Seed × input.World) :
    futureObservationBill input C mode accounting rule start sample ≤
      runObservationBill input C mode accounting rule sample := by
  unfold futureObservationBill runObservationBill
  apply iSup_le
  intro k
  apply le_iSup_of_le (start + k)
  unfold observationIncrement Ledger.observationBill
  apply Finset.sum_le_sum
  intro stage _
  exact mul_le_mul_right (ENat.toENNReal_mono (tsub_le_self)) _

theorem sourceEntryExperiment_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) :
    ((P.input fee hfee).freshSuffix first.val).experiment (P.sharedInstance.freshHead first) =
      P.binarySymmetric.experiment := by
  rw [StatisticalInput.freshSuffix_experiment]
  exact P.experiment_eq_binarySymmetric

def sourceEntryTape (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (fresh : ((P.input fee hfee).freshSuffix first.val).World) :
    P.binarySymmetric.experiment.Tape :=
  sourceEntryExperiment_eq P fee hfee first ▸
    worldTapes ((P.input fee hfee).freshSuffix first.val) fresh (P.sharedInstance.freshHead first)

private theorem observationCharge_transport {E F : PaperProofs.Statistics.BinaryExperiment}
    {Seed : Type u} [MeasurableSpace Seed] (h : E = F) (test : E.AdmissibleRule Seed)
    (seed : Seed) (tape : E.Tape) :
    F.observationCharge ((h ▸ test).rule.stop seed (h ▸ tape)) =
      E.observationCharge (test.rule.stop seed tape) := by
  cases h
  rfl

section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- At every REAL first entry, the entire local source-record observation
charge is bounded by the original remaining observation bill. Old deferred
executions are replayed, and all failure paths and infinite charges remain. -/
theorem sourceEntryTest_observationCharge_le_future (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hfee).World) (first : P.sharedInstance.Stage) (start : ℕ)
    (hentry : FirstEntryAt (P.input fee hfee) C.val mode accounting source.rule first.val start sample) :
    P.binarySymmetric.experiment.observationCharge
      ((sourceEntryTest P fee hfee first accounting source.rule source.measurable_rule).rule.stop
        (sample.1, publicStartup (run (P.input fee hfee) C.val mode accounting source.rule sample start))
        (sourceEntryTape P fee hfee first ((P.input fee hfee).restrictFreshWorld first.val sample.2))) ≤
      futureObservationBill (P.input fee hfee) C.val mode accounting source.rule start sample := by
  let startup := publicStartup (run (P.input fee hfee) C.val mode accounting source.rule sample start)
  let fresh := (P.input fee hfee).restrictFreshWorld first.val sample.2
  let input := (P.input fee hfee).freshSuffix first.val
  let head := P.sharedInstance.freshHead first
  let rule := sourceEntryReplayRule P first accounting source.rule
  let rawTest := nativeHeadTest input head rule
    (measurable_sourceEntryReplayRule P first accounting source.rule source.measurable_rule)
  have htransport := observationCharge_transport (sourceEntryExperiment_eq P fee hfee first) rawTest
    (sample.1, startup) (worldTapes input fresh head)
  change P.binarySymmetric.experiment.observationCharge
    ((sourceEntryTest P fee hfee first accounting source.rule source.measurable_rule).rule.stop
      (sample.1, startup) (sourceEntryTape P fee hfee first fresh)) = _ at htransport
  rw [htransport]
  have hlocal := nativeHead_observationCharge_le input (currentRelaxedContract _) (zeroNormalAccounting _)
    rule head rfl ((sample.1, startup), fresh)
  change (input.experiment head).observationCharge (headExitStop input head rule (sample.1, startup)
    (worldTapes input fresh head)) ≤ _ at hlocal
  refine hlocal.trans ?_
  let fixed := guardedReplayRule (I := P.sharedInstance.freshSuffix first.val) startup.availableTools (replayedSuffixCandidate first.val accounting source.rule startup)
  have hrun := runObservationBill_eq_of_seed_actions input (currentRelaxedContract _) .uncapped
    (zeroNormalAccounting _) rule fixed (sample.1, startup) sample.1 fresh (fun _ => rfl)
  rw [hrun]
  exact (replayedSuffix_observationBill_eq (P.input fee hfee) C.val C.property.1.1 C.property.1.2
    mode accounting source.rule source.legal sample first.val start hentry).le

end
end PDROC


