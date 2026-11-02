module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_001
public import PaperProofs.Paid.PDMenu_MenuSuffixSample_110

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open scoped ENNReal

namespace PDROC.CalibratedRuntime

theorem pathSummary_test_correct (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level reviews : ℕ) (bad : MenuBadAction) (test : P.experiment.AdmissibleRule S)
    (seed : Fin (n + 1) → S) (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (ha : (menuEntryAt table (n + 1) k).action = .test level bad)
    (ht : tests level = some test) (hs : test.rule.stop (seed 0) (world 0).2 = reviews)
    (hc : test.rule.decision (seed 0) (world 0).2 = (world 0).1) :
    pathSummary P tests table (n + 1) k seed world =
      let child := pathSummary P tests table n k (Fin.tail seed) (Fin.tail world)
      { observation := P.experiment.observationCharge reviews + child.observation,
        trace := (false, false) :: child.trace, failure := child.failure } := by
  simp only [pathSummary, ha, ht, hs, ENat.natCast_ne_top, ite_false, ite_eq_left hc]

theorem pathSummary_test_abandon (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level reviews : ℕ) (test : P.experiment.AdmissibleRule S)
    (seed : Fin (n + 1) → S) (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (ha : (menuEntryAt table (n + 1) k).action = .test level .abandon)
    (ht : tests level = some test) (hs : test.rule.stop (seed 0) (world 0).2 = reviews)
    (hw : test.rule.decision (seed 0) (world 0).2 ≠ (world 0).1) :
    pathSummary P tests table (n + 1) k seed world =
      { observation := P.experiment.observationCharge reviews, trace := [(true, false)], failure := true } := by
  simp only [pathSummary, ha, ht, hs, ENat.natCast_ne_top, ite_false, ite_eq_right hw,
    abandonRecord, add_zero]

theorem pathSummary_test_no_tool (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n level reviews : ℕ) (test : P.experiment.AdmissibleRule S)
    (seed : Fin (n + 1) → S) (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (ha : (menuEntryAt table (n + 1) 0).action = .test level .repair)
    (ht : tests level = some test) (hs : test.rule.stop (seed 0) (world 0).2 = reviews)
    (hw : test.rule.decision (seed 0) (world 0).2 ≠ (world 0).1) :
    pathSummary P tests table (n + 1) 0 seed world =
      { observation := P.experiment.observationCharge reviews, trace := [(true, false)], failure := true } := by
  simp only [pathSummary, ha, ht, hs, ENat.natCast_ne_top, ite_false, ite_eq_right hw,
    ite_true, abandonRecord, add_zero]

theorem pathSummary_test_repair (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level reviews : ℕ) (test : P.experiment.AdmissibleRule S)
    (seed : Fin (n + 1) → S) (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (ha : (menuEntryAt table (n + 1) k).action = .test level .repair)
    (ht : tests level = some test) (hs : test.rule.stop (seed 0) (world 0).2 = reviews)
    (hw : test.rule.decision (seed 0) (world 0).2 ≠ (world 0).1) (hk : k ≠ 0) :
    pathSummary P tests table (n + 1) k seed world =
      let child := pathSummary P tests table n (k - 1) (Fin.tail seed) (Fin.tail world)
      { observation := P.experiment.observationCharge reviews + child.observation,
        trace := (true, true) :: child.trace, failure := child.failure } := by
  simp only [pathSummary, ha, ht, hs, ENat.natCast_ne_top, ite_false, ite_eq_right hw, ite_eq_right hk]

theorem pathSummary_invalid (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level : ℕ) (bad : MenuBadAction) (seed : Fin (n + 1) → S)
    (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (ha : (menuEntryAt table (n + 1) k).action = .test level bad) (ht : tests level = none) :
    pathSummary P tests table (n + 1) k seed world = abandonRecord := by
  simp only [pathSummary, ha, ht]

theorem pathSummary_abandon (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k : ℕ) (seed : Fin (n + 1) → S) (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (ha : (menuEntryAt table (n + 1) k).action = .abandon ∨
      (menuEntryAt table (n + 1) k).action = .finish) :
    pathSummary P tests table (n + 1) k seed world = abandonRecord := by
  rcases ha with ha | ha <;> simp only [pathSummary, ha]

/-- Crop the unchanged fair bits and complete potential mark rows. This
contains no sampling or law assertion and does not redraw any mark. -/
def calibratedSuffixSeed (P : Parameters) (cursor n : ℕ)
    (hfit : cursor + n = P.certificate.stages) (seed : P.CalibratedMenuSeed) : Fin n → StageSeed P :=
  fun i =>
    let stage := PDMenu.menuSuffixStage P.certificate.stages P.tools cursor n hfit i
    (seed.1 stage, seed.2 stage)

theorem calibratedSuffixSeed_head (P : Parameters) (cursor n : ℕ)
    (hfit : cursor + (n + 1) = P.certificate.stages) (seed : P.CalibratedMenuSeed)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor) :
    calibratedSuffixSeed P cursor (n + 1) hfit seed 0 = (seed.1 stage, seed.2 stage) :=
  congrArg (fun stage => (seed.1 stage, seed.2 stage))
    (PDMenu.menuSuffixStage_zero P.certificate.stages P.tools cursor n hfit stage hstage)

theorem calibratedSuffixSeed_tail (P : Parameters) (cursor n : ℕ)
    (hfit : cursor + (n + 1) = P.certificate.stages) (hnext : cursor + 1 + n = P.certificate.stages)
    (seed : P.CalibratedMenuSeed) :
    Fin.tail (calibratedSuffixSeed P cursor (n + 1) hfit seed) =
      calibratedSuffixSeed P (cursor + 1) n hnext seed := by
  funext i
  exact congrArg (fun stage => (seed.1 stage, seed.2 stage))
    (PDMenu.menuSuffixStage_succ P.certificate.stages P.tools cursor n hfit hnext i)

theorem calibratedSuffixSeed_root (P : Parameters) (seed : P.CalibratedMenuSeed) :
    calibratedSuffixSeed P 0 P.certificate.stages (Nat.zero_add P.certificate.stages) seed =
      fun i => (seed.1 (PDMenu.menuStageAt P.certificate.stages P.tools i),
        seed.2 (PDMenu.menuStageAt P.certificate.stages P.tools i)) := by
  funext i
  exact congrArg (fun stage => (seed.1 stage, seed.2 stage))
    (Fin.ext (Nat.zero_add i.val))

end PDROC.CalibratedRuntime
