module

public import PaperProofs.Paid.PDMenu_CalibratedBasics_010
public import PaperProofs.Paid.PDMenu_MenuAnalysisLaw_088

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.CalibratedRuntime

/-- One unchanged physical stage's fair bit and complete row of potential
calibration marks. No selector is redrawn when a level is selected. -/
abbrev StageSeed (P : Parameters) := Bool × (Fin (P.certificate.M + 1) → Bool)

/-- One entry per actually written stage. The pair records wrong-write and
physical-repair flags; absent list entries mean that the stage was unwritten. -/
abbrev Trace := List (Bool × Bool)

abbrev Outcome := Trace × Bool

structure PathRecord where
  observation : ℝ≥0∞
  trace : Trace
  failure : Bool

def PathRecord.outcome (record : PathRecord) : Outcome := (record.trace, record.failure)

def finishRecord : PathRecord := ⟨0, [], false⟩
def abandonRecord : PathRecord := ⟨0, [], true⟩
def nonreturnRecord : PathRecord := ⟨⊤, [], true⟩

/-- The original local two-coin seed, selected from the original full mark
row. The totalized out-of-range value is never tested by calibratedFamily. -/
def localCalibrationSeed (P : Parameters) (level : ℕ) (seed : StageSeed P) : Bool × Bool :=
  (if h : level ≤ P.certificate.M then seed.2 ⟨level, by omega⟩ else false, seed.1)

theorem localCalibrationSeed_of_valid (P : Parameters) (level : ℕ)
    (seed : StageSeed P) (h : level ≤ P.certificate.M) :
    localCalibrationSeed P level seed = (seed.2 ⟨level, by omega⟩, seed.1) := by
  simp only [localCalibrationSeed, h, ↓reduceDIte]

/-- Only a seed-coordinate pullback of the original calibratedTest. -/
noncomputable def calibratedStageTest (P : Parameters) (level : ℕ) :
    P.experiment.AdmissibleRule (StageSeed P) := by
  let test : P.experiment.AdmissibleRule (Bool × Bool) := P.calibratedTest level
  let pull := fun sample : StageSeed P × P.experiment.Tape =>
    (localCalibrationSeed P level sample.1, sample.2)
  have hm : Measurable pull :=
    ((measurable_of_countable (localCalibrationSeed P level)).comp measurable_fst).prodMk measurable_snd
  exact {
    rule := {
      stop := fun seed tape => test.rule.stop (localCalibrationSeed P level seed) tape
      decision := fun seed tape => test.rule.decision (localCalibrationSeed P level seed) tape
      stopping := fun seed tape tape' n hp => test.rule.stopping (localCalibrationSeed P level seed) tape tape' n hp
      stoppedDecision := fun seed tape tape' n hs hs' hp =>
        test.rule.stoppedDecision (localCalibrationSeed P level seed) tape tape' n hs hs' hp }
    measurable_stop := test.measurable_stop.comp hm
    measurable_decision := test.measurable_decision.comp hm }

@[simp] theorem calibratedStageTest_stop (P : Parameters) (level : ℕ)
    (seed : StageSeed P) (tape : P.experiment.Tape) :
    (calibratedStageTest P level).rule.stop seed tape =
      (P.calibratedTest level).rule.stop (localCalibrationSeed P level seed) tape := rfl

@[simp] theorem calibratedStageTest_decision (P : Parameters) (level : ℕ)
    (seed : StageSeed P) (tape : P.experiment.Tape) :
    (calibratedStageTest P level).rule.decision seed tape =
      (P.calibratedTest level).rule.decision (localCalibrationSeed P level seed) tape := rfl

noncomputable def idealFamily (P : Parameters) (level : ℕ) : Option (P.experiment.AdmissibleRule Bool) :=
  some (PDMenu.menuAnalysisTest P level)

/-- Exactly the original level guard; malformed table levels abandon. -/
noncomputable def calibratedFamily (P : Parameters) (level : ℕ) :
    Option (P.experiment.AdmissibleRule (StageSeed P)) :=
  if level ≤ P.certificate.M then some (calibratedStageTest P level) else none

theorem calibratedFamily_some (P : Parameters) (level : ℕ) (h : level ≤ P.certificate.M) :
    calibratedFamily P level = some (calibratedStageTest P level) := ite_eq_left h

theorem calibratedFamily_none (P : Parameters) (level : ℕ) (h : ¬level ≤ P.certificate.M) :
    calibratedFamily P level = none := ite_eq_right h

/-- The one shared analysis recursion for both actual backends. Observation
duration is recorded separately from the complete discrete write/repair trace.
The original infinite nonreturn branch leaves this and later stages unwritten. -/
noncomputable def pathSummary (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) :
    (n k : ℕ) → (Fin n → S) → PDMenu.MenuAnalysisWorld P n → PathRecord
  | 0, _, _, _ => finishRecord
  | n + 1, k, seed, world => by
    classical
    exact match (menuEntryAt table (n + 1) k).action with
    | .finish | .abandon => abandonRecord
    | .test level bad => match tests level with
      | none => abandonRecord
      | some test =>
          let stopped := test.rule.stop (seed 0) (world 0).2
          if stopped = ⊤ then nonreturnRecord else
            let continuation :=
              if test.rule.decision (seed 0) (world 0).2 = (world 0).1 then
                let child := pathSummary P tests table n k (Fin.tail seed) (Fin.tail world)
                { child with trace := (false, false) :: child.trace }
              else match bad with
                | .abandon => { abandonRecord with trace := [(true, false)] }
                | .repair =>
                    if k = 0 then { abandonRecord with trace := [(true, false)] } else
                      let child := pathSummary P tests table n (k - 1) (Fin.tail seed) (Fin.tail world)
                      { child with trace := (true, true) :: child.trace }
            { continuation with observation := P.experiment.observationCharge stopped + continuation.observation }

theorem pathSummary_zero (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) (k : ℕ)
    (seed : Fin 0 → S) (world : PDMenu.MenuAnalysisWorld P 0) :
    pathSummary P tests table 0 k seed world = finishRecord := rfl

/-- Exact original first-unused-tool selection, evaluated on a pure used
set. No claim that a tool index equals a correction count is inserted. -/
def unusedTool (K : ℕ) (used : Finset (Fin K)) : Option (Fin K) :=
  (List.finRange K).find? (fun tool => tool ∉ used)

/-- Replay the chronological repair flags using the same actual finite
tool order and exclusion predicate. Stage labels remain physical Nat indices. -/
def repairPairs (K cursor : ℕ) (used : Finset (Fin K)) : Trace → List (ℕ × Fin K)
  | [] => []
  | event :: rest =>
      if event.2 then match unusedTool K used with
        | none => repairPairs K (cursor + 1) used rest
        | some tool => (cursor, tool) :: repairPairs K (cursor + 1) (insert tool used) rest
      else repairPairs K (cursor + 1) used rest

/-- The exact original discrete signature codomain, decoded from visited
write/repair flags by original physical tool selection. No visit gives false. -/
noncomputable def outcomeSignature (P : Parameters) (outcome : Outcome) : P.ExecutionSignature := by
  classical
  exact (
    (fun stage => match outcome.1[stage.val]? with | none => false | some event => !event.1),
    (fun stage => match outcome.1[stage.val]? with | none => false | some event => event.1),
    (fun stage tool => decide ((stage.val, tool) ∈ repairPairs P.tools 0 ∅ outcome.1)),
    outcome.2)

end PDROC.CalibratedRuntime
