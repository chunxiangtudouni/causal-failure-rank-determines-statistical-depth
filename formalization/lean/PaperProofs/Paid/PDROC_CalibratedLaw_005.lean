module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory
open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

instance instMeasurableSpaceOutcome : MeasurableSpace Outcome := ⊤

instance instMeasurableSingletonClassOutcome : MeasurableSingletonClass Outcome :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Measurability of the two analysis projections used in the complete
outcome law and observation expectation. No performance is a field. -/
def MeasurablePathRecord {A : Type*} [MeasurableSpace A] (f : A → PathRecord) : Prop :=
  Measurable (fun a => (f a).observation) ∧ Measurable (fun a => (f a).outcome)

namespace MeasurablePathRecord

theorem const {A : Type*} [MeasurableSpace A] (record : PathRecord) :
    MeasurablePathRecord (fun _ : A => record) := ⟨measurable_const, measurable_const⟩

theorem comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : B → PathRecord} (hf : MeasurablePathRecord f) {g : A → B} (hg : Measurable g) :
    MeasurablePathRecord (fun a => f (g a)) := ⟨hf.1.comp hg, hf.2.comp hg⟩

theorem ite {A : Type*} [MeasurableSpace A] {p : A → Prop} [DecidablePred p]
    (hp : MeasurableSet {a | p a}) {f g : A → PathRecord}
    (hf : MeasurablePathRecord f) (hg : MeasurablePathRecord g) :
    MeasurablePathRecord (fun a => if p a then f a else g a) := by
  refine ⟨?_, ?_⟩
  · simpa only [apply_ite] using Measurable.ite hp hf.1 hg.1
  · simpa only [apply_ite] using Measurable.ite hp hf.2 hg.2

theorem addObservation {A : Type*} [MeasurableSpace A] {f : A → PathRecord}
    (hf : MeasurablePathRecord f) {charge : A → ENNReal} (hc : Measurable charge) :
    MeasurablePathRecord (fun a => { f a with observation := charge a + (f a).observation }) :=
  ⟨hc.add hf.1, hf.2⟩

theorem prependTrace {A : Type*} [MeasurableSpace A] {f : A → PathRecord}
    (hf : MeasurablePathRecord f) (event : Bool × Bool) :
    MeasurablePathRecord (fun a => { f a with trace := event :: (f a).trace }) := by
  refine ⟨hf.1, ?_⟩
  exact (measurable_of_countable (fun outcome : Outcome => (event :: outcome.1, outcome.2))).comp hf.2

end MeasurablePathRecord

theorem measurable_pathSummary (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) :
    ∀ n k, MeasurablePathRecord (fun sample : (Fin n → S) × PDMenu.MenuAnalysisWorld P n =>
      pathSummary P tests table n k sample.1 sample.2) := by
  classical
  intro n
  induction n with
  | zero =>
    intro k
    exact MeasurablePathRecord.const finishRecord
  | succ n ih =>
    intro k
    have htail : Measurable (fun sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) =>
        (Fin.tail sample.1, Fin.tail sample.2)) :=
      (measurable_pi_iff.mpr (fun i => (measurable_pi_apply i.succ).comp measurable_fst)).prodMk
        (measurable_pi_iff.mpr (fun i => (measurable_pi_apply i.succ).comp measurable_snd))
    have hchild (j : ℕ) : MeasurablePathRecord
        (fun sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) =>
          pathSummary P tests table n j (Fin.tail sample.1) (Fin.tail sample.2)) := (ih j).comp htail
    cases ha : (menuEntryAt table (n + 1) k).action with
    | finish =>
      simpa only [pathSummary, ha] using
        (MeasurablePathRecord.const (A := (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1)) abandonRecord)
    | abandon =>
      simpa only [pathSummary, ha] using
        (MeasurablePathRecord.const (A := (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1)) abandonRecord)
    | test level bad =>
      cases ht : tests level with
      | none =>
        simpa only [pathSummary, ha, ht] using
          (MeasurablePathRecord.const (A := (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1)) abandonRecord)
      | some test =>
        have hhead : Measurable (fun sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) =>
            (sample.1 0, (sample.2 0).2)) :=
          ((measurable_pi_apply 0).comp measurable_fst).prodMk (((measurable_pi_apply 0).comp measurable_snd).snd)
        have hstop : Measurable (fun sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) =>
            test.rule.stop (sample.1 0) (sample.2 0).2) := test.measurable_stop.comp hhead
        have hcharge : Measurable (fun sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) =>
            P.experiment.observationCharge (test.rule.stop (sample.1 0) (sample.2 0).2)) :=
          (measurable_of_countable P.experiment.observationCharge).comp hstop
        have hcorrect : MeasurableSet {sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) |
            test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1} :=
          measurableSet_eq_fun (test.measurable_decision.comp hhead) (((measurable_pi_apply 0).comp measurable_snd).fst)
        have hstopset : MeasurableSet {sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) |
            test.rule.stop (sample.1 0) (sample.2 0).2 = ⊤} := (measurableSet_singleton ⊤).preimage hstop
        let continuation := fun sample : (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1) =>
          if test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1 then
            let child := pathSummary P tests table n k (Fin.tail sample.1) (Fin.tail sample.2)
            { child with trace := (false, false) :: child.trace }
          else match bad with
            | .abandon => { abandonRecord with trace := [(true, false)] }
            | .repair => if k = 0 then { abandonRecord with trace := [(true, false)] } else
                let child := pathSummary P tests table n (k - 1) (Fin.tail sample.1) (Fin.tail sample.2)
                { child with trace := (true, true) :: child.trace }
        have hcontinuation : MeasurablePathRecord continuation := by
          dsimp only [continuation]
          apply MeasurablePathRecord.ite hcorrect ((hchild k).prependTrace (false, false))
          cases bad with
          | abandon => exact MeasurablePathRecord.const _
          | repair =>
            by_cases hk : k = 0
            · simp only [hk, ite_true]
              exact MeasurablePathRecord.const _
            · simp only [ite_eq_right hk]
              exact (hchild (k - 1)).prependTrace (true, true)
        have hwhole := MeasurablePathRecord.ite hstopset
          (MeasurablePathRecord.const (A := (Fin (n + 1) → S) × PDMenu.MenuAnalysisWorld P (n + 1)) nonreturnRecord)
          (hcontinuation.addObservation hcharge)
        cases bad <;> simpa only [pathSummary, ha, ht, continuation] using hwhole

theorem measurable_pathObservation (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) (n k : ℕ) :
    Measurable (fun sample : (Fin n → S) × PDMenu.MenuAnalysisWorld P n =>
      (pathSummary P tests table n k sample.1 sample.2).observation) :=
  (measurable_pathSummary P tests table n k).1

theorem measurable_pathOutcome (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) (n k : ℕ) :
    Measurable (fun sample : (Fin n → S) × PDMenu.MenuAnalysisWorld P n =>
      (pathSummary P tests table n k sample.1 sample.2).outcome) :=
  (measurable_pathSummary P tests table n k).2

end PDROC.CalibratedLaw
