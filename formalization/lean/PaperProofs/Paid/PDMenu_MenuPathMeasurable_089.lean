module

public import PaperProofs.Paid.PDMenu_MenuAnalysisLaw_088

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory

namespace PDMenu

open PaperProofs.Paid

/-- Measurability only; no performance or native correspondence is
assumed or stored in the analysis record. -/
def MeasurableMenuRecord {α : Type*} [MeasurableSpace α] (f : α → MenuPathRecord) : Prop :=
  Measurable (fun a => (f a).observation) ∧ Measurable (fun a => (f a).physicalRepairs) ∧
    Measurable (fun a => (f a).failure)

namespace MeasurableMenuRecord

theorem const {α : Type*} [MeasurableSpace α] (record : MenuPathRecord) :
    MeasurableMenuRecord (fun _ : α => record) := ⟨measurable_const, measurable_const, measurable_const⟩

theorem comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : β → MenuPathRecord} (hf : MeasurableMenuRecord f) {g : α → β} (hg : Measurable g) :
    MeasurableMenuRecord (fun a => f (g a)) := ⟨hf.1.comp hg, hf.2.1.comp hg, hf.2.2.comp hg⟩

theorem ite {α : Type*} [MeasurableSpace α] {p : α → Prop} [DecidablePred p]
    (hp : MeasurableSet {a | p a}) {f g : α → MenuPathRecord}
    (hf : MeasurableMenuRecord f) (hg : MeasurableMenuRecord g) :
    MeasurableMenuRecord (fun a => if p a then f a else g a) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [apply_ite] using Measurable.ite hp hf.1 hg.1
  · simpa only [apply_ite] using Measurable.ite hp hf.2.1 hg.2.1
  · simpa only [apply_ite] using Measurable.ite hp hf.2.2 hg.2.2

theorem addObservation {α : Type*} [MeasurableSpace α] {f : α → MenuPathRecord}
    (hf : MeasurableMenuRecord f) {charge : α → ENNReal} (hc : Measurable charge) :
    MeasurableMenuRecord (fun a => { f a with observation := charge a + (f a).observation }) :=
  ⟨hc.add hf.1, hf.2.1, hf.2.2⟩

theorem incrementRepairs {α : Type*} [MeasurableSpace α] {f : α → MenuPathRecord}
    (hf : MeasurableMenuRecord f) :
    MeasurableMenuRecord (fun a => { f a with physicalRepairs := (f a).physicalRepairs + 1 }) :=
  ⟨hf.1, (measurable_of_countable (fun count : ℕ => count + 1)).comp hf.2.1, hf.2.2⟩

end MeasurableMenuRecord

theorem measurable_menuPathSummary (P : Parameters) (table : MenuTable) :
    ∀ (n k : ℕ), MeasurableMenuRecord
      (fun sample : MenuAnalysisSeed n × MenuAnalysisWorld P n => menuPathSummary P table n k sample.1 sample.2) := by
  classical
  intro n
  induction n with
  | zero =>
    intro k
    exact MeasurableMenuRecord.const menuPathFinish
  | succ n ih =>
    intro k
    have htail : Measurable (fun sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) =>
        (Fin.tail sample.1, Fin.tail sample.2)) :=
      (measurable_pi_iff.mpr (fun i => (measurable_pi_apply i.succ).comp measurable_fst)).prodMk
        (measurable_pi_iff.mpr (fun i => (measurable_pi_apply i.succ).comp measurable_snd))
    have hchild (j : ℕ) : MeasurableMenuRecord
        (fun sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) =>
          menuPathSummary P table n j (Fin.tail sample.1) (Fin.tail sample.2)) :=
      (ih j).comp htail
    cases ha : (Parameters.menuEntryAt table (n + 1) k).action with
    | finish =>
      simpa only [menuPathSummary, ha] using
        (MeasurableMenuRecord.const (α := MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1)) menuPathAbandon)
    | abandon =>
      simpa only [menuPathSummary, ha] using
        (MeasurableMenuRecord.const (α := MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1)) menuPathAbandon)
    | test level bad =>
      let test := menuAnalysisTest P level
      have hhead : Measurable (fun sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) =>
          (sample.1 0, (sample.2 0).2)) :=
        ((measurable_pi_apply 0).comp measurable_fst).prodMk
          (((measurable_pi_apply 0).comp measurable_snd).snd)
      have hstop : Measurable (fun sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) =>
          test.rule.stop (sample.1 0) (sample.2 0).2) := test.measurable_stop.comp hhead
      have hcharge : Measurable (fun sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) =>
          P.experiment.observationCharge (test.rule.stop (sample.1 0) (sample.2 0).2)) :=
        (measurable_of_countable P.experiment.observationCharge).comp hstop
      have hcorrect : MeasurableSet {sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) |
          test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1} :=
        measurableSet_eq_fun (test.measurable_decision.comp hhead)
          (((measurable_pi_apply 0).comp measurable_snd).fst)
      have hstopset : MeasurableSet {sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) |
          test.rule.stop (sample.1 0) (sample.2 0).2 = ⊤} :=
        (measurableSet_singleton ⊤).preimage hstop
      let continuation := fun sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1) =>
        if test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1 then
          menuPathSummary P table n k (Fin.tail sample.1) (Fin.tail sample.2)
        else match bad with
          | .abandon => menuPathAbandon
          | .repair =>
              if k = 0 then menuPathAbandon else
                let child := menuPathSummary P table n (k - 1) (Fin.tail sample.1) (Fin.tail sample.2)
                { child with physicalRepairs := child.physicalRepairs + 1 }
      have hcontinuation : MeasurableMenuRecord continuation := by
        dsimp only [continuation]
        apply MeasurableMenuRecord.ite hcorrect (hchild k)
        cases bad with
        | abandon => exact MeasurableMenuRecord.const menuPathAbandon
        | repair =>
          by_cases hk : k = 0
          · simp only [hk, ite_true]
            exact MeasurableMenuRecord.const menuPathAbandon
          · simp only [ite_eq_right hk]
            exact (hchild (k - 1)).incrementRepairs
      have hwhole := MeasurableMenuRecord.ite hstopset
        (MeasurableMenuRecord.const (α := MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1)) menuPathNonreturn)
        (hcontinuation.addObservation hcharge)
      cases bad <;> simpa only [menuPathSummary, ha, test, continuation] using hwhole

theorem measurable_menuPathObservation (P : Parameters) (table : MenuTable) (n k : ℕ) :
    Measurable (fun sample : MenuAnalysisSeed n × MenuAnalysisWorld P n =>
      (menuPathSummary P table n k sample.1 sample.2).observation) := (measurable_menuPathSummary P table n k).1

theorem measurable_menuPathRepairs (P : Parameters) (table : MenuTable) (n k : ℕ) :
    Measurable (fun sample : MenuAnalysisSeed n × MenuAnalysisWorld P n =>
      (menuPathSummary P table n k sample.1 sample.2).physicalRepairs) := (measurable_menuPathSummary P table n k).2.1

theorem measurable_menuPathFailure (P : Parameters) (table : MenuTable) (n k : ℕ) :
    Measurable (fun sample : MenuAnalysisSeed n × MenuAnalysisWorld P n =>
      (menuPathSummary P table n k sample.1 sample.2).failure) := (measurable_menuPathSummary P table n k).2.2

end PDMenu
