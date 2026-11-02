module

public import PaperProofs.Paid.PDROC_MenuExpected_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.MenuExpected

attribute [local instance] Classical.propDecidable

noncomputable def badRecord (P : Parameters) (table : MenuTable) (n k : ℕ) (bad : MenuBadAction)
    (sample : Tail P n) : PDMenu.MenuPathRecord :=
  match bad with
  | .abandon => PDMenu.menuPathAbandon
  | .repair => if k = 0 then PDMenu.menuPathAbandon else
      let child := PDMenu.menuPathSummary P table n (k-1) sample.1 sample.2
      {child with physicalRepairs := child.physicalRepairs+1}

theorem measurable_badRecord (P : Parameters) (table : MenuTable) (n k : ℕ) (bad : MenuBadAction) :
    PDMenu.MeasurableMenuRecord (badRecord P table n k bad) := by
  cases bad with
  | abandon => exact PDMenu.MeasurableMenuRecord.const PDMenu.menuPathAbandon
  | repair =>
      have heq : badRecord P table n k .repair = fun sample : Tail P n =>
          if k=0 then PDMenu.menuPathAbandon else
            let child := PDMenu.menuPathSummary P table n (k-1) sample.1 sample.2
            {child with physicalRepairs := child.physicalRepairs+1} := rfl
      rw [heq]
      by_cases hk : k = 0
      · simpa only [hk, ite_true] using
          (PDMenu.MeasurableMenuRecord.const (α:=Tail P n) PDMenu.menuPathAbandon)
      · simpa only [ite_eq_right hk] using
          (PDMenu.measurable_menuPathSummary P table n (k-1)).incrementRepairs

noncomputable def selectedRecord (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction)
    (sample : Head P × Tail P n) : PDMenu.MenuPathRecord :=
  if sample.1 ∈ correctGate P level then PDMenu.menuPathSummary P table n k sample.2.1 sample.2.2
  else badRecord P table n k bad sample.2

theorem measurable_selectedRecord (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction) :
    PDMenu.MeasurableMenuRecord (selectedRecord P table n k level bad) := by
  exact PDMenu.MeasurableMenuRecord.ite ((measurableSet_correctGate P level).preimage measurable_fst)
    ((PDMenu.measurable_menuPathSummary P table n k).comp measurable_snd)
    ((measurable_badRecord P table n k bad).comp measurable_snd)

theorem summary_test_ae (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n+1) k).action = .test level bad) :
    (fun sample : Tail P (n+1) => PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2) =ᵐ[PDMenu.menuAnalysisLaw P (n+1)]
      fun sample =>
        let selected := selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample)
        {selected with observation := headCharge P level (sample.1 0,sample.2 0)+selected.observation} := by
  filter_upwards [full_head_stop_ae_finite P n level] with sample hfinite
  by_cases hcorrect : (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
  · have hgate : (sample.1 0,sample.2 0) ∈ correctGate P level := hcorrect
    have hs : selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample) =
        PDMenu.menuPathSummary P table n k (Fin.tail sample.1) (Fin.tail sample.2) := by
      dsimp only [selectedRecord, PDMenu.menuAnalysisSplit]
      exact ite_eq_left hgate
    rw [hs]
    dsimp only [PDMenu.menuPathSummary]
    rw [ha]
    dsimp only
    rw [ite_eq_right hfinite]
    rw [ite_eq_left hcorrect]
    rfl
  · have hgate : (sample.1 0,sample.2 0) ∉ correctGate P level := hcorrect
    have hs : selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample) =
        badRecord P table n k bad (Fin.tail sample.1,Fin.tail sample.2) := by
      dsimp only [selectedRecord, PDMenu.menuAnalysisSplit]
      exact ite_eq_right hgate
    rw [hs]
    dsimp only [PDMenu.menuPathSummary]
    rw [ha]
    dsimp only
    rw [ite_eq_right hfinite]
    rw [ite_eq_right hcorrect]
    rfl

theorem selectedRecord_field_apply (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction)
    (field : PDMenu.MenuPathRecord → ℝ≥0∞) (sample : Tail P (n+1)) :
    field (selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample)) =
      if (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
      then field (PDMenu.menuPathSummary P table n k (Fin.tail sample.1) (Fin.tail sample.2))
      else field (badRecord P table n k bad (Fin.tail sample.1,Fin.tail sample.2)) := by
  by_cases hcorrect : (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
  · have hgate : (sample.1 0,sample.2 0) ∈ correctGate P level := hcorrect
    have hs : selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample) =
        PDMenu.menuPathSummary P table n k (Fin.tail sample.1) (Fin.tail sample.2) := by
      dsimp only [selectedRecord, PDMenu.menuAnalysisSplit]
      exact ite_eq_left hgate
    rw [hs]
    exact (ite_eq_left hcorrect).symm
  · have hgate : (sample.1 0,sample.2 0) ∉ correctGate P level := hcorrect
    have hs : selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample) =
        badRecord P table n k bad (Fin.tail sample.1,Fin.tail sample.2) := by
      dsimp only [selectedRecord, PDMenu.menuAnalysisSplit]
      exact ite_eq_right hgate
    rw [hs]
    exact (ite_eq_right hcorrect).symm

theorem selectedRecord_integral (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction)
    (field : PDMenu.MenuPathRecord → ℝ≥0∞)
    (hg : Measurable (fun sample : Tail P n => field (PDMenu.menuPathSummary P table n k sample.1 sample.2)))
    (hb : Measurable (fun sample : Tail P n => field (badRecord P table n k bad sample))) :
    (∫⁻ sample : Tail P (n+1), field (selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample))
      ∂PDMenu.menuAnalysisLaw P (n+1)) =
      ENNReal.ofReal (1-(P.binarySymmetric.endpointError level:ℝ)) *
        (∫⁻ sample : Tail P n, field (PDMenu.menuPathSummary P table n k sample.1 sample.2) ∂PDMenu.menuAnalysisLaw P n) +
      ENNReal.ofReal (P.binarySymmetric.endpointError level:ℝ) *
        (∫⁻ sample : Tail P n, field (badRecord P table n k bad sample) ∂PDMenu.menuAnalysisLaw P n) := by
  calc
    _ = ∫⁻ sample : Tail P (n+1),
        if (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
        then field (PDMenu.menuPathSummary P table n k (Fin.tail sample.1) (Fin.tail sample.2))
        else field (badRecord P table n k bad (Fin.tail sample.1,Fin.tail sample.2))
        ∂PDMenu.menuAnalysisLaw P (n+1) :=
      lintegral_congr (selectedRecord_field_apply P table n k level bad field)
    _ = _ := selected_analysis_integral P n level _ _ hg hb

theorem summary_test_observation_integral (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n+1) k).action = .test level bad) :
    (∫⁻ sample : Tail P (n+1), (PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2).observation
      ∂PDMenu.menuAnalysisLaw P (n+1)) =
      ENNReal.ofReal (P.binarySymmetric.endpointCharge level:ℝ) +
      ENNReal.ofReal (1-(P.binarySymmetric.endpointError level:ℝ)) *
        (∫⁻ sample : Tail P n, (PDMenu.menuPathSummary P table n k sample.1 sample.2).observation ∂PDMenu.menuAnalysisLaw P n) +
      ENNReal.ofReal (P.binarySymmetric.endpointError level:ℝ) *
        (∫⁻ sample : Tail P n, (badRecord P table n k bad sample).observation ∂PDMenu.menuAnalysisLaw P n) := by
  have he : (fun sample : Tail P (n+1) => (PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2).observation) =ᵐ[PDMenu.menuAnalysisLaw P (n+1)]
      fun sample => headCharge P level (sample.1 0,sample.2 0)+
        (selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample)).observation := by
    filter_upwards [summary_test_ae P table n k level bad ha] with sample hs
    rw [hs]
  have hm : Measurable (fun sample : Tail P (n+1) => headCharge P level (sample.1 0,sample.2 0)) :=
    (measurable_headCharge P level).comp
      (((measurable_pi_apply 0).comp measurable_fst).prodMk ((measurable_pi_apply 0).comp measurable_snd))
  rw [lintegral_congr_ae he, lintegral_add_left hm, full_headCharge_integral,
    selectedRecord_integral P table n k level bad (fun record => record.observation)
      (PDMenu.measurable_menuPathObservation P table n k) (measurable_badRecord P table n k bad).1]
  exact add_assoc _ _ _ |>.symm

theorem summary_test_repairs_integral (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n+1) k).action = .test level bad) :
    (∫⁻ sample : Tail P (n+1), ((PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2).physicalRepairs:ℝ≥0∞)
      ∂PDMenu.menuAnalysisLaw P (n+1)) =
      ENNReal.ofReal (1-(P.binarySymmetric.endpointError level:ℝ)) *
        (∫⁻ sample : Tail P n, ((PDMenu.menuPathSummary P table n k sample.1 sample.2).physicalRepairs:ℝ≥0∞) ∂PDMenu.menuAnalysisLaw P n) +
      ENNReal.ofReal (P.binarySymmetric.endpointError level:ℝ) *
        (∫⁻ sample : Tail P n, ((badRecord P table n k bad sample).physicalRepairs:ℝ≥0∞) ∂PDMenu.menuAnalysisLaw P n) := by
  have he : (fun sample : Tail P (n+1) => ((PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2).physicalRepairs:ℝ≥0∞)) =ᵐ[PDMenu.menuAnalysisLaw P (n+1)]
      fun sample => ((selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample)).physicalRepairs:ℝ≥0∞) := by
    filter_upwards [summary_test_ae P table n k level bad ha] with sample hs
    rw [hs]
  rw [lintegral_congr_ae he]
  exact selectedRecord_integral P table n k level bad (fun record => (record.physicalRepairs:ℝ≥0∞))
    ((measurable_of_countable (fun count : ℕ => (count:ℝ≥0∞))).comp (PDMenu.measurable_menuPathRepairs P table n k))
    ((measurable_of_countable (fun count : ℕ => (count:ℝ≥0∞))).comp (measurable_badRecord P table n k bad).2.1)

theorem summary_test_failure_integral (P : Parameters) (table : MenuTable) (n k level : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n+1) k).action = .test level bad) :
    (∫⁻ sample : Tail P (n+1), failureValue (PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2)
      ∂PDMenu.menuAnalysisLaw P (n+1)) =
      ENNReal.ofReal (1-(P.binarySymmetric.endpointError level:ℝ)) *
        (∫⁻ sample : Tail P n, failureValue (PDMenu.menuPathSummary P table n k sample.1 sample.2) ∂PDMenu.menuAnalysisLaw P n) +
      ENNReal.ofReal (P.binarySymmetric.endpointError level:ℝ) *
        (∫⁻ sample : Tail P n, failureValue (badRecord P table n k bad sample) ∂PDMenu.menuAnalysisLaw P n) := by
  have he : (fun sample : Tail P (n+1) => failureValue (PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2)) =ᵐ[PDMenu.menuAnalysisLaw P (n+1)]
      fun sample => failureValue (selectedRecord P table n k level bad (PDMenu.menuAnalysisSplit P n sample)) := by
    filter_upwards [summary_test_ae P table n k level bad ha] with sample hs
    rw [hs]
    rfl
  rw [lintegral_congr_ae he]
  exact selectedRecord_integral P table n k level bad failureValue
    (measurable_summary_failureValue P table n k)
    ((measurable_of_countable (fun bit : Bool => if bit=true then (1:ℝ≥0∞) else 0)).comp
      (measurable_badRecord P table n k bad).2.2)

end PDROC.MenuExpected
