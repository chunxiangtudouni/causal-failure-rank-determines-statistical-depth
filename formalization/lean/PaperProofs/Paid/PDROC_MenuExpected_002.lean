module

public import PaperProofs.Paid.PDROC_MenuExpected_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.MenuExpected

attribute [local instance] Classical.propDecidable

abbrev Tail (P : Parameters) (n : ℕ) := PDMenu.MenuAnalysisSeed n × PDMenu.MenuAnalysisWorld P n

theorem measurable_selected {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (gate : Set A) (hgate : MeasurableSet gate) (good bad : B → ℝ≥0∞)
    (hg : Measurable good) (hb : Measurable bad) :
    Measurable (fun pair : A × B => if pair.1 ∈ gate then good pair.2 else bad pair.2) := by
  classical
  exact Measurable.ite (hgate.preimage measurable_fst) (hg.comp measurable_snd) (hb.comp measurable_snd)

/-- Tonelli uses the full head sample. No independence of duration and
correctness inside that head sample is required. -/
theorem selected_product_integral {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (gate : Set A) (hgate : MeasurableSet gate) (good bad : B → ℝ≥0∞)
    (hg : Measurable good) (hb : Measurable bad) :
    (∫⁻ pair, if pair.1 ∈ gate then good pair.2 else bad pair.2 ∂μ.prod ν) =
      μ gate * (∫⁻ x, good x ∂ν) + μ gateᶜ * (∫⁻ x, bad x ∂ν) := by
  classical
  let gpart : A × B → ℝ≥0∞ := fun pair => gate.indicator (fun _ => 1) pair.1 * good pair.2
  let bpart : A × B → ℝ≥0∞ := fun pair => gateᶜ.indicator (fun _ => 1) pair.1 * bad pair.2
  have hgm : Measurable (gate.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hgate
  have hbm : Measurable (gateᶜ.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hgate.compl
  have hpart : Measurable gpart := (hgm.comp measurable_fst).mul (hg.comp measurable_snd)
  have hpoint : (fun pair : A × B => if pair.1 ∈ gate then good pair.2 else bad pair.2) =
      fun pair => gpart pair + bpart pair := by
    funext pair
    by_cases h : pair.1 ∈ gate <;> simp [gpart, bpart, h]
  rw [hpoint, lintegral_add_left hpart]
  have hgi := lintegral_prod_mul (μ:=μ) (ν:=ν) hgm.aemeasurable hg.aemeasurable
  have hbi := lintegral_prod_mul (μ:=μ) (ν:=ν) hbm.aemeasurable hb.aemeasurable
  rw [lintegral_indicator_fun_one hgate] at hgi
  rw [lintegral_indicator_fun_one hgate.compl] at hbi
  exact congrArg₂ (·+·) hgi hbi

theorem split_integral (P : Parameters) (n : ℕ) (f : Head P × Tail P n → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ sample, f (PDMenu.menuAnalysisSplit P n sample) ∂PDMenu.menuAnalysisLaw P (n+1)) =
      ∫⁻ pair, f pair ∂(headLaw P).prod (PDMenu.menuAnalysisLaw P n) :=
  (PDMenu.menuAnalysisSplit_measurePreserving P n).lintegral_comp hf

theorem full_head_stop_ae_finite (P : Parameters) (n level : ℕ) :
    ∀ᵐ sample : Tail P (n+1) ∂PDMenu.menuAnalysisLaw P (n+1),
      (PDMenu.menuAnalysisTest P level).rule.stop (sample.1 0) (sample.2 0).2 ≠ ⊤ := by
  have hp := (measurePreserving_fst (μ:=headLaw P) (ν:=PDMenu.menuAnalysisLaw P n)).quasiMeasurePreserving.ae
    (head_stop_ae_finite P level)
  exact (PDMenu.menuAnalysisSplit_measurePreserving P n).quasiMeasurePreserving.ae hp

theorem selected_analysis_integral (P : Parameters) (n level : ℕ) (good bad : Tail P n → ℝ≥0∞)
    (hg : Measurable good) (hb : Measurable bad) :
    (∫⁻ sample : Tail P (n+1),
      if (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
      then good (Fin.tail sample.1,Fin.tail sample.2) else bad (Fin.tail sample.1,Fin.tail sample.2)
      ∂PDMenu.menuAnalysisLaw P (n+1)) =
      ENNReal.ofReal (1-(P.binarySymmetric.endpointError level:ℝ)) * (∫⁻ x, good x ∂PDMenu.menuAnalysisLaw P n) +
      ENNReal.ofReal (P.binarySymmetric.endpointError level:ℝ) * (∫⁻ x, bad x ∂PDMenu.menuAnalysisLaw P n) := by
  classical
  let f : Head P × Tail P n → ℝ≥0∞ :=
    fun pair => if pair.1 ∈ correctGate P level then good pair.2 else bad pair.2
  have hf : Measurable f := measurable_selected _ (measurableSet_correctGate P level) _ _ hg hb
  have hpoint : (fun sample : Tail P (n+1) =>
      if (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
      then good (Fin.tail sample.1,Fin.tail sample.2) else bad (Fin.tail sample.1,Fin.tail sample.2)) =
      fun sample => f (PDMenu.menuAnalysisSplit P n sample) := by
    funext sample
    by_cases h : (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
    · have hgate : (sample.1 0,sample.2 0) ∈ correctGate P level := h
      simp only [f, PDMenu.menuAnalysisSplit, ite_eq_left h, ite_eq_left hgate]
    · have hgate : (sample.1 0,sample.2 0) ∉ correctGate P level := h
      simp only [f, PDMenu.menuAnalysisSplit, ite_eq_right h, ite_eq_right hgate]
  rw [hpoint, split_integral P n f hf]
  exact (selected_product_integral (headLaw P) (PDMenu.menuAnalysisLaw P n)
    (correctGate P level) (measurableSet_correctGate P level) good bad hg hb).trans
      (by rw [correct_mass, wrong_mass])

theorem full_headCharge_integral (P : Parameters) (n level : ℕ) :
    (∫⁻ sample : Tail P (n+1),
      headCharge P level (sample.1 0,sample.2 0) ∂PDMenu.menuAnalysisLaw P (n+1)) =
      ENNReal.ofReal (P.binarySymmetric.endpointCharge level:ℝ) := by
  have hf : Measurable (fun pair : Head P × Tail P n => headCharge P level pair.1) :=
    (measurable_headCharge P level).comp measurable_fst
  have hs := split_integral P n (fun pair => headCharge P level pair.1) hf
  have hp := (measurePreserving_fst (μ:=headLaw P) (ν:=PDMenu.menuAnalysisLaw P n)).lintegral_comp
    (measurable_headCharge P level)
  exact hs.trans (hp.trans (headCharge_integral P level))

noncomputable def failureValue (record : PDMenu.MenuPathRecord) : ℝ≥0∞ :=
  if record.failure = true then 1 else 0

theorem measurable_summary_failureValue (P : Parameters) (table : MenuTable) (n k : ℕ) :
    Measurable (fun sample : Tail P n => failureValue (PDMenu.menuPathSummary P table n k sample.1 sample.2)) :=
  (measurable_of_countable (fun bit : Bool => if bit = true then (1:ℝ≥0∞) else 0)).comp
    (PDMenu.measurable_menuPathFailure P table n k)

theorem failure_measure_eq_integral (P : Parameters) (table : MenuTable) (n k : ℕ) :
    (PDMenu.menuAnalysisLaw P n) {sample | (PDMenu.menuPathSummary P table n k sample.1 sample.2).failure = true} =
      ∫⁻ sample : Tail P n, failureValue (PDMenu.menuPathSummary P table n k sample.1 sample.2)
        ∂PDMenu.menuAnalysisLaw P n := by
  have hm : MeasurableSet {sample : Tail P n | (PDMenu.menuPathSummary P table n k sample.1 sample.2).failure = true} :=
    (measurableSet_singleton true).preimage (PDMenu.measurable_menuPathFailure P table n k)
  simpa only [Set.indicator, Set.mem_ofPred_eq, failureValue] using
    (lintegral_indicator_fun_one (μ:=PDMenu.menuAnalysisLaw P n) hm).symm

end PDROC.MenuExpected
