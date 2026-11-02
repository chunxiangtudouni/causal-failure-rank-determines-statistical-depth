module

public import PaperProofs.Common.NativeHeadAccounting
public import PaperProofs.Paid.PDMenu_SuffixActualCharge_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

noncomputable def paidHeadContinuationWeight (input : StatisticalInput I) (head : I.Stage)
    (rule : PolicyRule I Seed) (good bad : ℝ≥0∞) (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact if headExitDecision input head rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
    then good else bad

noncomputable def paidEntryContinuationWeight (head : I.Stage) (startup : Startup I)
    (good bad : ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact if HeadCorrectStartup head startup then good else bad
theorem paidHeadContinuationWeight_le (input : StatisticalInput I) (head : I.Stage)
    (rule : PolicyRule I Seed) (good bad penalty : ℝ≥0∞) (hg : good ≤ penalty) (hb : bad ≤ penalty)
    (sample : Seed × input.World) : paidHeadContinuationWeight input head rule good bad sample ≤ penalty := by
  unfold paidHeadContinuationWeight
  split_ifs
  · exact hg
  · exact hb

theorem paidHeadContinuationWeight_on_entry (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (clock : ℕ)
    (hentry : FirstEntryAt input C .uncapped accounting rule 1 clock sample) (good bad : ℝ≥0∞) :
    paidHeadContinuationWeight input head rule good bad sample =
      paidEntryContinuationWeight head (publicStartup (run input C .uncapped accounting rule sample clock)) good bad := by
  classical
  have hc := firstEntry_one_local_correct_iff input C hearly accounting rule hlegal head hhead sample clock hentry
  unfold paidHeadContinuationWeight paidEntryContinuationWeight
  by_cases hcorrect : HeadCorrectStartup head (publicStartup (run input C .uncapped accounting rule sample clock))
  · have hl := hc.mp hcorrect
    simp only [hcorrect, hl, ite_true]
  · have hl : ¬ headExitDecision input head rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head :=
      fun h => hcorrect (hc.mpr h)
    simp only [hcorrect, hl, ite_false]

/-- The non-arrival complement pays the same local testing charge and both
successor weights from its actual observation spending and global failure. -/
theorem paidHead_no_entry_charge_lower (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (next : I.Stage) (hnext : next.val = 1) (sample : Seed × input.World)
    (hnever : ∀ clock, (run input C .uncapped accounting rule sample clock).cursor ≠ 1)
    (good bad penalty : ℝ≥0∞) (hg : good ≤ penalty) (hb : bad ≤ penalty) :
    (input.experiment head).observationCharge
        (headExitStop input head rule sample.1 (worldTapes input sample.2 head)) +
      paidHeadContinuationWeight input head rule good bad sample ≤
        runPaidPenaltyCharge input C accounting rule penalty sample := by
  have hfailure := no_stage_one_entry_failure input C .uncapped accounting rule hlegal sample next hnext hnever
  unfold runPaidPenaltyCharge
  simp only [hfailure, ↓reduceIte]
  exact add_le_add ((nativeHead_observationCharge_le input C accounting rule head hhead sample).trans
    (runObservationBill_le_actual input C .uncapped accounting rule sample))
    (paidHeadContinuationWeight_le input head rule good bad penalty hg hb sample)

end PDMenu


