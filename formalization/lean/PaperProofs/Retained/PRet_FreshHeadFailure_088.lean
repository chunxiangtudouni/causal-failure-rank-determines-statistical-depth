module

public import PaperProofs.Retained.PRet_JointCharges_075
public import PaperProofs.Retained.PRet_OutputCompletion_049
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadFailure088

open Common Common.Native PRetAmbientComparator073 PRetJointCharges075 PRetOutputCompletion049
open scoped ENNReal

variable {Physical Ambient : Instance} {Seed : Type*} [MeasurableSpace Seed]

private theorem bool_eq_not_of_ne (bit truth : Bool) (hne : bit ≠ truth) : bit = !truth := by
  cases bit <;> cases truth <;> simp_all

/-- Joint ambient matching excludes an unmatchable head insertion on every
actually successful source path. Actual payment/repair success is NOT used. -/
theorem jointSuccess_headCorrect (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Seed)
    (embed : Physical.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (head : Physical.Stage) (hhead : head.val = 0) (hbad : ¬ Matchable Ambient (insert (embed head) old))
    (sample : Seed × input.World) (hs : jointSuccess input embed old source.rule sample) :
    headExitDecision input head source.rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head := by
  obtain ⟨n, _, hf, _, hm⟩ := hs
  have hall := run_finished_allWritten input (freshContract Physical) .uncapped (zeroNormalAccounting Physical)
    source.rule source.legal sample n hf
  cases hw : (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample n).ledger.written head with
  | none => exact False.elim (hall head hw)
  | some bit =>
    have hd := nativeHead_decision_of_written input (freshContract Physical) (zeroNormalAccounting Physical)
      source.rule source.legal head hhead sample n bit hw
    by_contra hn
    have hne : bit ≠ (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample n).ledger.truth head := by
      intro heq
      apply hn
      rw [hd, heq, run_truth input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule source.legal sample n]
    have hwrong := hw.trans (congrArg some (bool_eq_not_of_ne bit _ hne))
    apply hbad
    apply hm.subset
    apply Finset.insert_subset_iff.mpr
    exact ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨head, (mem_ordinaryMismatches _ head).mpr hwrong, rfl⟩)), Finset.subset_union_left⟩

/-- On a bad unmatchable head, the one actual fresh failure penalty pays
the local head error; finite-paid early exit/nonreturn remains present. -/
theorem unmatchable_head_charge_lower (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Seed)
    (embed : Physical.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (head : Physical.Stage) (hhead : head.val = 0) (hbad : ¬ Matchable Ambient (insert (embed head) old))
    (sample : Seed × input.World) (penalty : ℝ≥0∞) :
    (input.experiment head).observationCharge (headExitStop input head source.rule sample.1 (worldTapes input sample.2 head)) +
      (if headExitDecision input head source.rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
        then 0 else penalty) ≤ jointCharge input embed old source.rule penalty sample := by
  classical
  apply add_le_add (nativeHead_observationCharge_le input (freshContract Physical) (zeroNormalAccounting Physical)
    source.rule head hhead sample)
  by_cases hs : jointSuccess input embed old source.rule sample
  · have hc := jointSuccess_headCorrect input source embed old head hhead hbad sample hs
    simp only [hs, hc, ↓reduceIte, le_refl]
  · simp only [hs, ↓reduceIte]
    split_ifs
    · exact bot_le
    · exact le_rfl

end PaperProofs.Retained.PRetFreshHeadFailure088
