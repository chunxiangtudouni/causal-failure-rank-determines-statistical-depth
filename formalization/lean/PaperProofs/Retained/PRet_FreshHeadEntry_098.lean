module

public import PaperProofs.Retained.PRet_FreshHeadAdvance_097

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadEntry098

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshHeadRun080 PRetFreshHeadAdvance097

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The actual chosen finite local stopping time gives a UNIQUE genuine
first entry of the actual stitched Policy at cursor1, for either head bit. -/
theorem firstEntry_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad) (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    FirstEntryAt input (freshContract I) .uncapped (zeroNormalAccounting I)
      (twoContinuationPolicy input head test good bad hgood hbad).rule 1 (n + 2) sample := by
  let after := postHeadRaw head good bad
  let policy := twoContinuationPolicy input head test good bad hgood hbad
  have hr := run_advance_at input head hhead test good bad hgood hbad sample n hstop
  change (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 2)).cursor = 1 ∧ _
  refine ⟨?_, ?_⟩
  · rw [hr]
    rfl
  · intro k hk
    have hzero : (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample k).cursor = 0 := by
      by_cases hkn : k ≤ n
      · have hb : (k : ℕ∞) ≤ test.rule.stop sample.1 (worldTapes input sample.2 head) := by
          rw [hstop]
          exact_mod_cast hkn
        have hprefix := run_before input head hhead test after sample k hb
        change run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample k =
          headReviewState input (zeroNormalAccounting I) head (input.truthAt sample.2) (worldTapes input sample.2 head) k at hprefix
        rw [hprefix]
        exact headReviewState_cursor input (zeroNormalAccounting I) head _ _ k
      · have heq : k = n + 1 := by omega
        subst k
        have hw := run_write_at input head hhead test after sample n hstop
        change run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1) =
          bellmanHeadWrittenState input (freshContract I) (zeroNormalAccounting I) head (input.truthAt sample.2)
            (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) at hw
        rw [hw]
        exact bellmanHeadWrittenState_cursor input (freshContract I) (zeroNormalAccounting I) head _ _ n _
    rw [hzero]
    exact Nat.zero_ne_one

end PaperProofs.Retained.PRetFreshHeadEntry098
