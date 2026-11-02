module

public import PaperProofs.Paid.PDROC_OverlaySimulator_039
public import PaperProofs.Paid.PDROC_OverlayCorrect_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- Both actual correctness branches realize the same full source stage
exit. The first real exit is retained even when ghost repair compresses
multiple source calls into one physical step. -/
theorem overlay_postwrite_first_exit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).ledger.written stage ≠ none)
    (hfresh : ∀ pair ∈ historyCommitments (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history), pair.1.stage ≠ stage)
    (hgood : sourcePostwriteGuardGood source sample.1.1 stage (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history)) :
    ∃ exit : ℕ, exit ≤ 3 ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + exit)).halted = true ∨
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + exit)).cursor = stage.val + 1) ∧
      (∀ k < exit, (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).cursor = stage.val) ∧
      postwriteStageTrace source sample.1.1 stage (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history) 3 =
        overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + exit)).history := by
  obtain ⟨bit, hb⟩ := Option.ne_none_iff_exists'.mp hw
  by_cases he : bit = (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).ledger.truth stage
  · have hcorrect := hb.trans (congrArg some he)
    have hcap := overlay_correct_postwrite_exit P fee hfee C accounting source sample start stage ha hc hcorrect hfresh hgood
    refine ⟨1, by omega, hcap.2, ?_, hcap.1⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa only [Nat.add_zero] using And.intro ha hc
  · have hwrong := hb.trans (congrArg some (Bool.eq_not_iff.mpr he))
    exact overlay_wrong_postwrite_first_exit P fee hfee C accounting source sample start stage ha hc hwrong hgood

end PDROC
