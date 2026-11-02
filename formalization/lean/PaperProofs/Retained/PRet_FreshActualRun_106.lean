module

public import PaperProofs.Retained.PRet_FreshActualEntry_103

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshActualRun106

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshActualEntry103 PRetFreshSuffixRun101

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Actual all-clock continuation transport after the genuine finite local
test, with no externally supplied alignment, legality or run certificate. -/
theorem run_view_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
    let pre := (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history
    let before := pre ++ [.advanced head]
    let child := if historyWritten before head = (historyReport before head).map Prod.fst then good else bad
    ∀ k, ReferenceSuffixView I 1 before
      (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 2 + k))
      (run (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1))
        child.rule (sample.1, referenceSuffixWorld input 1 sample.2) k) := by
  obtain ⟨hn, hc, hw, hwrite, hreport, hcommit, hexec, hobs, hstart⟩ :=
    actual_entry_facts input head hhead test good bad sample n hstop
  exact actual_run_view input head hhead test good bad sample _ hn hc hw hwrite hreport hcommit hexec hobs (n + 2) hstart

end PaperProofs.Retained.PRetFreshActualRun106
