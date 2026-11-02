module

public import PaperProofs.Paid.PDROC_OverlaySimulator_030

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Finite-prefix error domination, for success assembly. This theorem is
pointwise, independent of SourceHistoryLaw and probability, and imports no
OverlaySuccess module. -/
theorem overlay_actual_error_prefix (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (n : ℕ) (stage : P.sharedInstance.Stage)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage =
      some (!(run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.truth stage)) :
    reportedWriteError (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) stage = some true := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  have hd := actualOrdinaryDecision_of_written P fee hfee C .uncapped accounting actual hl sample n stage
    (!(run input C.val .uncapped accounting actual sample n).ledger.truth stage) hw
  have ht := congrFun (run_truth input C.val .uncapped accounting actual hl sample n) stage
  have he : P.actualWriteError fee hfee C accounting actual stage sample := by
    unfold PaperProofs.Paid.Parameters.actualWriteError
    exact hd.trans (congrArg (fun bit => some (!bit)) ht)
  have hv := (overlayPathCoupling P fee hfee C accounting source).2.1 sample stage he
  exact (overlay_virtual_error_at_written P fee hfee C accounting source sample stage n _ hw).mp hv

end PDROC
