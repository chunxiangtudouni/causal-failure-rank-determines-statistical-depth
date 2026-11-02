module

public import PaperProofs.Paid.PDROC_CalibratedLaw_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.CalibratedLaw

theorem executionSignature_eq_of_runs {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (left : PolicyRule P.sharedInstance A) (right : PolicyRule P.sharedInstance B)
    (a : A × (P.input fee hfee).World) (b : B × (P.input fee hfee).World)
    (runs : ∀ clock, run (P.input fee hfee) C.val mode accounting left a clock =
      run (P.input fee hfee) C.val mode accounting right b clock) :
    P.executionSignature fee hfee C mode accounting left a =
      P.executionSignature fee hfee C mode accounting right b := by
  classical
  have flag (predicate : State P.sharedInstance → Prop) :
      P.eventualFlag fee hfee C mode accounting left predicate a =
        P.eventualFlag fee hfee C mode accounting right predicate b := by
    change decide (∃ clock, predicate (run (P.input fee hfee) C.val mode accounting left a clock)) =
      decide (∃ clock, predicate (run (P.input fee hfee) C.val mode accounting right b clock))
    apply congrArg (fun proposition : Prop => decide proposition)
    exact propext (exists_congr (fun clock => by rw [runs clock]))
  have success : runSuccess (P.input fee hfee) C.val mode accounting left a ↔
      runSuccess (P.input fee hfee) C.val mode accounting right b :=
    exists_congr (fun clock => by rw [runs clock])
  unfold Parameters.executionSignature
  refine Prod.ext
    (funext fun stage => flag (fun current => current.ledger.written stage = some (current.ledger.truth stage)))
    (Prod.ext
      (funext fun stage => flag (fun current => current.ledger.written stage = some (!current.ledger.truth stage)))
      (Prod.ext (funext fun stage => funext fun tool => flag
        (fun current => ∃ execution ∈ current.ledger.executions,
          execution.handle.stage = stage ∧ execution.tool = tool)) ?_))
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using not_congr success

theorem observationBill_eq_of_runs {A B : Type*}
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (left : PolicyRule P.sharedInstance A) (right : PolicyRule P.sharedInstance B)
    (a : A × (P.input fee hfee).World) (b : B × (P.input fee hfee).World)
    (runs : ∀ clock, run (P.input fee hfee) C.val mode accounting left a clock =
      run (P.input fee hfee) C.val mode accounting right b clock) :
    runObservationBill (P.input fee hfee) C.val mode accounting left a =
      runObservationBill (P.input fee hfee) C.val mode accounting right b := by
  simp only [runObservationBill, runs]

end PDROC.CalibratedLaw
