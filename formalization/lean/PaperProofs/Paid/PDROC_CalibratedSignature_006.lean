module

public import PaperProofs.Paid.PDROC_CalibratedSignature_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.CalibratedSignature

universe u v

theorem executionSignature_eq_of_same_run (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} {Seed' : Type v}
    (rule : PolicyRule P.sharedInstance Seed) (rule' : PolicyRule P.sharedInstance Seed')
    (sample : Seed × (P.input fee hfee).World) (sample' : Seed' × (P.input fee hfee).World)
    (hrun : ∀ clock, run (P.input fee hfee) C.val mode accounting rule sample clock =
      run (P.input fee hfee) C.val mode accounting rule' sample' clock) :
    P.executionSignature fee hfee C mode accounting rule sample =
      P.executionSignature fee hfee C mode accounting rule' sample' := by
  classical
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext stage
    change decide (∃ n, (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage =
      some ((run (P.input fee hfee) C.val mode accounting rule sample n).ledger.truth stage)) =
      decide (∃ n, (run (P.input fee hfee) C.val mode accounting rule' sample' n).ledger.written stage =
        some ((run (P.input fee hfee) C.val mode accounting rule' sample' n).ledger.truth stage))
    apply decide_eq_decide.mpr
    exact exists_congr fun n => by rw [hrun n]
  · funext stage
    change decide (∃ n, (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage =
      some (!(run (P.input fee hfee) C.val mode accounting rule sample n).ledger.truth stage)) =
      decide (∃ n, (run (P.input fee hfee) C.val mode accounting rule' sample' n).ledger.written stage =
        some (!(run (P.input fee hfee) C.val mode accounting rule' sample' n).ledger.truth stage))
    apply decide_eq_decide.mpr
    exact exists_congr fun n => by rw [hrun n]
  · funext stage tool
    change decide (∃ n, ∃ execution ∈ (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.executions,
      execution.handle.stage = stage ∧ execution.tool = tool) =
      decide (∃ n, ∃ execution ∈ (run (P.input fee hfee) C.val mode accounting rule' sample' n).ledger.executions,
        execution.handle.stage = stage ∧ execution.tool = tool)
    apply decide_eq_decide.mpr
    exact exists_congr fun n => by rw [hrun n]
  · change decide (¬runSuccess (P.input fee hfee) C.val mode accounting rule sample) =
      decide (¬runSuccess (P.input fee hfee) C.val mode accounting rule' sample')
    apply decide_eq_decide.mpr
    apply not_congr
    unfold runSuccess
    exact exists_congr fun n => by rw [hrun n]

theorem observationBill_eq_of_same_run {I : Instance} {Seed : Type u} {Seed' : Type v}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (rule' : PolicyRule I Seed') (sample : Seed × input.World) (sample' : Seed' × input.World)
    (hrun : ∀ clock, run input C mode accounting rule sample clock = run input C mode accounting rule' sample' clock) :
    runObservationBill input C mode accounting rule sample = runObservationBill input C mode accounting rule' sample' := by
  unfold runObservationBill
  apply iSup_congr
  intro clock
  rw [hrun clock]

end PDROC.CalibratedSignature
