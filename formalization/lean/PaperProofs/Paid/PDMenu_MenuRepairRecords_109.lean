module

public import PaperProofs.Paid.PDMenu_MenuRepairRun_105
public import PaperProofs.Paid.PDMenu_MenuSegmentCharge_106

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance}

/-- A name for the three original protocol records already identified by
the actual run theorem105. It is not a replacement program or cost model. -/
def menuRepairedFrom (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tool : I.Tool) : State I :=
  let handle : MismatchHandle I := ⟨stage, start.ledger.writeSerial stage⟩
  let allocated := record accounting start (.allocate handle tool) [.committed handle tool]
    (allocateLedger start handle tool) start.cursor false
  let executed := record accounting allocated (.execute handle tool) [.executed handle tool]
    (executeLedger allocated handle tool) allocated.cursor false
  record accounting executed (.advance stage) [.advanced stage]
    (advanceLedger executed stage) (executed.cursor + 1) false

theorem menuRepairedFrom_cursor (accounting : NormalAccounting I) (stage : I.Stage) (start : State I) (tool : I.Tool) :
    (menuRepairedFrom accounting stage start tool).cursor = start.cursor + 1 := rfl

theorem menuRepairedFrom_active (accounting : NormalAccounting I) (stage : I.Stage) (start : State I) (tool : I.Tool) :
    (menuRepairedFrom accounting stage start tool).halted = false := rfl

theorem menuRepairedFrom_written (accounting : NormalAccounting I) (stage : I.Stage) (start : State I) (tool : I.Tool) :
    (menuRepairedFrom accounting stage start tool).ledger.written = start.ledger.written := rfl

theorem menuRepairedFrom_truth (accounting : NormalAccounting I) (stage : I.Stage) (start : State I) (tool : I.Tool) :
    (menuRepairedFrom accounting stage start tool).ledger.truth = start.ledger.truth := rfl

theorem menuRepairedFrom_reviews (accounting : NormalAccounting I) (stage : I.Stage) (start : State I) (tool : I.Tool) :
    (menuRepairedFrom accounting stage start tool).ledger.reviews = start.ledger.reviews := rfl

theorem menuRepairedFrom_executionCount (accounting : NormalAccounting I) (stage : I.Stage) (start : State I) (tool : I.Tool) :
    (menuRepairedFrom accounting stage start tool).ledger.executions.length = start.ledger.executions.length + 1 := by
  simp only [menuRepairedFrom, record, advanceLedger, executeLedger, allocateLedger,
    List.length_append, List.length_singleton]

theorem menuRepairedFrom_actualBill (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tool : I.Tool) (fees : Fees I) :
    (menuRepairedFrom accounting stage start tool).ledger.actualBill fees =
      start.ledger.actualBill fees + ENNReal.ofReal (fees.correction stage tool : ℝ) := by
  unfold menuRepairedFrom
  rw [record_actualBill, advance_actualBill, record_actualBill, execute_actualBill,
    record_actualBill, allocate_actualBill]

theorem menuRepairedFrom_remainingTools (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tool : I.Tool) (K : ℕ) :
    K - (menuRepairedFrom accounting stage start tool).ledger.executions.length =
      (K - start.ledger.executions.length) - 1 := by
  rw [menuRepairedFrom_executionCount, Nat.sub_add_eq]

end PDMenu
