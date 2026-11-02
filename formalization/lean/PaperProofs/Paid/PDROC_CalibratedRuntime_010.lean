module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_007
public import PaperProofs.Paid.PDMenu_MenuRepairRecords_109
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

theorem advanceRecord_used {I : Instance} (accounting : NormalAccounting I)
    (state : State I) (stage : I.Stage) :
    historyUsed (record accounting state (.advance stage) [.advanced stage]
      (advanceLedger state stage) (state.cursor + 1) false).history = historyUsed state.history := by
  simp only [record, historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons,
    eventCommitment, List.filterMap_nil, List.append_nil]

theorem menuRepairedFrom_used {I : Instance} (accounting : NormalAccounting I)
    (stage : I.Stage) (state : State I) (tool : I.Tool) :
    historyUsed (PDMenu.menuRepairedFrom accounting stage state tool).history =
      insert tool (historyUsed state.history) := by
  classical
  ext other
  simp [PDMenu.menuRepairedFrom, record, historyUsed, historyCommitments, List.filterMap_append, eventCommitment]

theorem advanceRecord_pairs (P : Parameters) (accounting : NormalAccounting P.sharedInstance)
    (state : State P.sharedInstance) (stage : P.sharedInstance.Stage) :
    executionPairs P (record accounting state (.advance stage) [.advanced stage]
      (advanceLedger state stage) (state.cursor + 1) false).ledger = executionPairs P state.ledger := rfl

theorem menuRepairedFrom_pairs (P : Parameters) (accounting : NormalAccounting P.sharedInstance)
    (stage : P.sharedInstance.Stage) (state : State P.sharedInstance) (tool : Fin P.tools) :
    executionPairs P (PDMenu.menuRepairedFrom accounting stage state tool).ledger =
      executionPairs P state.ledger ++ [(stage.val, tool)] := by
  simp only [executionPairs, PDMenu.menuRepairedFrom, record, advanceLedger, executeLedger,
    allocateLedger, List.map_append, List.map_singleton]

theorem menuWrittenFrom_pairs (P : Parameters) (input : StatisticalInput P.sharedInstance)
    (C : Contract P.sharedInstance) (accounting : NormalAccounting P.sharedInstance)
    (stage : P.sharedInstance.Stage) (state : State P.sharedInstance)
    (tape : (input.experiment stage).Tape) (reviews : ℕ) (bit : Bool) :
    executionPairs P (menuWrittenFrom input C accounting stage state tape reviews bit).ledger =
      executionPairs P state.ledger := by
  have he := (menuWrittenFrom_fields input C accounting stage state tape reviews bit).2.2.2.2.2.1
  unfold executionPairs
  rw [he]

theorem run_written_at_later {I : Instance} {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start ended : ℕ) (hle : start ≤ ended) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    (run input C mode accounting rule sample ended).ledger.written stage = some bit := by
  have h := run_written_some_after input C mode accounting rule legal sample start (ended - start) stage bit hw
  simpa only [Nat.add_sub_of_le hle] using h

end PDROC.CalibratedRuntime
