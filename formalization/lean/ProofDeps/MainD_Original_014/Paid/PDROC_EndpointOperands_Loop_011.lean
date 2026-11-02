module

public import Paid.PDROC_EndpointOperands_Loop_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append)

/-- Pure execution adapter for the ORIGINAL advance. The two existing
functional producers are reused; no trace is selected here. -/
theorem advance_execute_spec (P : Parameters) (m : ℕ) (input : List Cell)
    (before : State) (base : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (power : values 7 = .rational (powerRecurrence P.certificate.odds m))
    (odds : values 6 = .rational P.certificate.odds) (row : values 8 = .natural m) :
    ∃ after, linearExecute input advanceCode before = some after ∧
      Header after base (Function.update
        (Function.update values 7 (.rational (powerRecurrence P.certificate.odds (m + 1)))) 8 (.natural (m + 1))) ∧
      after.register .fresh = .natural base ∧ after.pc = before.pc + 18 ∧ HeaderMemory before after base := by
  let next := Function.update values 7 (.rational (powerRecurrence P.certificate.odds (m + 1)))
  have valid : ∀ command ∈ [HeaderCommand.rational .multiply 7 6 7], command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    norm_num [HeaderCommand.Valid, headerWords]
  have evaluated : headerEval [.rational .multiply 7 6 7] values = some next := by
    simp [headerEval, HeaderCommand.eval, Cell.rat?, RatOp.eval, power, odds, next, powerRecurrence]
  obtain ⟨middle, scalarRun, scalarHeader, scalarFresh, scalarPC, _frame, _output⟩ :=
    headerCode_realize [.rational .multiply 7 6 7] input before base 0 0 values next
      valid header fresh evaluated
  have scalarMemory := headerCode_memory [.rational .multiply 7 6 7] input before middle base values next
    valid header fresh evaluated scalarRun
  have nextRow : next 8 = .natural m := by simp [next, row]
  have incrementRun := incrementRow_execute input middle base m scalarFresh
    (scalarHeader.live 8 (by decide)) ((scalarHeader.value 8 (by decide)).trans nextRow)
  refine ⟨incrementRowResult middle base m, ?_, incrementRow_header middle base m next scalarHeader, ?_, ?_,
    scalarMemory.trans (incrementRow_memory middle base m next scalarHeader)⟩
  · rw [advanceCode_split, linearExecute_append, scalarRun, Option.bind_some]
    exact incrementRun
  · exact (incrementRow_fresh middle base m).trans scalarFresh
  · rw [incrementRow_pc, scalarPC]
    rfl

end PDROC.EndpointOperands.Loop
