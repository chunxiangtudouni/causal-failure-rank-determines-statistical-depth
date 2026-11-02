module

public import Paid.PDROC_EndpointOperands_Loop_011
public import Paid.PDCompute_Pack_TraceInvariant_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- The original advance literal prefixes preserve exact old live/output
and only modify the real header. This includes the final counter store;
it does not synchronize slot7 and slot8 before their separate writes. -/
theorem advance_prefix_memory (P : Parameters) (m : ℕ) (input : List Cell)
    (before : State) (base : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (power : values 7 = .rational (powerRecurrence P.certificate.odds m))
    (odds : values 6 = .rational P.certificate.odds) (row : values 8 = .natural m) :
    ∀ count ≤ advanceCode.length, ∀ state,
      linearExecute input (advanceCode.take count) before = some state → HeaderMemory before state base := by
  let next := Function.update values 7 (.rational (powerRecurrence P.certificate.odds (m + 1)))
  have valid : ∀ command ∈ [HeaderCommand.rational .multiply 7 6 7], command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    norm_num [HeaderCommand.Valid, headerWords]
  have evaluated : headerEval [.rational .multiply 7 6 7] values = some next := by
    simp [headerEval, HeaderCommand.eval, Cell.rat?, RatOp.eval, power, odds, next, powerRecurrence]
  obtain ⟨middle, run, middleHeader, middleFresh, _middlePC, _frame, _output⟩ :=
    headerCode_realize [.rational .multiply 7 6 7] input before base 0 0 values next
      valid header fresh evaluated
  have firstMemory := headerCode_memory [.rational .multiply 7 6 7] input before middle base values next
    valid header fresh evaluated run
  have nextRow : next 8 = .natural m := by simp [next, row]
  have value := (middleHeader.value 8 (by decide)).trans nextRow
  have incrementRun := incrementRow_execute input middle base m middleFresh (middleHeader.live 8 (by decide)) value
  have laterPrefixes : ∀ count ≤ incrementRowCode.length, ∀ state,
      linearExecute input (incrementRowCode.take count) middle = some state → HeaderMemory before state base := by
    intro count bound state actual
    change count ≤ 8 at bound
    by_cases final : count = 8
    · have full : incrementRowCode.take 8 = incrementRowCode := rfl
      rw [final, full, incrementRun] at actual
      have same := Option.some.inj actual
      subst state
      exact firstMemory.trans (incrementRow_memory middle base m next middleHeader)
    · have unchanged := incrementRow_prefix input middle state base m middleFresh
        (middleHeader.live 8 (by decide)) value count (by omega) actual
      exact firstMemory.trans (HeaderMemory.of_unchanged base unchanged.1 unchanged.2.1 unchanged.2.2)
  rw [advanceCode_split]
  exact PDCompute.Pack.invariant_prefix_append input (headerCode [.rational .multiply 7 6 7]) incrementRowCode
    before middle run (fun state => HeaderMemory before state base)
    (fun count bound state actual => headerCode_prefix_memory [.rational .multiply 7 6 7] input before state base values next
      valid header fresh evaluated count bound actual) laterPrefixes

end PDROC.EndpointOperands.Loop
