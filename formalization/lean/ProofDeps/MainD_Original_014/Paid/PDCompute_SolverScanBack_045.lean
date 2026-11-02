module

public import Paid.PDCompute_SolverScanAdvance_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem scanKernel_advance_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State) (hpc : before.pc=origin+95) :
    FetchesCode program before.pc scanAdvanceCode := by
  have layout : scanKernel mode origin=
      ((rangeCompareCode++[.branchZero .flag (origin+112) (origin+8)])++scanCandidateCode mode++
        minimumUpdateCode (origin+75))++scanAdvanceCode++[.jump origin] := by
    simp only [scanKernel,scanCandidateCode,scanEndpointCode,scanAdvanceCode,List.append_assoc]
  rw [layout] at hcode
  have fetched := hcode.middle
  change FetchesCode program (origin+95) scanAdvanceCode at fetched
  simpa only [hpc] using fetched

/-- The two real counters advance, then the original direct jump
returns to the very same scan test. No iteration is discharged as a
fictitious state self-step. -/
theorem scanKernel_advance_trace (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State)
    (base n k index pointer : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin+95) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hp : values 39=.natural pointer) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 270 ∧ Header after base (scanAdvanceValues values index pointer) ∧
      after.register .fresh=.natural base ∧ after.pc=origin ∧
      Frame before after base n k ∧ after.output=before.output := by
  obtain ⟨advanced,run,advancedHeader,advancedBase,advancedPC,advancedFrame,advancedOutput⟩ :=
    scanAdvanceCode_execute input before base n k index pointer values header hbase hi hp
  obtain ⟨trace,hh,hl,hchain,ht,_⟩ := linearExecute_trace_time program input scanAdvanceCode
    scanAdvanceCode_straight before advanced (scanKernel_advance_fetch mode program origin hcode before hpc) run
  have ht' : time program trace ≤ 255 := ht
  have returnedPC : advanced.pc=origin+111 := by rw [advancedPC,hpc]
  have fetch := scanKernel_back_fetch mode program origin hcode advanced returnedPC
  let after : State := {advanced with pc:=origin}
  have control : step program input advanced=some after := by
    unfold step
    rw [fetch]
    rfl
  have appended := chain_append_control program input trace advanced after hchain hl control
  have hn : trace ≠ [] := by intro he; simp only [he,List.head?_nil,reduceCtorEq] at hh
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,advancedHeader,
    advancedBase,rfl,advancedFrame,advancedOutput⟩
  · simpa only [List.head?_append_of_ne_nil trace hn] using hh
  · omega

end PDCompute.Solver
