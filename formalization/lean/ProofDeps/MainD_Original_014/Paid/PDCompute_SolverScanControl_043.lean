module

public import Paid.PDCompute_SolverScanFetch_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem scanKernel_range_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State) (hpc : before.pc=origin) :
    FetchesCode program before.pc rangeCompareCode := by
  have layout : scanKernel mode origin=rangeCompareCode++
      ([.branchZero .flag (origin+112) (origin+8)]++
        scanCandidateCode mode++minimumUpdateCode (origin+75)++
          addNatSlot 25 1++addNatSlot 39 2++[.jump origin]) := by
    simp only [scanKernel,scanCandidateCode,scanEndpointCode,List.append_assoc]
  rw [layout] at hcode
  simpa only [hpc] using hcode.append_left

/-- Both real range-test outcomes. The false branch really jumps past
the entire112-instruction loop; the true branch enters its candidate block. -/
theorem scanKernel_test_trace (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State)
    (base n k index last : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hlast : values 6=.natural last) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 135 ∧ Header after base values ∧
      after.register .fresh=.natural base ∧
      after.pc=(if index ≤ last then origin+8 else origin+112) ∧
      Frame before after base n k ∧ after.output=before.output := by
  let compared := rangeCompareResult before base index last
  let after : State := {compared with pc:=if index ≤ last then origin+8 else origin+112}
  have fields := rangeCompareResult_fields before base index last
  obtain ⟨trace,hh,hl,hchain,ht,_⟩ := linearExecute_trace_time program input rangeCompareCode
    rangeCompareCode_straight before compared (scanKernel_range_fetch mode program origin hcode before hpc)
    (rangeCompareCode_execute input before base values index last header hbase hi hlast)
  have ht' : time program trace ≤ 120 := ht
  have fetch : program[compared.pc]?=some (.branchZero .flag (origin+112) (origin+8)) := by
    have hp : compared.pc=origin+7 := fields.2.2.2.2.1.trans (congrArg (·+7) hpc)
    rw [hp]
    exact (hcode 7 (by rw [scanKernel_length]; omega)).trans (by rfl)
  have control : step program input compared=some after := by
    unfold step
    rw [fetch]
    have flag : compared.register .flag=.natural (if index ≤ last then 1 else 0) := fields.2.2.2.1
    by_cases inside : index ≤ last <;>
      simp [Instruction.execute,flag,Cell.nat?,inside,after]
  have appended := chain_append_control program input trace compared after hchain hl control
  have hn : trace ≠ [] := by intro he; simp only [he,List.head?_nil,reduceCtorEq] at hh
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,?_,fields.2.2.1.trans hbase,rfl,?_,fields.2.2.2.2.2⟩
  · simpa only [List.head?_append_of_ne_nil trace hn] using hh
  · omega
  · apply header.frame
    · intro slot inside
      exact congrFun fields.1 (base+slot)
    · intro cell member
      change cell ∈ compared.live
      rw [fields.2.1]
      exact member
  · exact ⟨fun address _ => congrFun fields.1 address,
      fun address _ => by change address ∈ compared.live ↔ address ∈ before.live; rw [fields.2.1]⟩

end PDCompute.Solver
