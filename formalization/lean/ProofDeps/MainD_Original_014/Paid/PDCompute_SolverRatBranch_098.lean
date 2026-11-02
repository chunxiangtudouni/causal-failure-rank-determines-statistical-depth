module

public import Paid.PDCompute_SolverRatCompare_097

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def rationalBranchCode (comparison : Comparison) (left right whenZero whenNonzero : ℕ) : List Instruction :=
  rationalCompareCode comparison left right++[.branchZero .flag whenZero whenNonzero]

theorem rationalBranch_trace_memory (program : Program) (input : List Cell) (before : State)
    (base n k left right whenZero whenNonzero : ℕ) (x y : ℚ) (comparison : Comparison) (values : ℕ → Cell)
    (header : Header before base values) (hl : left < headerWords) (hr : right < headerWords)
    (hx : values left=.rational x) (hy : values right=.rational y) (hbase : before.register .fresh=.natural base)
    (fetch : FetchesCode program before.pc (rationalBranchCode comparison left right whenZero whenNonzero)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 135 ∧ Header after base values ∧ after.register .fresh=.natural base ∧
      after.pc=(if comparison.rat x y then whenNonzero else whenZero) ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,HeaderMemory before state base := by
  let compared:=PDROC.D27Prepare.Program.comparisonResult before base left right (comparison.rat x y)
  let after : State:={compared with pc:=if comparison.rat x y then whenNonzero else whenZero}
  have compareFetch : FetchesCode program before.pc (rationalCompareCode comparison left right) := fetch.append_left
  obtain ⟨trace,head,last,chain,bound,memory⟩:=
    rationalCompare_trace_memory program input before base left right x y comparison values header hl hr hx hy hbase compareFetch
  have fields:=PDROC.D27Prepare.Program.comparisonResult_fields before base left right (comparison.rat x y)
  have controlFetch : program[compared.pc]?=some (.branchZero .flag whenZero whenNonzero) := by
    rw [fields.2.2.2.2.1]
    have branchFetch:=fetch.append_right
    exact branchFetch 0 (by change 0 < 1; decide)
  have control : step program input compared=some after := by
    unfold step
    rw [controlFetch]
    have flagValue : compared.register .flag=.natural (if comparison.rat x y then 1 else 0) := fields.2.2.2.1
    cases boolean : comparison.rat x y <;> simp [Instruction.execute,flagValue,Cell.nat?,after,boolean]
  have appended:=chain_append_control program input trace compared after chain last control
  have nonempty : trace ≠ [] := by intro empty; simp only [empty,List.head?_nil,reduceCtorEq] at head
  have afterMemory : HeaderMemory before after base :=
    (HeaderMemory.trace_last memory last).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,header,hbase,rfl,
    ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,rfl,appendTrace_memory trace before after base memory afterMemory⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using head
  · have cost:=appended.2
    omega

end PDCompute.Solver
