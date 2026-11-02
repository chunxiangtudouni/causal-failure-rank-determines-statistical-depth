module

public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem minimumUpdateCode_trace_memory (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (minimumUpdateCode origin)) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (candidate best : ℚ)
    (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hc : values 28=.rational candidate) (hb : values 24=.rational best) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 630 ∧
      Header after base (if candidate < best then minimumUpdateValues values else values) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+20 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let compared := minimumCompareResult before base candidate best
  let returned : State := {compared with pc:=if candidate < best then origin+8 else origin+20}
  have fields := minimumCompareResult_fields before base candidate best
  obtain ⟨trace,hh,hl,hchain,ht,traceMemory⟩ := linearExecute_trace_memory program input minimumCompareCode
    minimumCompareCode_straight before compared base (minimumUpdate_compare_fetch program origin hcode before hpc)
    (minimumCompareCode_execute input before base values candidate best header hbase hc hb)
    (fun count bound state execute => minimumCompareCode_prefix_memory input before state base values candidate best
      header hbase hc hb count bound execute)
  have ht' : time program trace ≤ 120 := ht
  have hj : program[compared.pc]?=some (.branchZero .index (origin+20) (origin+8)) := by
    have he : compared.pc=origin+7 := fields.2.2.2.2.1.trans (congrArg (·+7) hpc)
    rw [he]
    exact (hcode 7 (by rw [minimumUpdateCode_length]; omega)).trans (by rfl)
  have hs : step program input compared=some returned := by
    unfold step
    rw [hj]
    have hi : compared.register .index=.natural (if candidate < best then 1 else 0) := fields.2.2.2.1
    by_cases less : candidate < best <;> simp [Instruction.execute,hi,Cell.nat?,returned,less]
  have controlled := chain_append_control program input trace compared returned hchain hl hs
  let branchTrace := trace++[returned]
  have hbh : branchTrace.head?=some before := by
    have hn : trace ≠ [] := by intro he; simp only [he,List.head?_nil,reduceCtorEq] at hh
    simpa only [branchTrace,List.head?_append_of_ne_nil trace hn] using hh
  have hbl : branchTrace.getLast?=some returned := by simp [branchTrace]
  have hbt : time program branchTrace ≤ 135 := by
    change time program (trace++[returned]) ≤ 135
    have bound := controlled.2
    omega
  have returnedMemory : HeaderMemory before returned base :=
    (HeaderMemory.trace_last traceMemory hl).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  have branchMemory : ∀ state ∈ branchTrace, HeaderMemory before state base :=
    appendTrace_memory trace before returned base traceMemory returnedMemory
  have hrh : Header returned base values := minimumCompareResult_header before base values candidate best header
  have hrb : returned.register .fresh=.natural base := fields.2.2.1.trans hbase
  have hrf : Frame before returned base n k := minimumCompareResult_frame before base n k candidate best
  have hro : returned.output=before.output := fields.2.2.2.2.2
  by_cases less : candidate < best
  · have hrpc : returned.pc=origin+8 := by simp only [returned,ite_eq_left less]
    obtain ⟨body,after,bodyHead,bodyLast,bodyChain,bodyTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,bodyMemory⟩ :=
      headerCode_trace_memory minimumUpdateCommands program input returned base n k values _
        minimumUpdateCommands_valid hrh hrb (minimumUpdateCommands_eval values)
        (minimumUpdate_body_fetch program origin hcode returned hrpc)
    have joined := joinTrace_spec program input branchTrace body before returned after 135 495
      hbh hbl bodyHead bodyLast controlled.1 bodyChain hbt bodyTime
    refine ⟨joinTrace branchTrace body,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,?_,
      afterBase,?_,hrf.trans afterFrame,afterOutput.trans hro,
      joinTrace_memory branchTrace body before returned base hbl branchMemory bodyMemory⟩
    · simpa only [ite_eq_left less] using afterHeader
    · have codeLength : (headerCode minimumUpdateCommands).length=12 := rfl
      rw [afterPC,hrpc,codeLength]
  · refine ⟨branchTrace,returned,hbh,hbl,controlled.1,hbt.trans (by decide),?_,hrb,?_,hrf,hro,branchMemory⟩
    · simpa only [ite_eq_right less] using hrh
    · simp only [returned,ite_eq_right less]

end PDCompute.Solver
