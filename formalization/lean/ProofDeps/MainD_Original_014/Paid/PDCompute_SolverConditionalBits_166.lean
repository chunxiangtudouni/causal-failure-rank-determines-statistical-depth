module

public import Paid.PDCompute_SolverCompareBits_164
public import Paid.PDCompute_SolverConditionalHeader_072

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Original strict comparison, ACTUAL branch, and actual selected
scalar block, with every prefix at the SAME complete-state budget. -/
theorem headerIfLess_trace_bits (program : Program) (input : List Cell) (origin : ℕ)
    (commands : List HeaderCommand) (values next : ℕ → Cell)
    (fetch : FetchesCode program origin (headerIfLessCode origin commands)) (before : State)
    (base n k budget : ℕ) (candidate best : ℚ) (valid : ∀ command∈commands,command.Valid)
    (evaluated : headerEval commands values=some next) (bounded : HeaderEvaluatedBits budget commands values)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hc : values 28=.rational candidate) (hb : values 24=.rational best) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (counter : natBits (origin+8+(headerCode commands).length)≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤135+165*(commands.length+1) ∧
      Header after base (if candidate<best then next else values) ∧ after.register .fresh=.natural base ∧
      after.pc=origin+8+(headerCode commands).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let compared:=minimumCompareResult before base candidate best
  let returned : State:={compared with pc:=if candidate<best then origin+8 else origin+8+(headerCode commands).length}
  have fields:=minimumCompareResult_fields before base candidate best
  have comparePC : natBits (before.pc+7)≤budget :=
    (natBits_mono (by rw [hpc]; omega : before.pc+7≤origin+8+(headerCode commands).length)).trans counter
  obtain ⟨trace,head,last,chain,cost,resources⟩:=minimumCompare_trace_bits program input before base budget values candidate best header fresh hc hb safe small addressBits
    comparePC (headerIfLess_compare_fetch program origin commands fetch before hpc)
  have compareMemory : ∀ state∈trace,HeaderMemory before state base := fun state member=>(resources state member).1
  have compareSafe : ∀ state∈trace,RootD27.Bits.SafeBits state budget := fun state member=>(resources state member).2
  have comparedSafe:=compareSafe compared (List.mem_of_getLast? last)
  have branchFetch : program[compared.pc]?=some (.branchZero .index (origin+8+(headerCode commands).length) (origin+8)) := by
    have position : compared.pc=origin+7 := fields.2.2.2.2.1.trans (congrArg (·+7) hpc)
    rw [position]
    exact fetch.append_left.append_right 0 (by change 0<1; decide)
  have actual : step program input compared=some returned := by
    unfold step
    rw [branchFetch]
    have indexValue : compared.register .index=.natural (if candidate<best then 1 else 0) := fields.2.2.2.1
    by_cases less : candidate<best <;> simp [Instruction.execute,indexValue,Cell.nat?,returned,less]
  have returnedCounter : natBits (if candidate<best then origin+8 else origin+8+(headerCode commands).length)≤budget := by
    split
    · exact (natBits_mono (by omega : origin+8≤origin+8+(headerCode commands).length)).trans counter
    · exact counter
  have returnedSafe : RootD27.Bits.SafeBits returned budget := comparedSafe.withPC _ returnedCounter
  have controlled:=chain_append_control program input trace compared returned chain last actual
  let branchTrace:=trace++[returned]
  have branchHead : branchTrace.head?=some before := by
    have nonempty : trace≠[] := by intro empty; rw [empty] at head; cases head
    simpa only [branchTrace,List.head?_append_of_ne_nil trace nonempty] using head
  have branchLast : branchTrace.getLast?=some returned := by simp [branchTrace]
  have branchTime : time program branchTrace≤135 := by have bound:=controlled.2; change time program (trace++[returned])≤135; omega
  have returnedMemory : HeaderMemory before returned base :=
    (HeaderMemory.trace_last compareMemory last).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  have branchMemory : ∀ state∈branchTrace,HeaderMemory before state base := appendTrace_memory trace before returned base compareMemory returnedMemory
  have branchSafe : ∀ state∈branchTrace,RootD27.Bits.SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with old|new
    · exact compareSafe state old
    · have equal:=List.mem_singleton.mp new
      subst state
      exact returnedSafe
  have returnedHeader : Header returned base values := minimumCompareResult_header before base values candidate best header
  have returnedBase : returned.register .fresh=.natural base := fields.2.2.1.trans fresh
  have returnedFrame : Frame before returned base n k := minimumCompareResult_frame before base n k candidate best
  have returnedOutput : returned.output=before.output := fields.2.2.2.2.2
  by_cases less : candidate<best
  · have returnedPC : returned.pc=origin+8 := by simp only [returned,ite_eq_left less]
    obtain ⟨body,after,bodyHead,bodyLast,bodyChain,bodyTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,bodyResources⟩:=
      headerCode_trace_bits commands program input returned base n k budget values next valid returnedHeader returnedBase evaluated returnedSafe bounded addressBits
        (by simpa only [returnedPC] using counter) (headerIfLess_body_fetch program origin commands fetch returned returnedPC)
    have joined:=joinTrace_spec program input branchTrace body before returned after 135 (165*(commands.length+1))
      branchHead branchLast bodyHead bodyLast controlled.1 bodyChain branchTime bodyTime
    refine ⟨joinTrace branchTrace body,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,?_,afterBase,?_,
      returnedFrame.trans afterFrame,afterOutput.trans returnedOutput,
      joinTrace_memory branchTrace body before returned base branchLast branchMemory (fun state member=>(bodyResources state member).1),
      PDCompute.Pack.joinTrace_invariant branchTrace body (fun state=>RootD27.Bits.SafeBits state budget) branchSafe
        (fun state member=>(bodyResources state member).2)⟩
    · simpa only [ite_eq_left less] using afterHeader
    · rw [afterPC,returnedPC]
  · refine ⟨branchTrace,returned,branchHead,branchLast,controlled.1,?_,?_,returnedBase,?_,returnedFrame,returnedOutput,branchMemory,branchSafe⟩
    · omega
    · simpa only [ite_eq_right less] using returnedHeader
    · simp only [returned,ite_eq_right less]

end PDCompute.Solver
