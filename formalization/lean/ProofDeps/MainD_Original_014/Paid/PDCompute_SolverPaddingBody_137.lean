module

public import Paid.PDCompute_SolverPaddingWrites_136
public import Paid.PDCompute_SolverBaseRowTrace_009
public import Paid.PDCompute_SolverLinearPC_121

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDMenu.ComputeFrame

/-- SAME original padding body and backedge, with exact recursive-result
state and EVERY-state Header-region/bit/PC properties on ONE trace. -/
theorem baseRowBody_trace_resources (program : Program) (input : List Cell) (origin : ℕ)
    (fetch : FetchesCode program origin (baseRowCode origin)) (before : State) (base pointer index budget : ℕ)
    (hpc : before.pc=origin+2) (address : before.register .address=.natural pointer)
    (current : before.register .index=.natural index) (one : before.register .flag=.natural 1)
    (safe : RootD27.Bits.SafeBits before budget) (lower : base ≤ pointer) (room : pointer+6 ≤ base+headerWords)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (zeroBits : (.rational 0 : Cell).bits ≤ budget)
    (pcBits : natBits (origin+18) ≤ budget) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some {baseRowWritesResult before pointer index with pc:=origin+1} ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 255 ∧
      ∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits state budget ∧
        origin ≤ state.pc ∧ state.pc < origin+18 := by
  let written:=baseRowWritesResult before pointer index
  let returned : State:={written with pc:=origin+1}
  have execute:=baseRowWrites_execute input before pointer index address current one
  obtain ⟨writes,head,last,chain,timeBound,prefixes,pcRange⟩:=linearExecute_trace_closedPC program input baseRowWrites
    baseRowWrites_straight before written (baseRow_body_fetch program origin fetch before hpc) execute
  have writesPC : natBits (before.pc+15) ≤ budget := (natBits_mono (by omega : before.pc+15 ≤ origin+18)).trans pcBits
  have resources : ∀ state ∈ writes,RegionMemory before state (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits state budget := by
    intro state member
    have split:=List.dropLast_append_getLast? written (by rw [last]; simp)
    have represented : ∃ count ≤ baseRowWrites.length,PDLower.CalibrationCompute.linearExecute input (baseRowWrites.take count) before=some state := by
      rw [← split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨count,bound,run⟩:=prefixes state proper
        exact ⟨count,Nat.le_of_lt bound,run⟩
      · have same : state=written := List.mem_singleton.mp terminal
        subst state
        exact ⟨baseRowWrites.length,le_refl _,by simpa only [List.take_length] using execute⟩
    obtain ⟨count,bound,run⟩:=represented
    exact baseRowWrites_prefix_resources input before state base pointer index budget count address current one safe lower room
      addressBits zeroBits writesPC bound run
  have jumpFetch : program[written.pc]?=some (.jump (origin+1)) := by
    have instruction : (baseRowCode origin)[17]?=some (.jump (origin+1)) := rfl
    have located:=(fetch 17 (by rw [baseRowCode_length]; omega)).trans instruction
    change program[before.pc+15]?=some (.jump (origin+1))
    have position : before.pc+15=origin+17 := by omega
    rw [position]
    exact located
  have control : step program input written=some returned := by unfold step; rw [jumpFetch]; rfl
  have appended:=chain_append_control program input writes written returned chain last control
  have writtenResources:=resources written (List.mem_of_getLast? last)
  have returnedSafe : RootD27.Bits.SafeBits returned budget :=
    writtenResources.2.withPC (origin+1) ((natBits_mono (by omega : origin+1 ≤ origin+18)).trans pcBits)
  have nonempty : writes ≠ [] := by intro empty; simp only [empty,List.head?_nil,reduceCtorEq] at head
  refine ⟨writes++[returned],?_,by simp [returned,written],appended.1,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using head
  · have bound : time program writes ≤ 240 := by simpa only [baseRowWrites_length] using timeBound
    have total:=appended.2
    omega
  · intro state member
    rcases List.mem_append.mp member with proper|terminal
    · have interval:=pcRange state proper
      rw [baseRowWrites_length] at interval
      exact ⟨(resources state proper).1,(resources state proper).2,by omega⟩
    · have same : state=returned := List.mem_singleton.mp terminal
      subst state
      exact ⟨writtenResources.1,returnedSafe,by change origin ≤ origin+1 ∧ origin+1 < origin+18; omega⟩

end PDCompute.Solver
