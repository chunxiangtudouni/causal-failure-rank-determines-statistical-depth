module

public import Paid.PDCompute_SolverDenseWriteBlock_077
public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (loadSlot loadSlotResult)
open PDMenu.ComputeFrame

theorem RegionMemory.of_unchanged {before after : State} (region : Finset ℕ)
    (heap : after.heap=before.heap) (live : after.live=before.live) (output : after.output=before.output) :
    RegionMemory before after region := by
  refine ⟨fun address _ => congrFun heap address,?_,?_,output⟩
  · rw [live]
    exact Finset.subset_union_left
  · simpa only [live] using Finset.Subset.refl before.live

/-- A true read leaves storage unchanged at EVERY state, so its
footprint can be placed in any actual subsequent write region. -/
theorem Header.loadSlot_trace_region {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (program : Program) (input : List Cell)
    (slot : ℕ) (target : Register) (inside : slot < headerWords) (hbase : before.register .fresh=.natural base)
    (region : Finset ℕ) (fetch : FetchesCode program before.pc (loadSlot slot target)) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some (loadSlotResult before base slot target) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 60 ∧ ∀ state ∈ trace,RegionMemory before state region := by
  have run:=(header.loadSlot_execute input slot target inside hbase).1
  obtain ⟨trace,head,last,chain,bound,prefixes⟩:=linearExecute_trace_time program input (loadSlot slot target)
    (loadSlot_straight slot target) before _ fetch run
  refine ⟨trace,head,last,chain,bound,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (loadSlotResult before base slot target) (by rw [last]; simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|final
  · obtain ⟨count,countBound,execute⟩:=prefixes state proper
    have memory:=loadSlot_prefix_memory input before state base slot target hbase (header.live slot inside)
      count (Nat.le_of_lt countBound) execute
    exact RegionMemory.of_unchanged region memory.1 memory.2.1 memory.2.2
  · have same : state=loadSlotResult before base slot target := by simpa only [List.mem_singleton] using final
    subst state
    exact RegionMemory.of_unchanged region rfl rfl rfl

end PDCompute.Solver
