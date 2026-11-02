module

public import Paid.PDCompute_SolverDenseRead_056

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem denseReadCell_trace (program : Program) (input : List Cell) (before : State) (base target pointer n k : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : target < headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (hlive : pointer ∈ before.live) (hfetch : FetchesCode program before.pc (denseReadCellCode target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (denseReadCellResult before base target pointer) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 105 ∧
      Header (denseReadCellResult before base target pointer) base (Function.update values target (before.heap pointer)) ∧
      (denseReadCellResult before base target pointer).register .fresh=.natural base ∧
      (denseReadCellResult before base target pointer).register .old=.natural (pointer+1) ∧
      (denseReadCellResult before base target pointer).pc=before.pc+6 ∧
      Frame before (denseReadCellResult before base target pointer) base n k ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let after := denseReadCellResult before base target pointer
  have run := denseReadCellCode_execute input before base target pointer hbase hpointer hlive
  obtain ⟨trace,hh,hl,hchain,ht,prefixes⟩ := linearExecute_trace_time program input (denseReadCellCode target)
    (denseReadCellCode_straight target) before after hfetch run
  have fields := denseReadCellResult_fields before base target pointer
  refine ⟨trace,hh,hl,hchain,ht,header.denseReadCell target pointer,
    fields.2.2.1.trans hbase,fields.2.2.2.1,fields.2.2.2.2.1,
    slotWrite_frame before after base target n k (before.heap pointer) inside fields.1 fields.2.1,?_⟩
  intro state member
  have split := List.dropLast_append_getLast? after (by rw [hl]; simp)
  rw [← split] at member
  rcases List.mem_append.mp member with proper|last
  · obtain ⟨count,bound,execute⟩ := prefixes state proper
    exact denseReadCellCode_prefix_memory input before state base target pointer values header inside hbase hpointer hlive
      count (Nat.le_of_lt bound) execute
  · have eq : state=after := by simpa only [List.mem_singleton] using last
    subst state
    exact denseReadCellCode_prefix_memory input before after base target pointer values header inside hbase hpointer hlive
      6 (le_refl _) run

end PDCompute.Solver
