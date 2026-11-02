module

public import Paid.PDCompute_SolverBaseRowHeap_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem baseRow_region_inside (base n k : ℕ) :
    ∀ offset < 6*(k+1), tableBase base+offset ∈ workspace base n k := by
  intro offset hoff
  have hcount : k+1 ≤ entryCount n k := by unfold entryCount; nlinarith
  apply Finset.mem_image.mpr
  refine ⟨headerWords+offset,Finset.mem_range.mpr ?_,?_⟩
  · unfold workspaceSize entryWords resultCapacity
    omega
  · unfold tableBase
    omega

private theorem initializationCost (k : ℕ) : 30+(300*(k+1)+30) ≤ 400*(k+1) := by omega

/-- The fixed original-ISA initialization phase really writes every base
row entry, returns at its actual following PC, preserves caller output and
all heap/live cells outside the actual solver workspace, and has the
source's linear genuine primitive cost. This is a phase, not full D27. -/
theorem initializeBaseRow (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (baseRowCode origin)) (before : State) (base n k : ℕ)
    (hpc : before.pc=origin) (haddress : before.register .address=.natural (tableBase base))
    (hcount : before.register .index=.natural (k+1)) :
    ∃ trace : List State, ∃ final : State,
      trace.head?=some before ∧ trace.getLast?=some final ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 400*(k+1) ∧ final.pc=origin+18 ∧
      final.register .address=.natural (tableBase base+6*(k+1)) ∧ final.register .index=.natural 0 ∧
      (∀ column, column ≤ k → HeapList final (cellBase base k 0 column) (denseEncodeEntry finishEntry)) ∧
      Frame before final base n k ∧ final.output=before.output := by
  let start := ({before with pc:=origin+1}).set .flag (.natural 1)
  let final := baseRowLoopResult origin (k+1) start (tableBase base)
  have hf : program[before.pc]?=some (.constant .flag (.natural 1)) := by
    rw [hpc]
    have hh : (baseRowCode origin)[0]?=some (.constant .flag (.natural 1)) := rfl
    simpa only [Nat.add_zero] using (hcode 0 (by rw [baseRowCode_length]; omega)).trans hh
  have hs : step program input before=some start := by
    unfold step
    rw [hf]
    simp [Instruction.execute,start,hpc]
  have hstartA : start.register .address=.natural (tableBase base) := by simp [start,State.set,haddress]
  have hstartI : start.register .index=.natural (k+1) := by simp [start,State.set,hcount]
  have hstartF : start.register .flag=.natural 1 := by simp [start,State.set]
  obtain ⟨loop,hh,hl,hchain,htime⟩ := baseRowLoop_trace program input origin hcode (k+1) start (tableBase base)
    rfl hstartA hstartI hstartF
  have hjoined := joinTrace_spec program input [before,start] loop before start final 30 (300*(k+1)+30)
    rfl rfl hh hl (List.isChain_pair.mpr hs) hchain (by simpa using time_le_length program [before,start]) htime
  refine ⟨joinTrace [before,start] loop,final,hjoined.1,hjoined.2.1,hjoined.2.2.1,?_,
    baseRowLoopResult_pc _ _ _ _,baseRowLoopResult_address _ _ _ _ hstartA,
    baseRowLoopResult_index _ _ _ _ hstartI,?_,?_,baseRowLoopResult_output _ _ _ _⟩
  · exact hjoined.2.2.2.trans (initializationCost k)
  · intro column hcolumn
    have h := baseRowLoopResult_entries origin (k+1) start (tableBase base) column (by omega)
    simpa only [cellBase,entryWords,Nat.zero_mul,Nat.zero_add] using h
  · exact baseRowLoopResult_frame origin (k+1) start (tableBase base) base n k (baseRow_region_inside base n k)

end PDCompute.Solver
