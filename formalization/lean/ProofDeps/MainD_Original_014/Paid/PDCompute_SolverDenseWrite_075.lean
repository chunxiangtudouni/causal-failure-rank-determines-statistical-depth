module

public import Paid.PDCompute_SolverDenseReadTrace_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot)
open PDMenu.ComputeFrame

/-- Actual inverse streaming move. The input is a live scalar header
cell; the output pointer is the original old register. -/
def denseWriteCellCode (source : ℕ) : List Instruction :=
  loadSlot source .total++[.store .old .total,.constant .flag (.natural 1),.natOp .add .old .old .flag]

def denseWriteCellResult (before : State) (base source pointer : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update
      (Function.update before.register .address (.natural (base+source))) .total (before.heap (base+source)))
      .flag (.natural 1)) .old (.natural (pointer+1))
    heap:=Function.update before.heap pointer (before.heap (base+source))
    live:=insert pointer before.live
    pc:=before.pc+6}

def CellWriteMemory (before after : State) (pointer : ℕ) : Prop :=
  (∀ address, address ≠ pointer → after.heap address=before.heap address) ∧
  after.live ⊆ insert pointer before.live ∧ before.live ⊆ after.live ∧ after.output=before.output

theorem denseWriteCellCode_length (source : ℕ) : (denseWriteCellCode source).length=6 := rfl

theorem denseWriteCellCode_straight (source : ℕ) : StraightCode (denseWriteCellCode source) := by
  intro instruction member
  simp only [denseWriteCellCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h|h) <;> subst instruction <;> trivial

theorem denseWriteCellCode_execute (input : List Cell) (before : State) (base source pointer : ℕ)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (hlive : base+source ∈ before.live) :
    linearExecute input (denseWriteCellCode source) before=some (denseWriteCellResult before base source pointer) := by
  simp [denseWriteCellCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,hpointer,hlive,denseWriteCellResult,Nat.add_assoc]

theorem denseWriteCellCode_prefix_memory (input : List Cell) (before after : State) (base source pointer : ℕ)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (hlive : base+source ∈ before.live) (count : ℕ) (hcount : count ≤ 6)
    (execute : linearExecute input ((denseWriteCellCode source).take count) before=some after) :
    CellWriteMemory before after pointer := by
  interval_cases count <;>
    simp [denseWriteCellCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      hbase,hpointer,hlive] at execute <;> subst after
  all_goals
    refine ⟨?_,?_,?_,rfl⟩
    · intro address different
      simp only [Function.update_of_ne different]
    · first | exact Finset.subset_insert _ _ | exact Finset.Subset.refl _
    · first | exact Finset.Subset.refl _ | exact Finset.subset_insert _ _

theorem CellWriteMemory.frame {before after : State} {pointer base n k : ℕ}
    (memory : CellWriteMemory before after pointer) (inside : pointer ∈ workspace base n k) :
    Frame before after base n k := by
  constructor
  · intro address outside
    apply memory.1 address
    intro same
    exact outside (same.symm ▸ inside)
  · intro address outside
    constructor
    · intro live
      rcases Finset.mem_insert.mp (memory.2.1 live) with same|old
      · exact False.elim (outside (same.symm ▸ inside))
      · exact old
    · intro live
      exact memory.2.2.1 live

theorem denseWriteCellResult_header (before : State) (base source pointer : ℕ) (values : ℕ → Cell)
    (header : Header before base values)
    (outside : pointer < base ∨ base+headerWords ≤ pointer) :
    Header (denseWriteCellResult before base source pointer) base values := by
  apply header.frame
  · intro slot bound
    change Function.update before.heap pointer (before.heap (base+source)) (base+slot)=before.heap (base+slot)
    rw [Function.update_of_ne (by rcases outside with low|high <;> omega)]
  · exact Finset.subset_insert _ _

theorem denseWriteCell_trace (program : Program) (input : List Cell) (before : State)
    (base source pointer : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (inside : source < headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (fetched : FetchesCode program before.pc (denseWriteCellCode source)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (denseWriteCellResult before base source pointer) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 105 ∧ ∀ state ∈ trace, CellWriteMemory before state pointer := by
  have run := denseWriteCellCode_execute input before base source pointer hbase hpointer (header.live source inside)
  obtain ⟨trace,hh,hl,hchain,ht,prefixes⟩ := linearExecute_trace_time program input (denseWriteCellCode source)
    (denseWriteCellCode_straight source) before _ fetched run
  refine ⟨trace,hh,hl,hchain,ht,?_⟩
  intro state member
  have split := List.dropLast_append_getLast? (denseWriteCellResult before base source pointer) (by rw [hl]; simp)
  rw [← split] at member
  rcases List.mem_append.mp member with proper|last
  · obtain ⟨count,bound,execute⟩ := prefixes state proper
    exact denseWriteCellCode_prefix_memory input before state base source pointer hbase hpointer (header.live source inside)
      count (Nat.le_of_lt bound) execute
  · have same : state=denseWriteCellResult before base source pointer := by simpa only [List.mem_singleton] using last
    subst state
    exact denseWriteCellCode_prefix_memory input before _ base source pointer hbase hpointer (header.live source inside)
      6 (le_refl _) run

end PDCompute.Solver
