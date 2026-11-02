module
public import Paid.PDCompute_Pack_Fragments_018
public import Paid.PDCompute_SolverSmallTraceMemory_061
public import Paid.PDCompute_SolverMemoryJoin_062
public import Paid.PDMenu_ComputeFrame_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot loadSlotResult)

def counterTestCode (slot zeroPC nonzeroPC : ℕ) : List Instruction :=
  loadSlot slot .index++[.branchZero .index zeroPC nonzeroPC]
def counterTestResult (before : State) (base slot value zeroPC nonzeroPC : ℕ) : State :=
  {loadSlotResult before base slot .index with pc:=if value=0 then zeroPC else nonzeroPC}

/-- The loop guard fetches the actual live counter and executes a real
conditional; its outcome is determined by that counter alone. -/
theorem counterTest_trace (program : Program) (input : List Cell) (before : State)
    (base slot value zeroPC nonzeroPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (fetched : FetchesCode program before.pc (counterTestCode slot zeroPC nonzeroPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (counterTestResult before base slot value zeroPC nonzeroPC) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 75 ∧
      Header (counterTestResult before base slot value zeroPC nonzeroPC) base values ∧
      (counterTestResult before base slot value zeroPC nonzeroPC).register .fresh=.natural base ∧
      (counterTestResult before base slot value zeroPC nonzeroPC).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  obtain ⟨loadTrace,hh,hl,hchain,ht,memory⟩:=header.loadSlot_trace_memory program input slot .index inside hbase fetched.append_left
  let loaded:=loadSlotResult before base slot .index
  have loadedPC : loaded.pc=before.pc+3 := rfl
  have loadedValue : loaded.register .index=.natural value :=
    (header.loadSlot_execute input slot .index inside hbase).2.trans hvalue
  have branchFetch : program[loaded.pc]?=some (.branchZero .index zeroPC nonzeroPC) := by
    rw [loadedPC]
    exact (fetched 3 (by change 3<4;decide)).trans (by rfl)
  have branch : step program input loaded=some (counterTestResult before base slot value zeroPC nonzeroPC) := by
    simp [step,branchFetch,Instruction.execute,loadedValue,Cell.nat?,counterTestResult,loaded]
  have joined:=chain_append_control program input loadTrace loaded _ hchain hl branch
  have nonempty : loadTrace≠[] := by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at hh
  have lastMemory:=HeaderMemory.trace_last memory hl
  refine ⟨loadTrace++[_],?_,by simp,joined.1,by omega,?_,?_,rfl,?_⟩
  · simpa only [List.head?_append_of_ne_nil loadTrace nonempty] using hh
  · exact header.loadSlot_preserves slot .index
  · simp [counterTestResult,loadSlotResult,hbase]
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact memory state earlier
    · have same : state=counterTestResult before base slot value zeroPC nonzeroPC := by simpa only [List.mem_singleton] using last
      subst state
      exact lastMemory

end PDCompute.Pack
