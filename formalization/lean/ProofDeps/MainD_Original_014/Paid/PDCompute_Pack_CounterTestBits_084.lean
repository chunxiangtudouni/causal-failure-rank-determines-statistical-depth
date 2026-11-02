module
public import Paid.PDCompute_Pack_SlotBitTrace_064
public import Paid.PDCompute_Pack_CounterTest_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot loadSlotResult)

theorem counterTest_trace_safe (program : Program) (input : List Cell) (before : State)
    (base slot value zeroPC nonzeroPC budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (safe : SafeBits before budget) (addressBits : 1+natBits (base+slot) ≤ budget)
    (counter : natBits (before.pc+3) ≤ budget) (zeroBits : natBits zeroPC ≤ budget) (nonzeroBits : natBits nonzeroPC ≤ budget)
    (fetched : FetchesCode program before.pc (counterTestCode slot zeroPC nonzeroPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (counterTestResult before base slot value zeroPC nonzeroPC) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 75 ∧
      Header (counterTestResult before base slot value zeroPC nonzeroPC) base values ∧
      (counterTestResult before base slot value zeroPC nonzeroPC).register .fresh=.natural base ∧
      (counterTestResult before base slot value zeroPC nonzeroPC).output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  obtain ⟨loadTrace,hh,hl,hchain,ht,memory,bits⟩:=loadSlot_trace_safe program input before base slot budget .index values header inside hbase safe addressBits counter fetched.append_left
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
  have loadedSafe : SafeBits loaded budget:=bits loaded (List.mem_of_getLast? hl)
  have finalCounter : natBits (if value=0 then zeroPC else nonzeroPC) ≤ budget:=by split <;> assumption
  have afterSafe : SafeBits (counterTestResult before base slot value zeroPC nonzeroPC) budget:=loadedSafe.withPC _ finalCounter
  refine ⟨loadTrace++[_],?_,by simp,joined.1,by omega,?_,?_,rfl,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil loadTrace nonempty] using hh
  · exact header.loadSlot_preserves slot .index
  · simp [counterTestResult,loadSlotResult,hbase]
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact memory state earlier
    · have same : state=counterTestResult before base slot value zeroPC nonzeroPC := by simpa only [List.mem_singleton] using last
      subst state
      exact lastMemory

  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact bits state earlier
    · have same : state=counterTestResult before base slot value zeroPC nonzeroPC:=by simpa only [List.mem_singleton] using last
      subst state
      exact afterSafe

end PDCompute.Pack
