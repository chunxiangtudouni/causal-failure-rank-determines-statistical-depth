module

public import Paid.PDCompute_CoreEmit_Caller_011
public import Paid.PDCompute_Pack_TraceInvariant_055
public import Paid.PDCompute_Pack_InstructionBits_058
public import Paid.PDLower_CalibrationCompute_IOBits_088
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList linearExecute)
open PDROC.CalibrationRow.Operand
open PDROC.DataBits

/-- Carry arbitrary dirty old values. Only actual newly assigned naturals
use the independently paid cap; the budget itself is unchanged. -/
private theorem natural_frame_safe (before after : State) (cap budget : ℕ)
    (safe : RootD27.Bits.SafeBits before budget) (capBits : 1+natBits cap≤budget)
    (registers : ∀ target,after.register target=before.register target ∨
      ∃ value≤cap,after.register target=.natural value)
    (heap : after.heap=before.heap) (live : after.live=before.live) (output : after.output=before.output)
    (counter : natBits after.pc≤budget) : RootD27.Bits.SafeBits after budget := by
  apply RootD27.Bits.SafeBits.of_fields
  · intro target
    rcases registers target with old|⟨value,bounded,actual⟩
    · rw [old]
      exact safe.register target
    · rw [actual]
      change 1+natBits value≤budget
      exact (Nat.add_le_add_left (natBits_mono bounded) 1).trans capBits
  · intro address inside
    rw [live] at inside
    exact safe.address address inside
  · intro address inside
    rw [live] at inside
    rw [heap]
    exact safe.heap address inside
  · intro value inside
    rw [output] at inside
    exact safe.output value inside
  · exact counter

/-- The real21-op pointer producer never doubles callerB. The actual
buffer end pays all new addresses/products/constants and true count. -/
theorem pointer_prefix_safe (input : List Cell) (before : State) (n k M count cap budget : ℕ) (upper : Bool)
    (dimensions : PreparedDimensions before n k M)
    (storedLength : HeapList before (lengthSlot upper) [.natural count])
    (safe : RootD27.Bits.SafeBits before budget)
    (endBound : bufferBase n k M upper+count≤cap) (capBits : 1+natBits cap≤budget)
    (counter : natBits (before.pc+21)≤budget) : PrefixSafe input (pointerCode upper) before budget := by
  apply PrefixSafe.of_bounded
  intro taken bound after executed
  have inside : taken≤21:=by simpa only [pointer_length] using bound
  obtain ⟨nLive,nValue⟩:=singleton_fields before 0 (.natural n) dimensions.1
  obtain ⟨kLive,kValue⟩:=singleton_fields before 1 (.natural k) dimensions.2.1
  obtain ⟨MLive,MValue⟩:=singleton_fields before 7 (.natural M) dimensions.2.2
  obtain ⟨countLive,countValue⟩:=singleton_fields before (lengthSlot upper) (.natural count) storedLength
  have nProduct:=Nat.mul_le_mul_left (n+1) (by omega : 1≤k+1)
  simp only [Nat.mul_one] at nProduct
  have kProduct:=Nat.mul_le_mul_right (k+1) (by omega : 1≤n+1)
  simp only [Nat.one_mul] at kProduct
  have productPositive : 1≤(n+1)*(k+1):=by nlinarith
  cases upper <;>
    simp only [bufferBase,RootD27.Core.retainedTableBase,PDCompute.Solver.entryCount,lengthSlot,
      Bool.false_eq_true,ite_false,ite_true] at endBound countLive countValue
  all_goals
    interval_cases taken <;>
      simp [pointerCode,lengthSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
        nLive,kLive,MLive,nValue,kValue,MValue,countLive,countValue] at executed <;>
      subst after
  all_goals
    apply natural_frame_safe before _ cap budget safe capBits
    · intro target
      cases target <;>
        first
        | exact Or.inl rfl
        | refine Or.inr ⟨_,?_,rfl⟩
          omega
    · rfl
    · rfl
    · rfl
    · exact (natBits_mono (by
        try dsimp only
        omega)).trans counter

/-- Same real fetched pointer trace, full physical preservation and
EVERY-prefix SAME B; only independent actual buffer/PC words are paid. -/
theorem pointer_trace_resources (program : Program) (input : List Cell) (before : State)
    (n k M count cap budget : ℕ) (upper : Bool)
    (dimensions : PreparedDimensions before n k M)
    (storedLength : HeapList before (lengthSlot upper) [.natural count])
    (safe : RootD27.Bits.SafeBits before budget)
    (endBound : bufferBase n k M upper+count≤cap) (capBits : 1+natBits cap≤budget)
    (counter : natBits (before.pc+21)≤budget) (fetch : FetchesCode program before.pc (pointerCode upper)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (pointerResult before n k M count upper) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤330 ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output ∧
        RootD27.Bits.SafeBits state budget := by
  have executed:=pointer_execute input before n k M count upper dimensions storedLength
  have bounded:=pointer_prefix_safe input before n k M count cap budget upper dimensions storedLength safe endBound capBits counter
  obtain ⟨trace,head,last,chain,cost,resources⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (pointerCode upper)
    (pointer_straight upper) before _ fetch executed
    (fun state=>state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output ∧ RootD27.Bits.SafeBits state budget) (by
      intro taken inside state actual
      have countBound : taken≤21:=by simpa only [pointer_length] using inside
      have memory:=pointer_prefix_memory input before state n k M count taken upper dimensions storedLength countBound actual
      exact ⟨memory.1,memory.2.1,memory.2.2,bounded taken state actual⟩)
  exact ⟨trace,head,last,chain,by simpa only [pointer_length] using cost,resources⟩

/-- A real heap-read/output copies the existing live value's bits. No
parameter-only price bound or newcallerB is imposed on dirty scratch. -/
theorem outputSlot_prefix_safe (input : List Cell) (before : State) (slot budget : ℕ) (value : Cell)
    (stored : HeapList before slot [value]) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits slot≤budget) (counter : natBits (before.pc+3)≤budget) :
    PrefixSafe input (outputSlotCode slot) before budget := by
  have physical:=singleton_fields before slot value stored
  let a:=({before with pc:=before.pc+1}).set .address (.natural slot)
  let b:=({a with pc:=a.pc+1}).set .value value
  let c:=outputSlotResult before slot value
  have firstPC : natBits (before.pc+1)≤budget:=(natBits_mono (by omega : before.pc+1≤before.pc+3)).trans counter
  have aSafe : RootD27.Bits.SafeBits a budget:=(safe.withPC _ firstPC).set .address (.natural slot) addressBits
  have secondPC : natBits (a.pc+1)≤budget:=(natBits_mono (by change before.pc+1+1≤before.pc+3;omega)).trans counter
  have valueBits : value.bits≤budget:=by rw [←physical.2];exact safe.heap slot physical.1
  have bSafe : RootD27.Bits.SafeBits b budget:=(aSafe.withPC _ secondPC).set .value value valueBits
  have loadRun : Instruction.execute input (.load .value .address) a=some b := by
    simp [Instruction.execute,a,b,State.set,Cell.nat?,physical.1,physical.2]
  have outputRun : Instruction.execute input (.output .value) b=some c := by
    simp [Instruction.execute,b,a,c,outputSlotResult,State.set]
  have thirdPC : natBits (b.pc+1)≤budget:=by change natBits (before.pc+3)≤budget;exact counter
  have cSafe:=PDLower.CalibrationCompute.output_execute_safe input b c .value budget bSafe thirdPC outputRun
  have tail:=PrefixSafe.singleton input (.output .value) b c budget outputRun bSafe cSafe
  have rest:=PrefixSafe.cons input (.load .value .address) [.output .value] a b budget loadRun aSafe tail
  exact PrefixSafe.cons input (.constant .address (.natural slot)) [.load .value .address,.output .value] before a budget rfl safe rest

/-- Strengthen the actual3-op price/tag/selector read on its SAME trace,
retaining the original physical output-prefix contract and SAME B. -/
theorem outputSlot_trace_resources (program : Program) (input : List Cell) (before : State) (slot budget : ℕ) (value : Cell)
    (stored : HeapList before slot [value]) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits slot≤budget) (counter : natBits (before.pc+3)≤budget)
    (fetch : FetchesCode program before.pc (outputSlotCode slot)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (outputSlotResult before slot value) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤60 ∧
      ∀ state∈trace,RootD27.Core.EmittedPrefix before [value] state ∧ RootD27.Bits.SafeBits state budget := by
  have executed:=outputSlot_execute input before slot value stored
  have bounded:=outputSlot_prefix_safe input before slot budget value stored safe addressBits counter
  obtain ⟨trace,head,last,chain,cost,resources⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (outputSlotCode slot)
    (outputSlot_straight slot) before _ fetch executed
    (fun state=>RootD27.Core.EmittedPrefix before [value] state ∧ RootD27.Bits.SafeBits state budget) (by
      intro taken inside state actual
      have countBound : taken≤3:=by simpa only [outputSlot_length] using inside
      exact ⟨outputSlot_prefix input before state slot taken value stored countBound actual,bounded taken state actual⟩)
  exact ⟨trace,head,last,chain,by simpa only [outputSlot_length] using cost,resources⟩

end PDCompute.CoreEmit
