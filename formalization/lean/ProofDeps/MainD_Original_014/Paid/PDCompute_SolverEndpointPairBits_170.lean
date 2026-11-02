module

public import Paid.PDCompute_SolverSequenceBits_155
public import Paid.PDCompute_SolverEndpointFrame_033
public import Paid.PDLower_CalibrationCompute_IOBits_088
public import Paid.PDCompute_Pack_InstructionBits_058
public import Paid.PDCompute_SolverSmallPrefixMemory_060

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

theorem ReaderMode.read_execute_safe (mode : ReaderMode) (input : List Cell) (before after : State)
    (target pointer : Register) (address budget : ℕ) (value : Cell) (safe : RootD27.Bits.SafeBits before budget)
    (haddress : before.register pointer=.natural address) (cell : mode.HasCell input before address value)
    (valueBits : value.bits≤budget) (pcBits : natBits (before.pc+1)≤budget)
    (actual : Instruction.execute input (mode.read target pointer) before=some after) : RootD27.Bits.SafeBits after budget := by
  cases mode with
  | inputROM => exact PDLower.CalibrationCompute.loadInput_execute_safe input before after target pointer address budget value safe haddress cell valueBits pcBits actual
  | liveHeap => exact PDCompute.Pack.load_execute_safe input before after target pointer address budget safe haddress cell.1 pcBits actual

/-- Actual original4-op endpoint pair, genuine ROM/heap data and real
pointer increment. Inputs are real typed cells, not an endpoint oracle. -/
theorem endpointPairCode_prefix_safe (mode : ReaderMode) (input : List Cell) (before : State)
    (address budget : ℕ) (error charge : ℚ) (haddress : before.register .address=.natural address)
    (herror : mode.HasCell input before address (.rational error)) (hcharge : mode.HasCell input before (address+1) (.rational charge))
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (errorBits : (.rational error : Cell).bits≤budget) (chargeBits : (.rational charge : Cell).bits≤budget)
    (pointerBits : 1+natBits (address+1)≤budget) (pcBits : natBits (before.pc+4)≤budget) :
    PrefixSafe input (endpointPairCode mode) before budget := by
  let read:=({before with pc:=before.pc+1}).set .total (.rational error)
  let marked:=({read with pc:=read.pc+1}).set .flag (.natural 1)
  let advanced:=({marked with pc:=marked.pc+1}).set .address (.natural (address+1))
  let final:=({advanced with pc:=advanced.pc+1}).set .value (.rational charge)
  have readRun:=ReaderMode.read_execute mode input before .address .total address (.rational error) haddress herror
  have readPC : natBits (before.pc+1)≤budget := (natBits_mono (by omega : before.pc+1≤before.pc+4)).trans pcBits
  have readSafe : RootD27.Bits.SafeBits read budget := ReaderMode.read_execute_safe mode input before read .total .address address budget (.rational error)
    safe haddress herror errorBits readPC readRun
  have markRun : Instruction.execute input (.constant .flag (.natural 1)) read=some marked := rfl
  have oneBits : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have markPC : natBits (read.pc+1)≤budget := (natBits_mono (by change before.pc+1+1≤before.pc+4; omega)).trans pcBits
  have markedSafe : RootD27.Bits.SafeBits marked budget := (readSafe.withPC _ markPC).set .flag (.natural 1) oneBits
  have markedAddress : marked.register .address=.natural address := by simp [marked,read,State.set,haddress]
  have markedOne : marked.register .flag=.natural 1 := by simp [marked,State.set]
  have advanceRun : Instruction.execute input (.natOp .add .address .address .flag) marked=some advanced := by
    simp [Instruction.execute,markedAddress,markedOne,Cell.nat?,NatOp.eval,advanced]
  have advancePC : natBits (marked.pc+1)≤budget := (natBits_mono (by change before.pc+1+1+1≤before.pc+4; omega)).trans pcBits
  have advancedSafe : RootD27.Bits.SafeBits advanced budget := (markedSafe.withPC _ advancePC).set .address (.natural (address+1)) pointerBits
  have advancedAddress : advanced.register .address=.natural (address+1) := by simp [advanced,State.set]
  have actualCharge : mode.HasCell input advanced (address+1) (.rational charge) := by cases mode <;> exact hcharge
  have finalRun:=ReaderMode.read_execute mode input advanced .address .value (address+1) (.rational charge) advancedAddress actualCharge
  have finalPC : natBits (advanced.pc+1)≤budget := by simpa only [advanced,marked,read,State.set,Nat.add_assoc] using pcBits
  have finalSafe : RootD27.Bits.SafeBits final budget := ReaderMode.read_execute_safe mode input advanced final .value .address (address+1) budget (.rational charge)
    advancedSafe advancedAddress actualCharge chargeBits finalPC finalRun
  have suffix:=PrefixSafe.singleton input (mode.read .value .address) advanced final budget finalRun advancedSafe finalSafe
  exact PrefixSafe.cons input _ _ before read budget readRun safe
    (PrefixSafe.cons input _ _ read marked budget markRun readSafe (PrefixSafe.cons input _ _ marked advanced budget advanceRun markedSafe suffix))

theorem endpointPair_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell) (before : State)
    (base address budget : ℕ) (error charge : ℚ) (haddress : before.register .address=.natural address)
    (herror : mode.HasCell input before address (.rational error)) (hcharge : mode.HasCell input before (address+1) (.rational charge))
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (errorBits : (.rational error : Cell).bits≤budget) (chargeBits : (.rational charge : Cell).bits≤budget)
    (pointerBits : 1+natBits (address+1)≤budget) (pcBits : natBits (before.pc+4)≤budget)
    (fetch : FetchesCode program before.pc (endpointPairCode mode)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (endpointPairResult before address error charge) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤75 ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have run:=endpointPairCode_execute mode input before address error charge haddress herror hcharge
  have prefixSafe:=endpointPairCode_prefix_safe mode input before address budget error charge haddress herror hcharge safe small errorBits chargeBits pointerBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (endpointPairCode mode)
    (endpointPairCode_straight mode) before _ fetch run (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      have memory:=endpointPairCode_prefix_memory mode input before state address error charge haddress herror hcharge count bound executed
      exact ⟨HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2,prefixSafe count state executed⟩)
  refine ⟨trace,head,last,chain,?_,invariant⟩
  simpa only [endpointPairCode_length] using cost

end PDCompute.Solver
