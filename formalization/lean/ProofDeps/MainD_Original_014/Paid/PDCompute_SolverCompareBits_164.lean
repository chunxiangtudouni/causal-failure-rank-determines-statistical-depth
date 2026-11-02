module

public import Paid.PDCompute_SolverSequenceBits_155
public import Paid.PDCompute_SolverMinimumMemory_063
public import Paid.PDLower_CalibrationCompute_IOBits_088

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

/-- Original7-op strict comparison, reusing frozen actual ratCompare
instruction safety088. All loaded values stay in the same caller budget. -/
theorem minimumCompareCode_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (values : ℕ → Cell)
    (candidate best : ℚ) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hc : values 28=.rational candidate) (hb : values 24=.rational best) (safe : RootD27.Bits.SafeBits before budget)
    (small : 4≤budget) (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget) :
    PrefixSafe input minimumCompareCode before budget := by
  let first:=loadSlotResult before base 28 .total
  let loaded:=loadSlotResult first base 24 .value
  let compared:=minimumCompareResult before base candidate best
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have firstRun:=(header.loadSlot_execute input 28 .total (by decide) fresh).1
  have firstSafe:=PrefixSafe.loadSlot input before base 28 budget .total safe fresh (header.live 28 (by decide)) (slotBits 28 (by decide))
    ((natBits_mono (by omega : before.pc+3≤before.pc+7)).trans pcBits)
  have firstBound:=firstSafe.final firstRun
  have firstFresh : first.register .fresh=.natural base := (loadSlotResult_fresh before base 28 .total (by decide)).trans fresh
  have firstHeader : Header first base values := header
  have secondRun:=(firstHeader.loadSlot_execute input 24 .value (by decide) firstFresh).1
  have secondPC : natBits (first.pc+3)≤budget :=
    (natBits_mono (by change before.pc+3+3≤before.pc+7; omega)).trans pcBits
  have secondSafe:=PrefixSafe.loadSlot input first base 24 budget .value firstBound firstFresh (firstHeader.live 24 (by decide)) (slotBits 24 (by decide)) secondPC
  have loadedBound:=secondSafe.final secondRun
  have firstTotal : first.register .total=.rational candidate := (header.loadSlot_execute input 28 .total (by decide) fresh).2.trans hc
  have loadedTotal : loaded.register .total=.rational candidate := by
    simpa only [loaded,loadSlotResult,State.set,Function.update_of_ne (by decide : (.total : Register)≠.value),
      Function.update_of_ne (by decide : (.total : Register)≠.address)] using firstTotal
  have loadedValue : loaded.register .value=.rational best := (firstHeader.loadSlot_execute input 24 .value (by decide) firstFresh).2.trans hb
  have actual : Instruction.execute input (.ratCompare .less .index .total .value) loaded=some compared := by
    simp [Instruction.execute,loadedTotal,loadedValue,Cell.rat?,Comparison.rat,compared,minimumCompareResult]
    rfl
  have zeroBits : (.natural 0 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have oneBits : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have comparisonPC : natBits (loaded.pc+1)≤budget := by
    simpa only [loaded,first,loadSlotResult,Nat.add_assoc] using pcBits
  have comparedBound:=PDLower.CalibrationCompute.ratCompare_execute_safe input loaded compared .less .index .total .value candidate best budget
    loadedBound loadedTotal loadedValue zeroBits oneBits comparisonPC actual
  have compareSafe:=PrefixSafe.singleton input (.ratCompare .less .index .total .value) loaded compared budget actual loadedBound comparedBound
  have leftRun : linearExecute input (loadSlot 28 .total++loadSlot 24 .value) before=some loaded := by
    rw [PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some]
    exact secondRun
  have leftSafe:=PrefixSafe.append input _ _ before first budget firstRun firstSafe secondSafe
  exact PrefixSafe.append input _ _ before loaded budget leftRun leftSafe compareSafe

theorem minimumCompare_trace_bits (program : Program) (input : List Cell) (before : State)
    (base budget : ℕ) (values : ℕ → Cell) (candidate best : ℚ) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (hc : values 28=.rational candidate) (hb : values 24=.rational best)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget)
    (fetch : FetchesCode program before.pc minimumCompareCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (minimumCompareResult before base candidate best) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤120 ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have run:=minimumCompareCode_execute input before base values candidate best header fresh hc hb
  have prefixSafe:=minimumCompareCode_prefix_safe input before base budget values candidate best header fresh hc hb safe small addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input minimumCompareCode
    minimumCompareCode_straight before _ fetch run (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      exact ⟨minimumCompareCode_prefix_memory input before state base values candidate best header fresh hc hb count bound executed,
        prefixSafe count state executed⟩)
  refine ⟨trace,head,last,chain,?_,invariant⟩
  simpa only [minimumCompareCode_length] using cost

end PDCompute.Solver
