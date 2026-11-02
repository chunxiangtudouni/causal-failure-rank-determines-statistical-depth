module

public import Paid.PDROC_CalibrationRow_OperandPrefix_002
public import Paid.PDCompute_SolverNatSlots_084
public import Paid.PDCompute_Pack_TraceInvariant_055
public import Paid.PDCompute_SolverHeaderLoads_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.NatControl

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)
open PDROC.CalibrationRow.Operand

/-- All TEN real natural-slot prefixes preserve the same actual caller
budget once the actual calculated natural result is bounded. Source and
target aliasing is allowed; both real reads precede the real write. -/
theorem natBinarySlots_prefix_safe (input : List Cell) (before : State) (base budget left right target : ℕ)
    (operation : NatOp) (x y result : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (leftInside : left<headerWords) (rightInside : right<headerWords) (targetInside : target<headerWords)
    (leftValue : values left=.natural x) (rightValue : values right=.natural y)
    (evaluated : operation.eval x y=some result) (safe : RootD27.Bits.SafeBits before budget)
    (resultBits : (.natural result : Cell).bits≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+10)≤budget) :
    PrefixSafe input (natBinarySlots operation left right target) before budget := by
  let first:=loadSlotResult before base left .total
  let loaded:=loadSlotResult first base right .value
  let computed:=({loaded with pc:=loaded.pc+1}).set .total (.natural result)
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have firstRun:=(header.loadSlot_execute input left .total leftInside fresh).1
  have firstSafe:=PrefixSafe.loadSlot input before base left budget .total safe fresh (header.live left leftInside) (slotBits left leftInside)
    ((natBits_mono (by omega : before.pc+3≤before.pc+10)).trans pcBits)
  have firstBound:=firstSafe.final firstRun
  have firstFresh : first.register .fresh=.natural base := (loadSlotResult_fresh before base left .total (by decide)).trans fresh
  have firstHeader : Header first base values := header
  have secondRun:=(firstHeader.loadSlot_execute input right .value rightInside firstFresh).1
  have secondPC : natBits (first.pc+3)≤budget :=
    (natBits_mono (by change before.pc+3+3≤before.pc+10; omega)).trans pcBits
  have secondSafe:=PrefixSafe.loadSlot input first base right budget .value firstBound firstFresh (firstHeader.live right rightInside)
    (slotBits right rightInside) secondPC
  have loadedBound:=secondSafe.final secondRun
  have loadedFresh : loaded.register .fresh=.natural base := (loadSlotResult_fresh first base right .value (by decide)).trans firstFresh
  have firstTotal : first.register .total=.natural x := (header.loadSlot_execute input left .total leftInside fresh).2.trans leftValue
  have loadedTotal : loaded.register .total=.natural x := by
    simpa only [loaded,loadSlotResult,State.set,Function.update_of_ne (by decide : (.total : Register)≠.value),
      Function.update_of_ne (by decide : (.total : Register)≠.address)] using firstTotal
  have loadedValue : loaded.register .value=.natural y := (firstHeader.loadSlot_execute input right .value rightInside firstFresh).2.trans rightValue
  have ratPC : natBits (loaded.pc+1)≤budget :=
    (natBits_mono (by change before.pc+3+3+1≤before.pc+10; omega)).trans pcBits
  have ratSafe:=PrefixSafe.natOp input loaded budget operation .total .total .value x y result loadedBound loadedTotal loadedValue evaluated resultBits ratPC
  have ratRun : Instruction.execute input (.natOp operation .total .total .value) loaded=some computed := by
    simp [Instruction.execute,loadedTotal,loadedValue,Cell.nat?,evaluated,computed]
  have ratLinear : linearExecute input [.natOp operation .total .total .value] loaded=some computed := by
    simp only [linearExecute,ratRun,Option.bind_some]
  have computedBound:=ratSafe.final ratLinear
  have computedFresh : computed.register .fresh=.natural base := by simpa only [computed,State.set,Function.update_of_ne (by decide : (.fresh : Register)≠.total)] using loadedFresh
  have storePC : natBits (computed.pc+3)≤budget := by
    simpa only [computed,loaded,first,loadSlotResult,State.set,Nat.add_assoc] using pcBits
  have storeSafe:=PrefixSafe.storeSlot input computed base target budget .total computedBound computedFresh (by decide) (slotBits target targetInside) storePC
  have leftSafe:=PrefixSafe.append input (loadSlot left .total) (loadSlot right .value) before first budget firstRun firstSafe secondSafe
  have leftRun : linearExecute input (loadSlot left .total++loadSlot right .value) before=some loaded := by
    rw [PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some]
    exact secondRun
  have middleSafe:=PrefixSafe.append input _ [.natOp operation .total .total .value] before loaded budget leftRun leftSafe ratSafe
  have middleRun : linearExecute input ((loadSlot left .total++loadSlot right .value)++[.natOp operation .total .total .value]) before=some computed := by
    rw [PDLower.CalibrationCompute.linearExecute_append,leftRun,Option.bind_some]
    exact ratLinear
  exact PrefixSafe.append input _ (storeSlot target .total) before computed budget middleRun middleSafe storeSafe

/-- SAME fetched natural-slot trace has its actual physical frame and
original full-state bits. Concrete controls discharge only the new value. -/
theorem natBinarySlots_trace_bits (program : Program) (input : List Cell) (before : State)
    (base left right target x y result n k budget : ℕ) (operation : NatOp) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (leftInside : left<headerWords) (rightInside : right<headerWords) (targetInside : target<headerWords)
    (leftValue : values left=.natural x) (rightValue : values right=.natural y) (evaluated : operation.eval x y=some result)
    (safe : RootD27.Bits.SafeBits before budget) (resultBits : (.natural result : Cell).bits≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+10)≤budget)
    (fetch : FetchesCode program before.pc (natBinarySlots operation left right target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (natBinarySlotsResult before base left right target x y result) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤165 ∧
      Header (natBinarySlotsResult before base left right target x y result) base (Function.update values target (.natural result)) ∧
      (natBinarySlotsResult before base left right target x y result).register .fresh=.natural base ∧
      (natBinarySlotsResult before base left right target x y result).pc=before.pc+10 ∧
      Frame before (natBinarySlotsResult before base left right target x y result) base n k ∧
      (natBinarySlotsResult before base left right target x y result).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have run:=natBinarySlots_execute input before base left right target x y result operation values header leftInside rightInside leftValue rightValue fresh evaluated
  have prefixSafe:=natBinarySlots_prefix_safe input before base budget left right target operation x y result values header fresh leftInside rightInside targetInside
    leftValue rightValue evaluated safe resultBits addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (natBinarySlots operation left right target)
    (natBinarySlots_straight operation left right target) before _ fetch run
    (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state execute
      exact ⟨natBinarySlots_prefix_memory input before state base left right target x y result operation values header leftInside rightInside targetInside
        leftValue rightValue fresh evaluated count bound execute,prefixSafe count state execute⟩)
  have fields:=PDROC.D27Prepare.Program.natBinarySlotsResult_fields before base left right target result
  exact ⟨trace,head,last,chain,cost,natBinarySlots_header before base left right target x y result values header,
    fields.2.2.1.trans fresh,fields.2.2.2.1,
    slotWrite_frame before _ base target n k (.natural result) targetInside fields.1 fields.2.1,fields.2.2.2.2,invariant⟩

end PDCompute.NatControl
