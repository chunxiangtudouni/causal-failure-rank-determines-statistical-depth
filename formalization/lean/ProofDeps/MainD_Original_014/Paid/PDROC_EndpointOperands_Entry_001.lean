module

public import Paid.PDROC_EndpointOperands_Base_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Endpoint RootD27.Bits PDROC.DataBits PDROC.CalibrationRow.Operand
open PDLower.CalibrationCompute

/-- The original twelve instructions physically store M+1 in the header
and cache. Existing E and all unrelated cells are caller carry. -/
theorem cache_header_prefix_safe (input : List Cell) (P : Parameters)
    (origin base E returnPC budget : ℕ) (before : State) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (stop : values 3=.natural P.certificate.M) (cache : values 0=.natural E)
    (safe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (position : before.pc+12≤pcCap origin returnPC) : PrefixSafe input cacheHeaderCode before budget := by
  let loaded := loadSlotResult before base 3 .total
  let one := ({loaded with pc:=loaded.pc+1}).set .value (.natural 1)
  let added := ({one with pc:=one.pc+1}).set .total (.natural (P.certificate.M+1))
  let saved := storeSlotResult added base 17 .total
  let addressed := loadSlotResult saved base 0 .address
  have addressCap (slot : ℕ) (inside : slot≤48) : 1+natBits (base+slot)≤budget := by
    apply ControlBudget.address P origin base E returnPC budget _ control
    unfold naturalCap
    omega
  have counterCap : (Cell.natural (P.certificate.M+1)).bits≤budget := by
    apply ControlBudget.nat P origin base E returnPC budget _ control
    unfold naturalCap
    omega
  have firstRun : linearExecute input (loadSlot 3 .total) before=some loaded :=
    loadSlot_execute input before base 3 .total fresh (header.live 3 (by decide))
  have firstSafe := PrefixSafe.loadSlot input before base 3 budget .total safe fresh
    (header.live 3 (by decide)) (addressCap 3 (by omega))
    (ControlBudget.pc P origin base E returnPC budget _ control (by omega))
  have loadedSafe := firstSafe.final firstRun
  have oneSafe : SafeBits one budget :=
    (loadedSafe.withPC _ (ControlBudget.pc P origin base E returnPC budget _ control
      (by dsimp only [loaded,loadSlotResult];omega))).set _ _
      (ControlBudget.nat P origin base E returnPC budget 1 control (by unfold naturalCap;omega))
  have addRun : (Instruction.natOp .add .total .total .value).execute input one=some added := by
    have cell := (header.value 3 (by decide)).trans stop
    simp [one,loaded,added,loadSlotResult,Instruction.execute,State.set,Cell.nat?,NatOp.eval,cell]
  have addedSafe : SafeBits added budget :=
    (oneSafe.withPC _ (ControlBudget.pc P origin base E returnPC budget _ control
      (by dsimp only [one,loaded,loadSlotResult,State.set];omega))).set _ _ counterCap
  have countedSafe : PrefixSafe input
      [.constant .value (.natural 1),.natOp .add .total .total .value] loaded budget := by
    apply PrefixSafe.cons input _ _ loaded one budget rfl loadedSafe
    exact PrefixSafe.singleton input _ one added budget addRun oneSafe addedSafe
  have addedFresh : added.register .fresh=.natural base := by
    simpa [added,one,loaded,loadSlotResult,State.set] using fresh
  have savedRun : linearExecute input (storeSlot 17 .total) added=some saved :=
    storeSlot_execute input added base 17 .total addedFresh (by decide)
  have savedSafe := PrefixSafe.storeSlot input added base 17 budget .total addedSafe addedFresh (by decide)
    (addressCap 17 (by omega)) (ControlBudget.pc P origin base E returnPC budget _ control
      (by dsimp only [added,one,loaded,loadSlotResult,State.set];omega))
  have savedFresh : saved.register .fresh=.natural base := by
    simpa [saved,storeSlotResult,added,one,loaded,loadSlotResult,State.set] using fresh
  have zeroLive : base+0∈saved.live := by
    exact Finset.mem_insert_of_mem (header.live 0 (by decide))
  have zeroCell : saved.heap (base+0)=.natural E := by
    have cell := (header.value 0 (by decide)).trans cache
    have different : base+0≠base+17 := by omega
    simpa [saved,storeSlotResult,added,one,loaded,loadSlotResult,State.set,different] using cell
  have addressRun : linearExecute input (loadSlot 0 .address) saved=some addressed :=
    loadSlot_execute input saved base 0 .address savedFresh zeroLive
  have addressSafe := PrefixSafe.loadSlot input saved base 0 budget .address (savedSafe.final savedRun)
    savedFresh zeroLive (addressCap 0 (by omega))
    (ControlBudget.pc P origin base E returnPC budget _ control
      (by dsimp only [saved,storeSlotResult,added,one,loaded,loadSlotResult,State.set];omega))
  have addressValue : addressed.register .address=.natural E := by
    simpa [addressed,loadSlotResult,State.set] using zeroCell
  have finalSafe := PrefixSafe.store input addressed budget .address .total E
    (addressSafe.final addressRun) addressValue
    (ControlBudget.pc P origin base E returnPC budget _ control
      (by dsimp only [addressed,saved,storeSlotResult,added,one,loaded,loadSlotResult,State.set];omega))
  have tail := PrefixSafe.append input (loadSlot 0 .address) [.store .address .total]
    saved addressed budget addressRun addressSafe finalSafe
  have stores := PrefixSafe.append input (storeSlot 17 .total)
    (loadSlot 0 .address++[.store .address .total]) added saved budget savedRun savedSafe tail
  have countedRun : linearExecute input
      [.constant .value (.natural 1),.natOp .add .total .total .value] loaded=some added := by
    have firstStep : (Instruction.constant .value (.natural 1)).execute input loaded=some one := rfl
    simp only [linearExecute,firstStep,Option.bind_some,addRun]
  have rest := PrefixSafe.append input
    [.constant .value (.natural 1),.natOp .add .total .total .value]
    (storeSlot 17 .total++(loadSlot 0 .address++[.store .address .total])) loaded added budget
    countedRun countedSafe stores
  change PrefixSafe input (loadSlot 3 .total++
    ([.constant .value (.natural 1),.natOp .add .total .total .value]++
      (storeSlot 17 .total++(loadSlot 0 .address++[.store .address .total])))) before budget
  exact PrefixSafe.append input (loadSlot 3 .total) _ before loaded budget firstRun firstSafe rest

end PDROC.EndpointOperands
