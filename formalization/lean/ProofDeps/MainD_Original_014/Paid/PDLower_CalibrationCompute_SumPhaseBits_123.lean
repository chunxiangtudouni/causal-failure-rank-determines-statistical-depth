module

public import Paid.PDLower_CalibrationCompute_SumStartBits_091
public import Paid.PDLower_CalibrationCompute_SumFinishBits_096
public import Paid.PDLower_CalibrationCompute_SumLoopBits_098
public import Paid.PDLower_CalibrationCompute_SumPhaseStrong_063

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

namespace PDLower.CalibrationCompute

/-- Real zero initialization, every actual scalar sum iteration and
center-half finish, with the SAME complete-state B throughout. The
intrinsic array/scalar conditions are discharged for the original caller
by the shared-denominator budget bridge, rather than supplied to the
original whole-program target. -/
theorem sumPhase_bits (origin : ℕ) (input : List Cell) (base : ℕ) (row : Array ℚ)
    (before : State) (header : Header) (budget : ℕ)
    (position : before.pc=labelAddress origin .sumStart)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (outside : base+16≤header.readBase) (rowSize : header.level<row.size)
    (bounds : SumOperandBounds origin base header.readBase header.level budget row)
    (zeroRat : (Cell.rational 0).bits≤budget) (halfBits : (Cell.rational (1/2)).bits≤budget)
    (centerAddress : (Cell.natural (header.readBase+header.level)).bits≤budget)
    (centerHalfBits : (Cell.rational (row.getD header.level 0*(1/2))).bits≤budget)
    (finalQBits : (Cell.rational (rowPrefixSum row header.level+row.getD header.level 0*(1/2))).bits≤budget) :
    ∃ after : State,BitSegment origin input before after (1000*(header.level+1)) budget ∧
      after.pc=labelAddress origin .weight ∧
      ({header with
        cursor:=header.level,q:=rowPrefixSum row header.level+row.getD header.level 0*(1/2)}).At after base ∧
      after.register .fresh=.natural base ∧ after.output=before.output ∧
      PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before after := by
  have targets : ∀ label,natBits (labelAddress origin label)≤budget := by
    intro label
    simpa only [Nat.add_zero] using bounds.pc label 0 (Nat.zero_le _)
  let first : State := {sumStartResult before base with pc:=labelAddress origin .sumGate}
  let firstHeader : Header := {header with q:=0,cursor:=0}
  have start : BitSegment origin input before first 150 budget :=
    sumStart_bitSegment origin input before base budget position safe fresh bounds.zero zeroRat
      (bounds.slot 7 (by simp)) (bounds.slot 11 (by simp))
      (by simpa only [position] using bounds.pc .sumStart 8 (by decide)) targets
  have firstRepresented : firstHeader.At first base := sumStart_header represented
  have initializedRow := sumStart_rowStrong row rowAt outside
  have firstRow : RowAt first firstHeader.readBase row := ⟨initializedRow.live,initializedRow.value⟩
  have firstFresh : first.register .fresh=.natural base := by
    simpa [first,sumStartResult,constantSlot_fresh] using fresh
  obtain ⟨last,loop,atFinish,lastHeader,lastRow,lastFresh,lastOutput,loopMemory⟩ :=
    sumLoop_bits origin input base row header.level first firstHeader budget rfl firstRepresented firstRow firstFresh
      start.final outside rowSize (by simp [firstHeader]) (by simp [firstHeader,rowPrefixSum_zero]) bounds
  let summedHeader : Header := {header with cursor:=header.level,q:=rowPrefixSum row header.level}
  let completed := sumFinishResult last base header.readBase header.level (rowPrefixSum row header.level) (row.getD header.level 0)
  let after : State := {completed with pc:=labelAddress origin .weight}
  have complete : BitSegment origin input last after 285 budget :=
    sumFinish_bitSegment origin input last base budget summedHeader row atFinish lastHeader lastRow rowSize lastFresh loop.final
      (bounds.slot 5 (by simp)) (bounds.slot 9 (by simp)) (bounds.slot 11 (by simp))
      centerAddress halfBits centerHalfBits finalQBits
      (by simpa only [atFinish] using bounds.pc .sumFinish 17 (by decide)) (targets .weight)
  refine ⟨after,((start.trans loop).trans complete).mono (by omega),rfl,?_,?_,?_,?_⟩
  · exact sumFinish_header row lastHeader
  · simpa [after,completed,sumFinishResult,storeSlotResult,sumFinishLeadResult,loadSlotResult] using lastFresh
  · exact lastOutput
  · have initialized : PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before first := by
      have one := constantSlotResult_memoryFrame (sumRegion base) before base 11 (.rational 0) (by simp [sumRegion])
      have two := constantSlotResult_memoryFrame (sumRegion base) (constantSlotResult before base 11 (.rational 0))
        base 7 (.natural 0) (by simp [sumRegion])
      exact one.trans two
    have finished : PDMenu.ComputeFrame.MemoryFrame (sumRegion base) last after :=
      sumFinish_memoryFrame last base header.readBase header.level (rowPrefixSum row header.level) (row.getD header.level 0)
    exact (initialized.trans loopMemory).trans finished

end PDLower.CalibrationCompute
