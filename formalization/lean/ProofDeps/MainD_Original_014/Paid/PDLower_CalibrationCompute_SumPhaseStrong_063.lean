module

public import Paid.PDLower_CalibrationCompute_SumLoopStrong_062
public import Paid.PDLower_CalibrationCompute_SumFinish_034

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem RowAt.constantResultStrong {before : State} {read : ℕ} {row : Array ℚ}
    (represented : RowAt before read row) (base offset : ℕ) (value : Cell)
    (separate : ∀ index<row.size,read+index ≠ base+offset) :
    RowAt (constantSlotResult before base offset value) read row := by
  have same : RowAt ({before with pc:=before.pc+1}.set .value value) read row :=
    ⟨represented.live,represented.value⟩
  exact same.storeResult base offset .value separate

theorem sumStart_rowStrong {before : State} {base : ℕ} {header : Header} (row : Array ℚ)
    (represented : RowAt before header.readBase row) (outside : base+16≤header.readBase) :
    RowAt (sumStartResult before base) header.readBase row := by
  have first := represented.constantResultStrong base 11 (.rational 0) (by intros; omega)
  exact first.constantResultStrong base 7 (.natural 0) (by intros; omega)

/-- Complete ACTUAL summation phase, including zero initialization,
every prefix iteration, the final center cell's half contribution and
the real jump to the weight block. -/
theorem sumPhase_framed (origin : ℕ) (input : List Cell) (base : ℕ) (row : Array ℚ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .sumStart)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (fresh : before.register .fresh=.natural base)
    (outside : base+16≤header.readBase) (rowSize : header.level<row.size) :
    ∃ after : State,
      Segment origin input before after (1000*(header.level+1)) ∧
      after.pc=labelAddress origin .weight ∧
      ({header with
        cursor:=header.level
        q:=rowPrefixSum row header.level+row.getD header.level 0*(1/2)}).At after base ∧
      after.register .fresh=.natural base ∧ after.output=before.output ∧ PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before after := by
  let first : State := {sumStartResult before base with pc:=labelAddress origin .sumGate}
  let firstHeader : Header := {header with q:=0,cursor:=0}
  have start : Segment origin input before first 150 :=
    segment_go origin .sumStart .sumGate input before (sumStartResult before base) position
      (sumStart_execute input before base fresh) rfl
  have firstRepresented : firstHeader.At first base := sumStart_header represented
  have initializedRow := sumStart_rowStrong row rowAt outside
  have firstRow : RowAt first firstHeader.readBase row := ⟨initializedRow.live,initializedRow.value⟩
  have firstFresh : first.register .fresh=.natural base := by
    simpa [first,sumStartResult,constantSlot_fresh] using fresh
  obtain ⟨last,loop,atFinish,lastHeader,lastRow,lastFresh,lastOutput,loopMemory⟩ :=
    sumLoop_framed origin input base row header.level first firstHeader rfl firstRepresented firstRow firstFresh outside rowSize
      (by simp [firstHeader]) (by simp [firstHeader,rowPrefixSum_zero])
  let summedHeader : Header := {header with cursor:=header.level,q:=rowPrefixSum row header.level}
  let completed := sumFinishResult last base header.readBase header.level (rowPrefixSum row header.level)
    (row.getD header.level 0)
  let after : State := {completed with pc:=labelAddress origin .weight}
  have complete : Segment origin input last after 285 :=
    segment_go origin .sumFinish .weight input last completed atFinish
      (sumFinish_execute input last base summedHeader row lastHeader lastRow rowSize lastFresh) rfl
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
