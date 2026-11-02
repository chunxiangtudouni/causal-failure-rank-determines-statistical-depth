module

public import Paid.PDLower_CalibrationCompute_Gates_030
public import Paid.PDLower_CalibrationCompute_SumMemory_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The actual bounded prefix summation loop. Its invariant relates the
stored accumulator to the original array prefix; the supplied row is the
already computed row, and no successful summation run is assumed. -/
theorem sumLoop_framed (origin : ℕ) (input : List Cell) (base : ℕ) (row : Array ℚ) (remaining : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .sumGate)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (fresh : before.register .fresh=.natural base)
    (readOutside : base+16 ≤ header.readBase) (rowSize : header.level < row.size)
    (count : header.level=header.cursor+remaining)
    (qValue : header.q=rowPrefixSum row header.cursor) :
    ∃ after : State,
      Segment origin input before after (465*remaining+135) ∧
      after.pc=labelAddress origin .sumFinish ∧
      ({header with cursor:=header.level,q:=rowPrefixSum row header.level}).At after base ∧
      RowAt after header.readBase row ∧ after.register .fresh=.natural base ∧ after.output=before.output ∧ PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before after := by
  have budget : 15*((basicBlock .sumGate).body.length+1)+15=135 := by decide
  induction remaining generalizing before header with
  | zero =>
    have cursorEq : header.cursor=header.level := by omega
    let middle := sumGateResult before base header.cursor header.level
    let after : State := {middle with pc:=labelAddress origin .sumFinish}
    have run : Segment origin input before after 135 := by
      simpa only [middle,after,cursorEq,lt_self_iff_false,ite_false,budget] using
        segment_branch origin .sumGate .sumFinish .sumCell input before middle
          (header.cursor < header.level) position (sumGate_execute input before base header represented fresh)
          rfl (by simp [middle,sumGateResult])
    have finalHeader : {header with cursor:=header.level,q:=rowPrefixSum row header.level}=header := by
      have qEq : rowPrefixSum row header.level=header.q := by rw [←cursorEq,←qValue]
      have pairEq : (header.level,rowPrefixSum row header.level)=(header.cursor,header.q) :=
        Prod.ext cursorEq.symm qEq
      exact congrArg (fun pair : ℕ×ℚ => {header with cursor:=pair.1,q:=pair.2}) pairEq
    refine ⟨after,?_,rfl,?_,?_,?_,rfl,?_⟩
    · simpa using run
    · rw [finalHeader]
      exact represented
    · exact ⟨rowAt.live,rowAt.value⟩
    · exact (sumGate_fresh before base header.cursor header.level).trans fresh
    · exact PDMenu.ComputeFrame.MemoryFrame.refl (sumRegion base) before
  | succ remaining ih =>
    have below : header.cursor<header.level := by omega
    have inside : header.cursor<row.size := by omega
    let middle := sumGateResult before base header.cursor header.level
    let entered : State := {middle with pc:=labelAddress origin .sumCell}
    have hEntered : header.At entered base := represented
    have rEntered : RowAt entered header.readBase row := ⟨rowAt.live,rowAt.value⟩
    have fEntered : entered.register .fresh=.natural base :=
      (sumGate_fresh before base header.cursor header.level).trans fresh
    have iEntered : entered.register .index=.natural header.cursor := sumGate_index before base header represented
    have gate : Segment origin input before entered 135 := by
      simpa only [middle,entered,ite_eq_left below,budget] using
        segment_branch origin .sumGate .sumFinish .sumCell input before middle
          (header.cursor < header.level) position (sumGate_execute input before base header represented fresh)
          rfl (by simp [middle,sumGateResult])
    let computed := sumCellResult entered base header.readBase header.cursor header.q (row.getD header.cursor 0)
    let nextState : State := {computed with pc:=labelAddress origin .sumGate}
    let nextHeader : Header := {header with cursor:=header.cursor+1,q:=header.q+row.getD header.cursor 0}
    have cell : Segment origin input entered nextState 330 :=
      segment_go origin .sumCell .sumGate input entered computed rfl
        (sumCell_execute input entered base header row hEntered rEntered inside fEntered iEntered) rfl
    have nextRepresented : nextHeader.At nextState base := sumCell_header row hEntered
    have computedRow := sumCell_row row rEntered readOutside
    have nextRow : RowAt nextState nextHeader.readBase row := ⟨computedRow.live,computedRow.value⟩
    have nextFresh : nextState.register .fresh=.natural base :=
      (sumCell_fresh entered base header.readBase header.cursor header.q (row.getD header.cursor 0)).trans fEntered
    have nextCount : nextHeader.level=nextHeader.cursor+remaining := by dsimp [nextHeader]; omega
    have nextQ : nextHeader.q=rowPrefixSum row nextHeader.cursor := by
      change header.q+row.getD header.cursor 0=rowPrefixSum row (header.cursor+1)
      rw [rowPrefixSum_succ,qValue]
    obtain ⟨after,later,last,finalHeader,finalRow,finalFresh,finalOutput,finalMemory⟩ := ih nextState nextHeader rfl
      nextRepresented nextRow nextFresh readOutside rowSize nextCount nextQ
    refine ⟨after,((gate.trans cell).trans later).mono (by omega),last,?_,finalRow,finalFresh,?_,?_⟩
    · exact finalHeader
    · exact finalOutput
    · have current : PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before nextState :=
        sumCell_memoryFrame entered base header.readBase header.cursor header.q (row.getD header.cursor 0)
      exact current.trans finalMemory

end PDLower.CalibrationCompute
