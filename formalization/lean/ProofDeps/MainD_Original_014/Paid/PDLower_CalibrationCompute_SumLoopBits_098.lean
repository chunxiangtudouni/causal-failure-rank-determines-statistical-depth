module

public import Paid.PDLower_CalibrationCompute_SumGateBits_093
public import Paid.PDLower_CalibrationCompute_SumCellBits_095
public import Paid.PDLower_CalibrationCompute_SumMemory_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

namespace PDLower.CalibrationCompute

/-- Only intrinsic concrete scalar/address inequalities. The actual
runtime, live header, row and caller scratch remain separate inputs. -/
structure SumOperandBounds (origin base read level budget : ℕ) (row : Array ℚ) : Prop where
  slot : ∀ offset∈([5,7,9,11] : List ℕ),1+natBits (base+offset)≤budget
  address : ∀ cursor<level,(Cell.natural (read+cursor)).bits≤budget
  next : ∀ cursor<level,(Cell.natural (cursor+1)).bits≤budget
  sumBits : ∀ count≤level,(Cell.rational (rowPrefixSum row count)).bits≤budget
  zero : (Cell.natural 0).bits≤budget
  one : (Cell.natural 1).bits≤budget
  pc : ∀ label count,count≤(basicBlock label).body.length→natBits (labelAddress origin label+count)≤budget

/-- Actual whole scalar summation loop and the same caller operand
budget at EVERY original state. No successful loop or global-prefix
resource conclusion is an input; each accumulator bound is the actual
shared-denominator array-prefix sum. -/
theorem sumLoop_bits (origin : ℕ) (input : List Cell) (base : ℕ) (row : Array ℚ) (remaining : ℕ)
    (before : State) (header : Header) (budget : ℕ)
    (position : before.pc=labelAddress origin .sumGate)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (readOutside : base+16≤header.readBase) (rowSize : header.level<row.size)
    (count : header.level=header.cursor+remaining)
    (qValue : header.q=rowPrefixSum row header.cursor)
    (bounds : SumOperandBounds origin base header.readBase header.level budget row) :
    ∃ after : State,BitSegment origin input before after (465*remaining+135) budget ∧
      after.pc=labelAddress origin .sumFinish ∧
      ({header with cursor:=header.level,q:=rowPrefixSum row header.level}).At after base ∧
      RowAt after header.readBase row ∧ after.register .fresh=.natural base ∧ after.output=before.output ∧
      PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before after := by
  have targets : ∀ label,natBits (labelAddress origin label)≤budget := by
    intro label
    simpa only [Nat.add_zero] using bounds.pc label 0 (Nat.zero_le _)
  induction remaining generalizing before header with
  | zero =>
    have cursorEq : header.cursor=header.level := by omega
    let middle := sumGateResult before base header.cursor header.level
    let after : State := {middle with pc:=labelAddress origin .sumFinish}
    have run : BitSegment origin input before after 135 budget := by
      simpa only [middle,after,cursorEq,lt_self_iff_false,ite_false] using
        sumGate_bitSegment origin input before base budget header position represented fresh safe
          (bounds.slot 7 (by simp)) (bounds.slot 5 (by simp)) bounds.zero bounds.one
          (by simpa only [position] using bounds.pc .sumGate 7 (by decide)) targets
    have finalHeader : {header with cursor:=header.level,q:=rowPrefixSum row header.level}=header := by
      have qEq : rowPrefixSum row header.level=header.q := by rw [←cursorEq,←qValue]
      have pairEq : (header.level,rowPrefixSum row header.level)=(header.cursor,header.q) := Prod.ext cursorEq.symm qEq
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
    have fEntered : entered.register .fresh=.natural base := (sumGate_fresh before base header.cursor header.level).trans fresh
    have iEntered : entered.register .index=.natural header.cursor := sumGate_index before base header represented
    have gate : BitSegment origin input before entered 135 budget := by
      simpa only [middle,entered,ite_eq_left below] using
        sumGate_bitSegment origin input before base budget header position represented fresh safe
          (bounds.slot 7 (by simp)) (bounds.slot 5 (by simp)) bounds.zero bounds.one
          (by simpa only [position] using bounds.pc .sumGate 7 (by decide)) targets
    let computed := sumCellResult entered base header.readBase header.cursor header.q (row.getD header.cursor 0)
    let nextState : State := {computed with pc:=labelAddress origin .sumGate}
    let nextHeader : Header := {header with cursor:=header.cursor+1,q:=header.q+row.getD header.cursor 0}
    have addedBits : (Cell.rational (header.q+row.getD header.cursor 0)).bits≤budget := by
      rw [qValue,←rowPrefixSum_succ]
      exact bounds.sumBits (header.cursor+1) (by omega)
    have cell : BitSegment origin input entered nextState 330 budget :=
      sumCell_bitSegment origin input entered base budget header row rfl hEntered rEntered inside fEntered iEntered gate.final
        (bounds.slot 7 (by simp)) (bounds.slot 9 (by simp)) (bounds.slot 11 (by simp))
        (bounds.address header.cursor below) addedBits bounds.one (bounds.next header.cursor below)
        (by simpa only [entered] using bounds.pc .sumCell 20 (by decide)) (targets .sumGate)
    have nextRepresented : nextHeader.At nextState base := sumCell_header row hEntered
    have computedRow := sumCell_row row rEntered readOutside
    have nextRow : RowAt nextState nextHeader.readBase row := ⟨computedRow.live,computedRow.value⟩
    have nextFresh : nextState.register .fresh=.natural base :=
      (sumCell_fresh entered base header.readBase header.cursor header.q (row.getD header.cursor 0)).trans fEntered
    have nextCount : nextHeader.level=nextHeader.cursor+remaining := by dsimp [nextHeader]; omega
    have nextQ : nextHeader.q=rowPrefixSum row nextHeader.cursor := by
      change header.q+row.getD header.cursor 0=rowPrefixSum row (header.cursor+1)
      rw [rowPrefixSum_succ,qValue]
    obtain ⟨after,later,last,finalHeader,finalRow,finalFresh,finalOutput,finalMemory⟩ :=
      ih nextState nextHeader rfl nextRepresented nextRow nextFresh cell.final readOutside rowSize nextCount nextQ bounds
    refine ⟨after,((gate.trans cell).trans later).mono (by omega),last,?_,finalRow,finalFresh,?_,?_⟩
    · exact finalHeader
    · exact finalOutput
    · have current : PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before nextState :=
        sumCell_memoryFrame entered base header.readBase header.cursor header.q (row.getD header.cursor 0)
      exact current.trans finalMemory

end PDLower.CalibrationCompute
