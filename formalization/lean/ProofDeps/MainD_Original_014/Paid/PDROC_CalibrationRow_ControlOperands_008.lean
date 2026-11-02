module

public import Paid.PDROC_CalibrationRow_ControlOperands_003
public import Paid.PDROC_CalibrationRow_ControlOperands_006
public import Paid.PDROC_CalibrationRow_ControlOperands_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits PDMenu.ComputeFrame

/-- All THIRTY actual levelInit prefixes retain the SAME caller B.
No incoming row, cursor, pointer, clock type or scratch P-bound is used. -/
theorem levelInit_prefix_safe (input : List Cell) (P : Parameters) (origin base level budget : ℕ)
    (before : State) (header : PDROC.CalibrationRow.Header P base level before)
    (position : before.pc=labelAddress origin .levelInit) (levelBound : level≤P.certificate.M+1)
    (safe : SafeBits before budget) (bounds : ControlBudget P origin base budget) :
    PrefixSafe input (basicBlock .levelInit).body before budget := by
  have active := activeWidth_le P.certificate.M level levelBound
  have cap := controlNaturalCap_lower P base
  have doubled : level*2≤controlNaturalCap P base := by omega
  have widthBound : level*2+1≤controlNaturalCap P base := by omega
  have doubledM : P.certificate.M*2≤controlNaturalCap P base := by
    have width := cap.2.1
    unfold rowWidth at width
    omega
  have widthM : P.certificate.M*2+3≤controlNaturalCap P base := by
    simpa only [rowWidth,Nat.mul_comm] using cap.2.1
  have secondBound : firstRow base+(P.certificate.M*2+3)≤controlNaturalCap P base := by
    simp only [controlNaturalCap,firstRow,rowWidth]
    omega
  let width := widthResult before base level
  have widthFields := widthResult_fields before base level
  have widthHeader := PDROC.CalibrationRow.Header.transport P base level before width header
    (widthResult_frame before base level _) (by rw [widthFields.2.1]; exact Finset.subset_insert _ _) widthFields.2.2.1
  have widthPC : width.pc=before.pc+10 := widthFields.2.2.2.2.1
  have widthRun := width_execute input before base level header.fresh (header.live 5 (by decide)) header.level
  have widthSafe := width_prefix_safe input before base level budget safe header.fresh (header.live 5 (by decide)) header.level
    (ControlBudget.slot P origin base budget 5 bounds (by decide)) (ControlBudget.slot P origin base budget 8 bounds (by decide))
    (ControlBudget.literal P origin base budget 2 bounds (by decide)) (ControlBudget.literal P origin base budget 1 bounds (by decide))
    (ControlBudget.nat P origin base budget _ bounds doubled) (ControlBudget.nat P origin base budget _ bounds widthBound)
    (ControlBudget.pc_prefix P origin base budget bounds before .levelInit 10 position (by decide))
  let first := firstPointerResult width base
  have firstFields := firstPointer_fields width base
  have firstHeader := PDROC.CalibrationRow.Header.transport P base level width first widthHeader
    (firstPointer_frame width base _) (by rw [firstFields.2.1]; exact Finset.subset_insert _ _) firstFields.2.2.1
  have firstPC : first.pc=before.pc+15 := by
    simpa only [widthPC,Nat.add_assoc] using firstFields.2.2.2.2.1
  have firstRun := firstPointer_execute input width base widthHeader.fresh
  have firstSafe := firstPointer_prefix_safe input width base budget (widthSafe.final widthRun) widthHeader.fresh
    (ControlBudget.literal P origin base budget 16 bounds (by decide))
    (ControlBudget.nat P origin base budget (base+16) bounds cap.1)
    (ControlBudget.slot P origin base budget 9 bounds (by decide))
    (by simpa only [widthPC,Nat.add_assoc] using
      ControlBudget.pc_prefix P origin base budget bounds before .levelInit 15 position (by decide))
  let second := secondPointerResult first base P.certificate.M
  have secondFields := secondPointer_fields first base P.certificate.M
  have secondFresh := secondFields.2.2.1.trans firstHeader.fresh
  have secondPC : second.pc=before.pc+26 := by
    simpa only [firstPC,Nat.add_assoc] using secondFields.2.2.2.1
  have secondRun := secondPointer_execute input first base P.certificate.M firstHeader.fresh
    firstFields.2.2.2.1 (firstHeader.live 2 (by decide)) firstHeader.M
  have secondSafe := secondPointer_prefix_safe input first base P.certificate.M budget (firstSafe.final firstRun)
    firstHeader.fresh firstFields.2.2.2.1 (firstHeader.live 2 (by decide)) firstHeader.M
    (ControlBudget.literal P origin base budget 2 bounds (by decide)) (ControlBudget.literal P origin base budget 3 bounds (by decide))
    (ControlBudget.nat P origin base budget _ bounds doubledM) (ControlBudget.nat P origin base budget _ bounds widthM)
    (ControlBudget.nat P origin base budget _ bounds secondBound)
    (ControlBudget.slot P origin base budget 2 bounds (by decide)) (ControlBudget.slot P origin base budget 10 bounds (by decide))
    (by simpa only [firstPC,Nat.add_assoc] using
      ControlBudget.pc_prefix P origin base budget bounds before .levelInit 26 position (by decide))
  have resetSafe := constantSlot_sameBudget input second base 7 budget (.natural 0) (secondSafe.final secondRun) secondFresh
    (ControlBudget.literal P origin base budget 0 bounds (by decide)) (ControlBudget.slot P origin base budget 7 bounds (by decide))
    (by simpa only [secondPC,Nat.add_assoc] using
      ControlBudget.pc_prefix P origin base budget bounds before .levelInit 30 position (by decide))
  have tail := PrefixSafe.append input secondPointerCode (constantSlot 7 (.natural 0)) first second budget
    secondRun secondSafe resetSafe
  have buffers := PrefixSafe.append input firstPointerCode (secondPointerCode++constantSlot 7 (.natural 0))
    width first budget firstRun firstSafe tail
  have whole := PrefixSafe.append input widthCode
    (firstPointerCode++(secondPointerCode++constantSlot 7 (.natural 0))) before width budget widthRun widthSafe buffers
  rw [levelInit_decompose,buffersCode_decompose]
  simpa only [List.append_assoc] using whole

end PDROC.CalibrationRow.Operand
