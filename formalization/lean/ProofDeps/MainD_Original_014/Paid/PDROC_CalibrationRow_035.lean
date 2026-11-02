module

public import Paid.PDROC_CalibrationRow_031
public import Paid.PDROC_CalibrationRow_020
public import Paid.PDROC_CalibrationRow_021
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Actual leftRead plus its real conditional interior block. The
source index and multiplier come from the physical read row/header12. -/
theorem leftRoute (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (inside : cursor<2*level+1) (before : State)
    (data : ScatterData P base level clock cursor read write before)
    (position : before.pc=labelAddress origin .leftRead)
    (index : before.register .index=.natural cursor) :
    ∃ after : State,Segment origin input before after 360 ∧
      ScatterData P base level clock cursor read write after ∧ after.pc=labelAddress origin .leftStore ∧
      after.register .index=.natural (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val ∧
      after.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma)) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
  let mass := (P.walkRow level true clock).getD cursor 0
  let probability : ℚ := 1/2-P.certificate.gamma
  let middle := letterReadResult before base read cursor (2*level+1) 12 mass probability
  let selected : State := {middle with pc:=labelAddress origin (if cursor=0 ∨ cursor=2*level then .leftStore else .leftInterior)}
  have readBound : cursor<(P.walkRow level true clock).size := by
    simpa only [PDROC.endpointWalkRow_size] using inside
  have body : linearExecute input (basicBlock .leftRead).body before=some middle := by
    rw [leftRead_decompose]
    exact letterRead_execute input before base read cursor (2*level+1) 12 mass probability
      data.control.header.fresh (data.control.header.live 9 (by decide)) data.control.read
      (data.control.header.live 12 (by decide)) data.control.header.leftBias
      (data.control.header.live 8 (by decide)) data.control.width index
      (data.readRow.live cursor readBound) (data.readRow.value cursor readBound)
  have control : (controlInstruction origin (basicBlock .leftRead).control).execute input middle=some selected := by
    simpa only [basicBlock,letterReadResult,Nat.add_sub_cancel,middle,selected] using
      boundary_control_execute input (channelProductResult (sourceReadResult before base read cursor mass)
        base 12 mass probability) base cursor (2*level+1) origin .leftInterior .leftStore
  have first : Segment origin input before selected 300 :=
    kernel_block_trace origin .leftRead input before middle selected position body control
  have fields := letterRead_fields before base read cursor (2*level+1) 12 mass probability
  have selectedData := ScatterData.sameMemory P base level clock cursor read write before selected data rfl rfl fields.2.2.1
  have selectedIndex : selected.register .index=.natural cursor := fields.2.2.2.1.trans index
  by_cases boundary : cursor=0 ∨ cursor=2*level
  · have target : (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val=cursor := by
      simpa only [letterTarget,boundary,ite_true] using letterTarget_left level cursor inside
    refine ⟨selected,first.mono (by omega),selectedData,?_,?_,fields.2.2.2.2.1,rfl,rfl,fields.2.2.2.2.2.2.2,fields.2.2.1⟩
    · simp only [selected,boundary,ite_true]
    · rw [target]
      exact selectedIndex
  · let last := interiorResult selected false cursor
    let after : State := {last with pc:=labelAddress origin .leftStore}
    have selectedPosition : selected.pc=labelAddress origin .leftInterior := by
      simp only [selected,boundary,ite_false]
    have laterBody : linearExecute input (basicBlock .leftInterior).body selected=some last := by
      rw [leftInterior_body]
      exact interior_execute input selected false cursor selectedIndex
    have laterControl : (controlInstruction origin (basicBlock .leftInterior).control).execute input last=some after := rfl
    have later : Segment origin input selected after 60 :=
      kernel_block_trace origin .leftInterior input selected last after selectedPosition laterBody laterControl
    have lastFields := interior_fields selected false cursor
    have afterData := ScatterData.sameMemory P base level clock cursor read write selected after selectedData rfl rfl lastFields.2.2.1
    have target : (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val=cursor-1 := by
      simpa only [letterTarget,boundary,ite_false,Bool.false_eq_true] using letterTarget_left level cursor inside
    refine ⟨after,first.trans later,afterData,rfl,?_,lastFields.2.2.2.2.1.trans fields.2.2.2.2.1,
      rfl,rfl,lastFields.2.2.2.2.2.2.trans fields.2.2.2.2.2.2.2,lastFields.2.2.1.trans fields.2.2.1⟩
    rw [target]
    exact lastFields.2.2.2.1

end PDROC.CalibrationRow
