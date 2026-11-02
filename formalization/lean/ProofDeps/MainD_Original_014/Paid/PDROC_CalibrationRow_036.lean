module

public import Paid.PDROC_CalibrationRow_032
public import Paid.PDROC_CalibrationRow_025
public import Paid.PDROC_CalibrationRow_021
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem rightRoute (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (inside : cursor<2*level+1) (before : State)
    (data : ScatterLeftData P base level clock cursor read write inside before)
    (position : before.pc=labelAddress origin .rightRead) :
    ∃ after : State,Segment origin input before after 405 ∧
      ScatterLeftData P base level clock cursor read write inside after ∧ after.pc=labelAddress origin .rightStore ∧
      after.register .index=.natural (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val ∧
      after.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma)) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
  let mass := (P.walkRow level true clock).getD cursor 0
  let probability : ℚ := 1/2+P.certificate.gamma
  let middle := rightReadResult before base read cursor (2*level+1) mass probability
  let selected : State := {middle with pc:=labelAddress origin (if cursor=0 ∨ cursor=2*level then .rightStore else .rightInterior)}
  have readBound : cursor<(P.walkRow level true clock).size := by
    simpa only [PDROC.endpointWalkRow_size] using inside
  have body : linearExecute input (basicBlock .rightRead).body before=some middle :=
    rightRead_execute input before base read cursor (2*level+1) mass probability data.control.header.fresh
      (data.control.header.live 7 (by decide)) data.control.cursorValue
      (data.control.header.live 9 (by decide)) data.control.read
      (data.control.header.live 13 (by decide)) data.control.header.rightBias
      (data.control.header.live 8 (by decide)) data.control.width
      (data.readRow.live cursor readBound) (data.readRow.value cursor readBound)
  have control : (controlInstruction origin (basicBlock .rightRead).control).execute input middle=some selected := by
    simpa only [basicBlock,rightReadResult,letterReadResult,Nat.add_sub_cancel,middle,selected] using
      boundary_control_execute input (channelProductResult
        (sourceReadResult (loadSlotResult before base 7 .index) base read cursor mass)
        base 13 mass probability) base cursor (2*level+1) origin .rightInterior .rightStore
  have first : Segment origin input before selected 345 :=
    kernel_block_trace origin .rightRead input before middle selected position body control
  have fields := rightRead_fields before base read cursor (2*level+1) mass probability data.control.cursorValue
  have selectedData := ScatterLeftData.sameMemory P base level clock cursor read write inside before selected data rfl rfl fields.2.2.1
  have selectedIndex : selected.register .index=.natural cursor := fields.2.2.2.1
  by_cases boundary : cursor=0 ∨ cursor=2*level
  · have target : (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val=cursor := by
      simpa only [letterTarget,boundary,ite_true] using letterTarget_right level cursor inside
    refine ⟨selected,first.mono (by omega),selectedData,?_,?_,fields.2.2.2.2.1,rfl,rfl,fields.2.2.2.2.2.2.2,fields.2.2.1⟩
    · simp only [selected,boundary,ite_true]
    · rw [target]
      exact selectedIndex
  · let last := interiorResult selected true cursor
    let after : State := {last with pc:=labelAddress origin .rightStore}
    have selectedPosition : selected.pc=labelAddress origin .rightInterior := by
      simp only [selected,boundary,ite_false]
    have laterBody : linearExecute input (basicBlock .rightInterior).body selected=some last := by
      rw [rightInterior_body]
      exact interior_execute input selected true cursor selectedIndex
    have laterControl : (controlInstruction origin (basicBlock .rightInterior).control).execute input last=some after := rfl
    have later : Segment origin input selected after 60 :=
      kernel_block_trace origin .rightInterior input selected last after selectedPosition laterBody laterControl
    have lastFields := interior_fields selected true cursor
    have afterData := ScatterLeftData.sameMemory P base level clock cursor read write inside selected after selectedData rfl rfl lastFields.2.2.1
    have target : (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val=cursor+1 := by
      simpa only [letterTarget,boundary,ite_false,ite_true] using letterTarget_right level cursor inside
    refine ⟨after,first.trans later,afterData,rfl,?_,lastFields.2.2.2.2.1.trans fields.2.2.2.2.1,
      rfl,rfl,lastFields.2.2.2.2.2.2.trans fields.2.2.2.2.2.2.2,lastFields.2.2.1.trans fields.2.2.1⟩
    rw [target]
    exact lastFields.2.2.2.1

end PDROC.CalibrationRow
