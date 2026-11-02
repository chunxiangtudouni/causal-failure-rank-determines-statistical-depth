module

public import Paid.PDROC_CalibrationRow_Scatter_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Actual leftRead plus its real conditional interior block. The
source index and multiplier come from the physical read row/header12. -/
theorem leftRoute_safe (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (inside : cursor<2*level+1) (before : State)
    (data : ScatterData P base level clock cursor read write before)
    (Good : State→Prop) (closed : ScatterClosed P origin base level clock read write input Good)
    (good : Good before)
    (position : before.pc=labelAddress origin .leftRead)
    (index : before.register .index=.natural cursor) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after 360 ∧
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
  have first : SafeSegment origin base (region base P.certificate.M) input Good before selected 300 :=
    scatterBlock_safe P origin base level clock cursor read write input Good closed .leftRead rfl
      before middle selected (.leftRead data inside index) good position body control
      (scatterRead_prefix_frames _ input before .leftRead (Or.inl rfl))
      ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
      (letterRead_fields before base read cursor (2*level+1) 12 mass probability).2.2.2.2.2.2.2
      (letterRead_fields before base read cursor (2*level+1) 12 mass probability).2.2.1
      (fun _ member => member)
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
    have later : SafeSegment origin base (region base P.certificate.M) input Good selected after 60 :=
      scatterBlock_safe P origin base level clock cursor read write input Good closed .leftInterior rfl
        selected last after (.leftInterior selectedData inside boundary selectedIndex fields.2.2.2.2.1)
        first.final.2.2.2.2 selectedPosition laterBody laterControl
        (by simpa only [leftInterior_body] using interior_prefix_frames _ input selected false)
        ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩ (interior_fields selected false cursor).2.2.2.2.2.2
        (interior_fields selected false cursor).2.2.1 (fun _ member => member)
    have lastFields := interior_fields selected false cursor
    have afterData := ScatterData.sameMemory P base level clock cursor read write selected after selectedData rfl rfl lastFields.2.2.1
    have target : (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val=cursor-1 := by
      simpa only [letterTarget,boundary,ite_false,Bool.false_eq_true] using letterTarget_left level cursor inside
    refine ⟨after,first.trans later,afterData,rfl,?_,lastFields.2.2.2.2.1.trans fields.2.2.2.2.1,
      rfl,rfl,lastFields.2.2.2.2.2.2.trans fields.2.2.2.2.2.2.2,lastFields.2.2.1.trans fields.2.2.1⟩
    rw [target]
    exact lastFields.2.2.2.1

end PDROC.CalibrationRow
