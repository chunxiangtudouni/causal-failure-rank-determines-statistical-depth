module

public import Paid.PDLower_CalibrationCompute_Emit_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem emitLead_header {before : State} {base : ℕ} {header : Header} (weight : ℚ)
    (represented : header.At before base) (outside : base+16≤header.outputCursor) :
    header.At (emitLeadResult before base header.outputCursor header.q weight) base := by
  have first : HeapList (writeCell before header.outputCursor (.rational header.q)) base header.cells :=
    HeapList.writeOutside represented header.outputCursor (.rational header.q) (by
      intro i bound
      rw [Header.cells_length] at bound
      omega)
  have second := HeapList.writeOutside first (header.outputCursor+1) (.rational weight) (by
    intro i bound
    rw [Header.cells_length] at bound
    omega)
  exact second

/-- The actual two result writes preserve all original header fields;
the only subsequent header changes are cursor+2 and level+1. -/
theorem emit_header {before : State} {base : ℕ} {header : Header} (weight : ℚ)
    (represented : header.At before base) (outside : base+16≤header.outputCursor) :
    ({header with level:=header.level+1,outputCursor:=header.outputCursor+2}).At
      (emitResult before base header.outputCursor header.level header.q weight) base := by
  have lead := emitLead_header weight represented outside
  have cursor : ({header with outputCursor:=header.outputCursor+2}).At
      (storeSlotResult (emitLeadResult before base header.outputCursor header.q weight) base 15 .index) base :=
    lead.storeResult 15 (by decide) .index (.natural (header.outputCursor+2))
      (by simp [emitLeadResult]) (Header.set_outputCursor _ _)
  exact incrementSlot_header cursor (by decide) (Header.set_level _ _)

theorem emit_fresh (before : State) (base cursor level : ℕ) (q weight : ℚ) :
    (emitResult before base cursor level q weight).register .fresh=before.register .fresh := by
  simp [emitResult,incrementSlot_fresh,storeSlotResult,emitLeadResult,loadSlotResult]

end PDLower.CalibrationCompute
