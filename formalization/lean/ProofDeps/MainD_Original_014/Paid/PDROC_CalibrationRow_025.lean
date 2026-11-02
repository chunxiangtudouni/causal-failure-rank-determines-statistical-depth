module

public import Paid.PDROC_CalibrationRow_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem leftRead_body_macro : (basicBlock Label.leftRead).body=letterReadCode 12 := rfl
theorem rightRead_body_macro : (basicBlock Label.rightRead).body=loadSlot 7 .index++letterReadCode 13 := rfl

def rightReadResult (before : State) (base read cursor width : ℕ) (mass probability : ℚ) : State :=
  letterReadResult (loadSlotResult before base 7 .index) base read cursor width 13 mass probability

/-- The right letter really reloads header7. Thus a left-interior target
in .index cannot accidentally be reused as the next source cursor. -/
theorem rightRead_execute (input : List Cell) (before : State)
    (base read cursor width : ℕ) (mass probability : ℚ)
    (fresh : before.register .fresh=.natural base)
    (cursorLive : base+7 ∈ before.live) (cursorValue : before.heap (base+7)=.natural cursor)
    (readLive : base+9 ∈ before.live) (readValue : before.heap (base+9)=.natural read)
    (biasLive : base+13 ∈ before.live) (biasValue : before.heap (base+13)=.rational probability)
    (widthLive : base+8 ∈ before.live) (widthValue : before.heap (base+8)=.natural width)
    (cellLive : read+cursor ∈ before.live) (cellValue : before.heap (read+cursor)=.rational mass) :
    linearExecute input (basicBlock .rightRead).body before=some (rightReadResult before base read cursor width mass probability) := by
  rw [rightRead_body_macro,linearExecute_append,
    loadSlot_execute input before base 7 .index fresh cursorLive,Option.bind_some]
  apply letterRead_execute input (loadSlotResult before base 7 .index) base read cursor width 13 mass probability
  · simpa [loadSlotResult] using fresh
  · exact readLive
  · exact readValue
  · exact biasLive
  · exact biasValue
  · exact widthLive
  · exact widthValue
  · simpa [loadSlotResult] using cursorValue
  · exact cellLive
  · exact cellValue

theorem rightRead_fields (before : State) (base read cursor width : ℕ) (mass probability : ℚ)
    (cursorValue : before.heap (base+7)=.natural cursor) :
    (rightReadResult before base read cursor width mass probability).heap=before.heap ∧
    (rightReadResult before base read cursor width mass probability).live=before.live ∧
    (rightReadResult before base read cursor width mass probability).register .fresh=before.register .fresh ∧
    (rightReadResult before base read cursor width mass probability).register .index=.natural cursor ∧
    (rightReadResult before base read cursor width mass probability).register .value=.rational (mass*probability) ∧
    (rightReadResult before base read cursor width mass probability).register .flag=.natural (boundaryFlag cursor width) ∧
    (rightReadResult before base read cursor width mass probability).pc=before.pc+21 ∧
    (rightReadResult before base read cursor width mass probability).output=before.output := by
  simp only [rightReadResult,(letterRead_fields _ _ _ _ _ _ _ _).1,
    (letterRead_fields _ _ _ _ _ _ _ _).2.1,(letterRead_fields _ _ _ _ _ _ _ _).2.2.1,
    (letterRead_fields _ _ _ _ _ _ _ _).2.2.2.1,(letterRead_fields _ _ _ _ _ _ _ _).2.2.2.2.1,
    (letterRead_fields _ _ _ _ _ _ _ _).2.2.2.2.2.1,(letterRead_fields _ _ _ _ _ _ _ _).2.2.2.2.2.2.1,
    (letterRead_fields _ _ _ _ _ _ _ _).2.2.2.2.2.2.2,loadSlotResult]
  simp [cursorValue]

end PDROC.CalibrationRow
