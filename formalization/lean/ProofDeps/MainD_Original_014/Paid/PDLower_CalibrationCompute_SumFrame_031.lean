module

public import Paid.PDLower_CalibrationCompute_SumCell_029

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem RowAt.storeResult {before : State} {read : ℕ} {row : Array ℚ}
    (represented : RowAt before read row) (base offset : ℕ) (source : Register)
    (separate : ∀ index < row.size,read+index ≠ base+offset) :
    RowAt (storeSlotResult before base offset source) read row := by
  constructor
  · intro index inside
    exact Finset.mem_insert_of_mem (represented.live index inside)
  · intro index inside
    simpa only [storeSlotResult,Function.update_apply,separate index inside,↓reduceIte] using
      represented.value index inside

theorem incrementSlot_row {before : State} {read : ℕ} {row : Array ℚ}
    (represented : RowAt before read row) (base offset value : ℕ)
    (separate : ∀ index < row.size,read+index ≠ base+offset) :
    RowAt (incrementSlotResult before base offset value) read row := by
  have unchanged : RowAt (incrementSlotLoaded before base offset value) read row :=
    ⟨represented.live,represented.value⟩
  exact unchanged.storeResult base offset .index separate

theorem sumCell_row {before : State} {base : ℕ} {header : Header} (row : Array ℚ)
    (represented : RowAt before header.readBase row) (readOutside : base+16 ≤ header.readBase) :
    RowAt (sumCellResult before base header.readBase header.cursor header.q (row.getD header.cursor 0))
      header.readBase row := by
  let d := sumCellLeadResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)
  have unchanged : RowAt d header.readBase row := ⟨represented.live,represented.value⟩
  have afterSum : RowAt (storeSlotResult d base 11 .value) header.readBase row :=
    unchanged.storeResult base 11 .value (by intros; omega)
  exact incrementSlot_row afterSum base 7 header.cursor (by intros; omega)

theorem sumCell_fresh (before : State) (base read cursor : ℕ) (q value : ℚ) :
    (sumCellResult before base read cursor q value).register .fresh = before.register .fresh := by
  simp [sumCellResult,incrementSlot_fresh,storeSlotResult,sumCellLeadResult,loadSlotResult]

theorem sumCell_output (before : State) (base read cursor : ℕ) (q value : ℚ) :
    (sumCellResult before base read cursor q value).output = before.output := rfl

theorem sumCell_pc (before : State) (base read cursor : ℕ) (q value : ℚ) :
    (sumCellResult before base read cursor q value).pc = before.pc+20 := by
  simp [sumCellResult,incrementSlot_pc,storeSlotResult,sumCellLeadResult,loadSlotResult,Nat.add_assoc]

end PDLower.CalibrationCompute
