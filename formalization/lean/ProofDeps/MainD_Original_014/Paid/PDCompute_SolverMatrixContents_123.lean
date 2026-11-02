module

public import Paid.PDCompute_SolverScanChoice_105

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- Actual saved machine arguments and counters used by matrix113.
This invariant contains no table, argmin or run-existence field. -/
structure MatrixContents (P : Parameters) (values : ℕ → Cell) (fee penalty : ℚ)
    (n k source row column : ℕ) : Prop where
  sourceValue : values 0=.natural source
  penaltyValue : values 2=.rational penalty
  nValue : values 3=.natural n
  kValue : values 4=.natural k
  feeValue : values 5=.rational fee
  lastValue : values 6=.natural P.certificate.M
  rowValue : values 19=.natural row
  columnValue : values 20=.natural column

theorem MatrixContents.preserve {P : Parameters} {values next : ℕ → Cell} {fee penalty : ℚ}
    {n k source row column : ℕ} (contents : MatrixContents P values fee penalty n k source row column)
    (keep : ∀ slot,slot < 7 ∨ slot=19 ∨ slot=20 → next slot=values slot) :
    MatrixContents P next fee penalty n k source row column := by
  exact ⟨(keep 0 (by decide)).trans contents.sourceValue,(keep 2 (by decide)).trans contents.penaltyValue,
    (keep 3 (by decide)).trans contents.nValue,(keep 4 (by decide)).trans contents.kValue,
    (keep 5 (by decide)).trans contents.feeValue,(keep 6 (by decide)).trans contents.lastValue,
    (keep 19 (by decide)).trans contents.rowValue,(keep 20 (by decide)).trans contents.columnValue⟩

theorem MatrixContents.column {P : Parameters} {values : ℕ → Cell} {fee penalty : ℚ}
    {n k source row oldColumn : ℕ} (contents : MatrixContents P values fee penalty n k source row oldColumn) (column : ℕ) :
    MatrixContents P (Function.update values 20 (.natural column)) fee penalty n k source row column :=
  ⟨contents.sourceValue,contents.penaltyValue,contents.nValue,contents.kValue,contents.feeValue,contents.lastValue,contents.rowValue,rfl⟩

theorem MatrixContents.row {P : Parameters} {values : ℕ → Cell} {fee penalty : ℚ}
    {n k source oldRow column : ℕ} (contents : MatrixContents P values fee penalty n k source oldRow column) (row : ℕ) :
    MatrixContents P (Function.update values 19 (.natural row)) fee penalty n k source row column :=
  ⟨contents.sourceValue,contents.penaltyValue,contents.nValue,contents.kValue,contents.feeValue,contents.lastValue,rfl,contents.columnValue⟩

def SavedInputValues (before after : ℕ → Cell) : Prop := ∀ slot,slot < 7 → after slot=before slot

theorem SavedInputValues.refl (values : ℕ → Cell) : SavedInputValues values values := fun _ _ => rfl

theorem SavedInputValues.trans {before middle after : ℕ → Cell} (first : SavedInputValues before middle)
    (later : SavedInputValues middle after) : SavedInputValues before after :=
  fun slot inside => (later slot inside).trans (first slot inside)

theorem SavedInputValues.update (values : ℕ → Cell) (slot : ℕ) (value : Cell) (outside : 7 ≤ slot) :
    SavedInputValues values (Function.update values slot value) := by
  intro index inside
  exact Function.update_of_ne (by omega : index ≠ slot) _ _

end PDCompute.Solver
