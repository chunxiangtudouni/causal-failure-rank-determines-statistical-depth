module

public import Paid.PDROC_BitVM_Common_IO_Wide_Fields_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

/-- A proof bound on actual paths; not a width argument to the finite
program. This quantity is invariant when an emitted block is moved from
the remaining real input to the real cursor gap/output rows. -/
def scanEnvelope (gap rows width : Nat) : Nat := gap + rows + 2 * width + 2

theorem blockCost_coarse (block : FieldBlock) (gap rows : Nat) :
    blockCost block gap rows ≤ 128 * (scanEnvelope gap rows (blockWord block).length)^2 := by
  let f := block.fixed.length
  let n := block.digits.length
  let h := scanEnvelope gap rows (blockWord block).length
  have width : (blockWord block).length = f + (2 * n + 1) := by
    simp only [blockWord, List.length_append, rawField_length]
    rfl
  have hvalue : h = gap + rows + 2 * (f + (2 * n + 1)) + 2 := by
    simp only [h, scanEnvelope, width]
  have hpositive : 2 ≤ h := by omega
  have fixedFirst : f ≤ h := by omega
  have fixedSecond : 2 * gap + 2 * rows + 2 * f + 6 ≤ 3 * h := by omega
  have fixedProduct := Nat.mul_le_mul fixedFirst fixedSecond
  have fixedBound : fixedCost f gap rows ≤ 3 * h^2 + 1 := by
    unfold fixedCost
    nlinarith [fixedProduct]
  have natFirst : n + 1 ≤ h := by omega
  have natSecond : gap + f + (rows + f) + n + 2 ≤ h := by omega
  have natProduct := Nat.mul_le_mul natFirst natSecond
  have natBound : natFieldCost n (gap + f) (rows + f) ≤ 64 * h^2 := by
    have bound := natFieldCost_coarse n (gap + f) (rows + f)
    nlinarith [natProduct]
  change fixedCost f gap rows + natFieldCost n (gap + f) (rows + f) ≤ 128 * h^2
  nlinarith

/-- Coarse quadratic work per field; the number of fields is ten for
the original raw6 stream. No recurrence multiplies bit bounds at runtime. -/
theorem fieldsCost_coarse (blocks : List FieldBlock) (gap rows : Nat) :
    fieldsCost blocks gap rows ≤
      256 * blocks.length * (scanEnvelope gap rows (fieldsWord blocks).length)^2 := by
  induction blocks generalizing gap rows with
  | nil => simp [fieldsCost]
  | cons block rest ih =>
    let h := scanEnvelope gap rows (fieldsWord (block :: rest)).length
    let b := scanEnvelope gap rows (blockWord block).length
    have lengths : (fieldsWord (block :: rest)).length =
        (blockWord block).length + (fieldsWord rest).length := by simp [fieldsWord]
    have hpositive : 2 ≤ h := by simp only [h, scanEnvelope]; omega
    have b_le : b ≤ h := by simp only [b, h, scanEnvelope, lengths]; omega
    have square : b^2 ≤ h^2 := by nlinarith
    have blockBound := blockCost_coarse block gap rows
    have firstBound : blockCost block gap rows + 1 ≤ 256 * h^2 := by
      change blockCost block gap rows ≤ 128 * b^2 at blockBound
      nlinarith
    have same : scanEnvelope (gap + (blockWord block).length) (rows + (blockWord block).length)
        (fieldsWord rest).length = h := by
      simp only [h, scanEnvelope, lengths]
      omega
    have tailBound := ih (gap + (blockWord block).length) (rows + (blockWord block).length)
    rw [same] at tailBound
    change blockCost block gap rows + 1 +
        fieldsCost rest (gap + (blockWord block).length) (rows + (blockWord block).length) ≤
      256 * (rest.length + 1) * h^2
    calc
      _ ≤ 256 * h^2 + 256 * rest.length * h^2 := Nat.add_le_add firstBound tailBound
      _ = _ := by ring

end PDROC.BitVM.Common.IO.Wide
