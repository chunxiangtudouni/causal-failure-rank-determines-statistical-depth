module

public import Paid.PDROC_CalibrationRow_ScatterOperands_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem small_natural_catalog (P : Parameters) (base level clock number : ℕ)
    (bound : number ≤ rowWidth P.certificate.M + 16) :
    Catalog P base level clock (.natural number) := by
  apply Catalog.natural
  unfold resultBase
  omega

theorem offset_catalog (P : Parameters) (base level clock offset : ℕ) (bound : offset ≤ 16) :
    Catalog P base level clock (.natural offset) := by
  apply small_natural_catalog
  omega

theorem header_address_catalog (P : Parameters) (base level clock offset : ℕ) (bound : offset ≤ 16) :
    Catalog P base level clock (.natural (base + offset)) := by
  apply Catalog.natural
  unfold resultBase
  omega

theorem read_address_catalog (P : Parameters) (base level clock read write query : ℕ)
    (buffers : Buffers base P.certificate.M read write) (inside : query < rowWidth P.certificate.M) :
    Catalog P base level clock (.natural (read + query)) := by
  apply Catalog.natural
  rcases buffers with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp only [firstRow, secondRow, resultBase] <;> omega

theorem write_address_catalog (P : Parameters) (base level clock read write query : ℕ)
    (buffers : Buffers base P.certificate.M read write) (inside : query < rowWidth P.certificate.M) :
    Catalog P base level clock (.natural (write + query)) := by
  apply Catalog.natural
  rcases buffers with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp only [firstRow, secondRow, resultBase] <;> omega

theorem read_pointer_catalog (P : Parameters) (base level clock read write : ℕ)
    (buffers : Buffers base P.certificate.M read write) : Catalog P base level clock (.natural read) := by
  simpa only [Nat.add_zero] using read_address_catalog P base level clock read write 0 buffers
    (by unfold rowWidth; omega)

theorem write_pointer_catalog (P : Parameters) (base level clock read write : ℕ)
    (buffers : Buffers base P.certificate.M read write) : Catalog P base level clock (.natural write) := by
  simpa only [Nat.add_zero] using write_address_catalog P base level clock read write 0 buffers
    (by unfold rowWidth; omega)

theorem width_naturals_catalog (P : Parameters) (base level clock : ℕ)
    (levelBound : level ≤ P.certificate.M + 1) (number : ℕ) (bound : number ≤ max (2 * level + 1) 2) :
    Catalog P base level clock (.natural number) := by
  apply small_natural_catalog
  have width := activeWidth_le P.certificate.M level levelBound
  omega

end PDROC.CalibrationRow.ScatterOperands
