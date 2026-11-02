module

public import Paid.PDROC_CalibrationRow_ScatterOperands_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- The actual pre-store add result is the first-letter transient.
Its catalogue membership is derived locally from the original entry
and frozen leftStore_correct, not supplied as a successful-run oracle. -/
theorem leftStore_sum_catalog (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (before : State)
    (data : ScatterData P base level clock cursor read write before)
    (inside : cursor < 2 * level + 1) (levelBound : level ≤ P.certificate.M + 1)
    (index : before.register .index = .natural (walkMove level ⟨cursor, inside⟩ (0 : Fin 2)).val)
    (value : before.register .value = .rational ((P.walkRow level true clock).getD cursor 0 * (1 / 2 - P.certificate.gamma))) :
    Catalog P base level clock
      (.rational ((rowScatterPrefix P level (P.walkRow level true clock) cursor).getD
          (walkMove level ⟨cursor, inside⟩ (0 : Fin 2)).val 0 +
        (P.walkRow level true clock).getD cursor 0 * (1 / 2 - P.certificate.gamma))) := by
  let target := walkMove level ⟨cursor, inside⟩ (0 : Fin 2)
  let previous := rowScatterPrefix P level (P.walkRow level true clock) cursor
  let amount := (P.walkRow level true clock).getD cursor 0 * (1 / 2 - P.certificate.gamma)
  have correct := leftStore_correct input P base level clock cursor read write before data inside levelBound index value
  have actual := correct.2.writeRow.value target.val
    (by simpa only [rowLeftPrefix, PDROC.endpointArrayBump_size, rowScatterPrefix_size] using target.isLt)
  change (scatterStoreResult before base write target.val (previous.getD target.val 0) amount).heap
    (write + target.val) = .rational ((rowLeftPrefix P level clock cursor inside).getD target.val 0) at actual
  rw [(scatterStore_fields before base write target.val (previous.getD target.val 0) amount).1,
    Function.update_self] at actual
  have same := Cell.rational.inj actual
  change Catalog P base level clock (.rational (previous.getD target.val 0 + amount))
  rw [same]
  exact Catalog.afterLeft cursor inside target

/-- The right pre-store add sees the already updated first-left row,
including equal absorbing targets. It is the next complete partial row. -/
theorem rightStore_sum_catalog (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (inside : cursor < 2 * level + 1) (before : State)
    (data : ScatterLeftData P base level clock cursor read write inside before)
    (levelBound : level ≤ P.certificate.M + 1)
    (index : before.register .index = .natural (walkMove level ⟨cursor, inside⟩ (1 : Fin 2)).val)
    (value : before.register .value = .rational ((P.walkRow level true clock).getD cursor 0 * (1 / 2 + P.certificate.gamma))) :
    Catalog P base level clock
      (.rational ((rowLeftPrefix P level clock cursor inside).getD
          (walkMove level ⟨cursor, inside⟩ (1 : Fin 2)).val 0 +
        (P.walkRow level true clock).getD cursor 0 * (1 / 2 + P.certificate.gamma))) := by
  let target := walkMove level ⟨cursor, inside⟩ (1 : Fin 2)
  let previous := rowLeftPrefix P level clock cursor inside
  let amount := (P.walkRow level true clock).getD cursor 0 * (1 / 2 + P.certificate.gamma)
  have correct := rightStore_correct input P base level clock cursor read write inside before data levelBound index value
  have actual := correct.2.writeRow.value target.val
    (by simpa only [rowScatterPrefix_size] using target.isLt)
  change (scatterStoreResult before base write target.val (previous.getD target.val 0) amount).heap
    (write + target.val) = .rational
      ((rowScatterPrefix P level (P.walkRow level true clock) (cursor + 1)).getD target.val 0) at actual
  rw [(scatterStore_fields before base write target.val (previous.getD target.val 0) amount).1,
    Function.update_self] at actual
  have same := Cell.rational.inj actual
  change Catalog P base level clock (.rational (previous.getD target.val 0 + amount))
  rw [same]
  exact Catalog.partialRow (cursor + 1) (by omega) target

end PDROC.CalibrationRow.ScatterOperands
