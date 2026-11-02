module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Statistics.PDROC_Lower_001
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open PaperProofs.Paid

namespace PDROC

theorem auxiliaryRecord_wordSignedScore (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) :
    wordSignedScore P.binarySymmetric
      ⟨record.observations.length, fun k => record.observations[k.val]⟩ = record.score := by
  unfold wordSignedScore AuxiliaryRecord.score
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map record.observations (fun symbol : Fin 2 => if symbol.val = 1 then (1 : ℤ) else -1)

theorem auxiliaryPosteriorLevels (P : PaperProofs.Paid.Parameters) : P.AuxiliaryPosteriorLevels := by
  intro record
  rw [wordPosteriorError_eq_endpoint, auxiliaryRecord_wordSignedScore]
  rfl

end PDROC

