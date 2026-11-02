module

public import PaperProofs.Common.ReferenceCostAsymptotics

/-!
The infinite-rank part of B12 for the independently defined full-policy
penalty value. The actual original reference gives zero observations and
zero failure probability; its correction fees are omitted only by the
original penalty relaxation, not by changing the native monetary ledger.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Structure

variable {I : Instance}

theorem availablePenaltyValue_zero_of_infiniteRank (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (htop : errorRank I.compatibility available = ⊤)
    (penalty : ℝ≥0∞) :
    availablePenaltyValue input C accounting available penalty = 0 := by
  have h := availablePenaltyValue_le_policy input C accounting available penalty
    (Measure.dirac ())
    (referenceAvailableUncappedPolicy input C hearly accounting available (1 / 4) none)
  change _ ≤ penaltyObjective input C .uncapped accounting
    (referenceRule input available (1 / 4) none) (Measure.dirac ()) penalty at h
  rw [penaltyObjective,
    referenceExpectedObservationBill_infiniteRank input C hearly accounting available
      (1 / 4) (by norm_num) (by norm_num) htop none (Measure.dirac ()),
    referenceRisk_zero_of_infinite_rank input C hearly accounting available
      (1 / 4) (by norm_num) (by norm_num) htop none (Measure.dirac ()),
    mul_zero, add_zero] at h
  exact le_antisymm h bot_le

end PaperProofs.Common.Native

namespace PaperProofs.Common

open PaperProofs.Structure

variable {I : Instance}

theorem StatisticalInput.healthyPenalty_zero_of_infiniteRank (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool)
    (htop : errorRank (I.compatibility.drop next) available = ⊤) (penalty : ℝ≥0∞) :
    input.healthyPenalty next available penalty = 0 := by
  exact Native.availablePenaltyValue_zero_of_infiniteRank (input.freshSuffix next)
    (currentRelaxedContract (I.freshSuffix next)) rfl
    (zeroNormalAccounting (I.freshSuffix next)) available htop penalty

theorem StatisticalInput.healthyPenaltyReal_zero_of_infiniteRank (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool)
    (htop : errorRank (I.compatibility.drop next) available = ⊤) (price : ℝ) :
    input.healthyPenaltyReal next available price = 0 := by
  rw [StatisticalInput.healthyPenaltyReal,
    input.healthyPenalty_zero_of_infiniteRank next available htop, ENNReal.toReal_zero]

end PaperProofs.Common
