module

public import PaperProofs.Statistics.StoppedWald

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Statistics.PStarMainSeedInformation001

open MeasureTheory
open scoped ENNReal

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The original stopped KL identity on ANY private-seed universe. The
finite-ET premise is exactly the original identity's two-truth premise;
all measurability and stopping properties stay in the original test type. -/
theorem stoppedInformationIdentity_any_seed (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    Measurable (E.stoppedTranscript test) ∧
      ∀ x, InformationTheory.klDiv (E.transcriptLaw ν test x) (E.transcriptLaw ν test (!x)) =
        ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x := by
  refine ⟨E.measurable_stoppedTranscript test, ?_⟩
  intro x
  rw [E.transcriptLaw_klDiv_eq_ofReal_stoppedSum ν test x hfinite,
    E.integral_stoppedSum_wald ν test x (hfinite x),
    ENNReal.ofReal_mul (E.divergence_pos x).le]
  congr 1
  exact ENNReal.ofReal_toReal (hfinite x)

/-- Data processing for the ACTUAL possibly non-MAP decision, with the
same arbitrary seed, law, test and original finite-ET premise. -/
theorem stoppedDecisionInformationBound_any_seed (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    ∀ x, InformationTheory.klDiv (E.decisionLaw ν test x) (E.decisionLaw ν test (!x)) ≤
      ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x := by
  intro x
  have hinfo := stoppedInformationIdentity_any_seed E ν test hfinite
  have hkl := InformationTheory.klDiv_map_le (E.transcriptLaw ν test x)
    (E.transcriptLaw ν test (!x)) (E.measurable_decodedStoppedDecision test)
  rw [E.transcriptLaw_decodedDecision ν test x (hfinite x),
    E.transcriptLaw_decodedDecision ν test (!x) (hfinite (!x)), hinfo.2 x] at hkl
  exact hkl

end PaperProofs.Statistics.PStarMainSeedInformation001
