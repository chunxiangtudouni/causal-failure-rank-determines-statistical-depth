module

public import PaperProofs.Statistics.PosteriorSPRT
public import PaperProofs.Statistics.LocalLower

/-!
The local price theorem for the original finite full-support binary
experiment and the actual infimum over causal privately randomized tests.
The posterior-SPRT upper guarantee and stopped-information lower bound
are both proved in the imported modules; no pending statistical property
is retained as a premise here.
-/

@[expose] public section

namespace PaperProofs.Statistics.BinaryExperiment

theorem localLogarithmicPrice (E : BinaryExperiment) : E.LocalLogarithmicPrice :=
  E.localLogarithmicPrice_of_sprt E.posteriorSPRTGuarantee

theorem globalLogarithmicEnvelope (E : BinaryExperiment) : E.GlobalLogarithmicEnvelope :=
  E.globalLogarithmicEnvelope_of_sprt E.posteriorSPRTGuarantee

theorem localValue_log_upper (E : BinaryExperiment) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 4 ≤ t →
      E.localValueReal t ≤ E.coefficient * Real.log t + C :=
  E.localValue_log_upper_of_sprt E.posteriorSPRTGuarantee

end PaperProofs.Statistics.BinaryExperiment
