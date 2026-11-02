module

public import PaperProofs.Retained.PRet_JointCharges_075
public import PaperProofs.Retained.PRet_OutputCompletion_049
public import PaperProofs.Common.NativeHeadAccounting

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshNoEntry085

open Common Common.Native PRetAmbientComparator073 PRetJointCharges075 PRetOutputCompletion049
open scoped ENNReal

variable {Physical Ambient : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Nonarrival at a genuine second stage prevents actual ordinary
completion, hence fails the ORIGINAL joint-matching fresh predicate too.
No physical repair success or finite observation cost is assumed. -/
theorem no_entry_jointFailure (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Seed)
    (embed : Physical.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (second : Physical.Stage) (hsecond : second.val = 1) (sample : Seed × input.World)
    (hnever : ∀ n, (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample n).cursor ≠ 1) :
    ¬ jointSuccess input embed old source.rule sample := by
  rintro ⟨n, _, hf, _, _⟩
  have hall := run_finished_allWritten input (freshContract Physical) .uncapped (zeroNormalAccounting Physical)
    source.rule source.legal sample n hf
  have hc := run_cursor_zero_of_no_stage_one input (freshContract Physical) .uncapped (zeroNormalAccounting Physical)
    source.rule source.legal sample hnever n
  have hinv := run_cursorInvariant input (freshContract Physical) .uncapped (zeroNormalAccounting Physical)
    source.rule source.legal sample n
  have hw := hinv.future_written second (by rw [hc, hsecond]; exact Nat.zero_lt_one)
  exact hall second hw

/-- The actual single failure penalty pays any bounded local continuation
weight on the entire no-entry complement, including finite-paid abandon and
nonreturn. All bought observations remain in the same actual charge. -/
theorem no_entry_charge_lower (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Seed)
    (embed : Physical.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (head second : Physical.Stage) (hhead : head.val = 0) (hsecond : second.val = 1)
    (sample : Seed × input.World)
    (hnever : ∀ n, (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample n).cursor ≠ 1)
    (weight penalty : ℝ≥0∞) (hweight : weight ≤ penalty) :
    (input.experiment head).observationCharge (headExitStop input head source.rule sample.1 (worldTapes input sample.2 head)) + weight ≤
      jointCharge input embed old source.rule penalty sample := by
  classical
  have hf := no_entry_jointFailure input source embed old second hsecond sample hnever
  unfold jointCharge
  simp only [hf, ↓reduceIte]
  exact add_le_add (nativeHead_observationCharge_le input (freshContract Physical) (zeroNormalAccounting Physical)
    source.rule head hhead sample) hweight

end PaperProofs.Retained.PRetFreshNoEntry085
