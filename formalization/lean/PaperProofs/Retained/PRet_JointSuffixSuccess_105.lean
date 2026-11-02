module

public import PaperProofs.Retained.PRet_JointSuffixSuccess_104

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetJointSuffixSuccess105

open Common Common.Native PRetAmbientComparator073 PRetJointSuffixSuccess104

variable {I Ambient : Instance}

/-- Success transports through the actual all-clock continuation view,
with the same old obligations and a single original failure event. -/
theorem jointSuccess_of_views {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I) (first : ℕ)
    (parent : Policy input (freshContract I) .uncapped (zeroNormalAccounting I) Seed)
    (child : Policy (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) Seed)
    (sample : Seed × input.World) (before : List (VisibleEvent I))
    (embed : I.Stage → Ambient.Stage) (base old : Finset Ambient.Stage)
    (hbase : base ⊆ old)
    (hallBefore : ∀ stage : I.Stage, stage.val < first → historyWritten before stage ≠ none)
    (hold : ∀ (stage : I.Stage) (bit : Bool), stage.val < first →
      historyWritten before stage = some bit → bit ≠ input.truthAt sample.2 stage → embed stage ∈ old)
    (hclean : ∀ stage, historyWrite before (I.freshStageLift first stage) = none)
    (start : ℕ)
    (views : ∀ k, ReferenceSuffixView I first before
      (run input (freshContract I) .uncapped (zeroNormalAccounting I) parent.rule sample (start + k))
      (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped (zeroNormalAccounting (I.freshSuffix first))
        child.rule (sample.1, referenceSuffixWorld input first sample.2) k))
    (hs : jointSuccess (input.freshSuffix first) (fun stage => embed (I.freshStageLift first stage)) old child.rule
      (sample.1, referenceSuffixWorld input first sample.2)) :
    jointSuccess input embed base parent.rule sample := by
  obtain ⟨k, hh, hf, ha, hm⟩ := hs
  obtain ⟨m, _, hp⟩ := run_has_prefix input (freshContract I) .uncapped (zeroNormalAccounting I) parent.rule parent.legal sample (start + k)
  obtain ⟨n, _, hc⟩ := run_has_prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) child.rule child.legal (sample.1, referenceSuffixWorld input first sample.2) k
  exact ⟨start + k, completed_prefixes_joint input first parent.rule child.rule sample before embed base old
    hbase hallBefore hold hclean hp hc (views k) hh hf ha hm⟩

end PaperProofs.Retained.PRetJointSuffixSuccess105
