module

public import RootB234_PrepEntry_StageChannelsPublic_069
public import RootB23_WordOddsBits_Core_001
public import RootB234_ChannelWidth_Prefix002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.ChannelWidth.Public

open PaperProofs.Common.Native PSTRWordBool RationalControllerComputation
open PaperProofs.Statistics

/-- Every original experiment, and every truncation of the actual reverse order. -/
theorem reverse_prefix_fieldSize_le (E : BinaryExperiment) (k : Nat) :
    RatInput.Encoder.fieldSize
      ((((List.finRange E.alphabetSize).reverse.take k).map
        (fun y => |E.channel true y-E.channel false y|)).sum) ≤
      4*(((rawExperiment E).flatMap encodeDatum).length+1) :=
  reversePrefix_linear E k

theorem channel_drift_fieldSize_le (E : BinaryExperiment) :
    RatInput.Encoder.fieldSize E.channelDriftLower ≤
      16*(((rawExperiment E).flatMap encodeDatum).length+1) :=
  channelDriftLower_linear E

/-- Constants precede all original inputs; k has no range premise. -/
theorem reverse_prefix_polynomial :
    ∃ c d : Nat,0<c ∧ 0<d ∧ ∀ (E : BinaryExperiment) (k : Nat),
      RatInput.Encoder.fieldSize
        ((((List.finRange E.alphabetSize).reverse.take k).map
          (fun y => |E.channel true y-E.channel false y|)).sum) ≤
        c*(((rawExperiment E).flatMap encodeDatum).length+1)^d := by
  refine ⟨4,1,by decide,by decide,?_⟩
  intro E k
  simpa only [pow_one] using reverse_prefix_fieldSize_le E k

theorem channel_drift_polynomial :
    ∃ c d : Nat,0<c ∧ 0<d ∧ ∀ E : BinaryExperiment,
      RatInput.Encoder.fieldSize E.channelDriftLower ≤
        c*(((rawExperiment E).flatMap encodeDatum).length+1)^d := by
  refine ⟨16,1,by decide,by decide,?_⟩
  intro E
  simpa only [pow_one] using channel_drift_fieldSize_le E

/-- One common pair c=16,d=1 bounds both fields on the same original material. -/
theorem shared_polynomial :
    ∃ c d : Nat,0<c ∧ 0<d ∧
      (∀ (E : BinaryExperiment) (k : Nat),
        RatInput.Encoder.fieldSize
          ((((List.finRange E.alphabetSize).reverse.take k).map
            (fun y => |E.channel true y-E.channel false y|)).sum) ≤
          c*(((rawExperiment E).flatMap encodeDatum).length+1)^d) ∧
      (∀ E : BinaryExperiment,RatInput.Encoder.fieldSize E.channelDriftLower ≤
        c*(((rawExperiment E).flatMap encodeDatum).length+1)^d) := by
  refine ⟨16,1,by decide,by decide,?_,?_⟩
  · intro E k
    have bound := reverse_prefix_fieldSize_le E k
    simp only [pow_one]
    omega
  · intro E
    simpa only [pow_one] using channel_drift_fieldSize_le E

end RootB234.ChannelWidth.Public
