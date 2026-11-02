module

public import RootB23_WordOddsBits_Core_001

/-! All leaves are charged to the complete original RCC.wordInput.
In particular, the false prior is derived from priorOne, not supplied. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB23.WordOddsBits

open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics
open PSTRTMLength004

theorem datum_width_le_encode (data : List Datum) (q : Rat)
    (present : Datum.rational q ∈ data) : width q ≤ (encode data).length := by
  have member : datumBits (.rational q) ∈ data.map datumBits :=
    List.mem_map.mpr ⟨.rational q,present,rfl⟩
  have small := List.le_sum_of_mem member
  have length := encode_length data
  dsimp only [datumBits] at small
  unfold width
  omega

theorem word_datum_width_le (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) (q : Rat)
    (present : Datum.rational q ∈ rawExperiment E ++ [.rational p] ++ rawWord E word) :
    width q ≤ (wordInput E p word).length :=
  datum_width_le_encode _ q present

theorem priorOne_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width E.priorOne ≤ (wordInput E p word).length := by
  apply word_datum_width_le E p word
  simp [rawExperiment]

theorem channel_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord)
    (truth : Bool) (symbol : Fin E.alphabetSize) :
    width (E.channel truth symbol) ≤ (wordInput E p word).length := by
  apply word_datum_width_le E p word
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  unfold rawExperiment
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨truth,?_,?_⟩
  · cases truth <;> simp
  · exact List.mem_map.mpr ⟨symbol,List.mem_finRange symbol,rfl⟩

theorem target_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width p ≤ (wordInput E p word).length := by
  apply word_datum_width_le E p word
  simp

theorem prior_true_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width (E.prior true) ≤ (wordInput E p word).length := by
  change width E.priorOne ≤ _
  exact priorOne_width_le_input E p word

theorem prior_false_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width (E.prior false) ≤ 2*(wordInput E p word).length := by
  change width (1-E.priorOne) ≤ _
  exact (one_sub_width_le E.priorOne).trans
    (Nat.mul_le_mul_left 2 (priorOne_width_le_input E p word))

theorem lower_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width (p/(1-p)) ≤ 3*(wordInput E p word).length := by
  have hp := target_width_le_input E p word
  have hc := one_sub_width_le p
  have hd := div_width_le p (1-p)
  omega

theorem upper_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width ((1-p)/p) ≤ 3*(wordInput E p word).length := by
  have hp := target_width_le_input E p word
  have hc := one_sub_width_le p
  have hd := div_width_le (1-p) p
  omega

end RootB23.WordOddsBits
