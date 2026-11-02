module
public import Common.PSTR_TM_NativeEventSerial_212
public import Common.PSTR_TM_Arithmetic_008

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeFieldBits219
open PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMLength004
variable {I : Instance}

/-! Proof-only support for the ORIGINAL native controller input budget.
These are encoded bit widths, never numerical alphabet/clock bounds by a
structural machine Word. No certificate or statistic enters any input. -/

private theorem datumBits_le_sum_of_mem (data : List Datum) (value : Datum) (hv : value ∈ data) :
    datumBits value ≤ (data.map datumBits).sum := by
  induction data with
  | nil => simp at hv
  | cons head later ih =>
    rcases List.mem_cons.mp hv with hh | ht
    · subst value
      simp only [List.map_cons,List.sum_cons]
      omega
    · have hh := ih ht
      simp only [List.map_cons,List.sum_cons]
      omega

theorem datumBits_le_encode_of_mem (data : List Datum) (value : Datum) (hv : value ∈ data) :
    datumBits value ≤ (encode data).length := by
  rw [encode_length]
  have hs := datumBits_le_sum_of_mem data value hv
  omega

theorem preparation_datumBits_le (input : StatisticalInput I) (C : Contract I) (budget : Rat)
    (value : Datum) (hv : value ∈ rawInstance input ++ rawContract C ++ [.rational budget]) :
    datumBits value ≤ (preparationInput input C budget).length :=
  datumBits_le_encode_of_mem _ value hv

theorem alphabet_datum_mem (input : StatisticalInput I) (i : I.Stage) :
    .natural (input.experiment i).alphabetSize ∈ rawInstance input := by
  have hx : .natural (input.experiment i).alphabetSize ∈ rawExperiment (input.experiment i) := by
    simp [rawExperiment]
  have he : .natural (input.experiment i).alphabetSize ∈
      (List.finRange I.stageCount).flatMap (fun stage => rawExperiment (input.experiment stage)) := by
    apply List.mem_flatMap.mpr
    exact ⟨i,List.mem_finRange (n := I.stageCount) i,hx⟩
  simp only [rawInstance,List.mem_append]
  tauto

/-- Alphabet values can greatly exceed any structural Word. Their actual
original encoded widths are nevertheless bounded by preparationInput. -/
theorem alphabet_bits_le_preparation (input : StatisticalInput I) (C : Contract I) (budget : Rat)
    (i : I.Stage) : natBits (input.experiment i).alphabetSize ≤ (preparationInput input C budget).length := by
  have hi := alphabet_datum_mem input i
  have hm : .natural (input.experiment i).alphabetSize ∈
      rawInstance input ++ rawContract C ++ [.rational budget] := by
    simp only [List.mem_append]
    tauto
  have hb := preparation_datumBits_le input C budget _ hm
  change 2*natBits (input.experiment i).alphabetSize+2 ≤ _ at hb
  omega

theorem stage_bits_le (i : I.Stage) : natBits i.val ≤ natBits I.stageCount := by
  have hi : i.val < I.stageCount := i.isLt
  exact PSTRTMArithmetic008.natBits_mono (Nat.le_of_lt hi)

theorem tool_bits_le (r : I.Tool) : natBits r.val ≤ natBits I.toolCount :=
  PSTRTMArithmetic008.natBits_mono (Nat.le_of_lt r.isLt)

theorem prefix_observation_bits_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (budget : Rat) (i : I.Stage) (symbol : Nat) (hm : .observation i symbol ∈ s.history) :
    natBits symbol ≤ (preparationInput input C budget).length := by
  have ho : symbol ∈ historyObservations s.history i := by
    unfold historyObservations
    apply List.mem_filterMap.mpr
    exact ⟨.observation i symbol,hm,by simp [eventObservation]⟩
  have halpha := prefix_historyObservation_alphabet input C mode accounting policy seed truth tapes hp i symbol ho
  exact (PSTRTMArithmetic008.natBits_mono (Nat.le_of_lt halpha)).trans
    (alphabet_bits_le_preparation input C budget i)

theorem prefix_eventSerial_bits_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (event : VisibleEvent I) (hm : event ∈ s.history) :
    natBits (PSTRTMNativeEventSerial212.eventSerial event) ≤ natBits s.clock :=
  PSTRTMArithmetic008.natBits_mono
    (PSTRTMNativeEventSerial212.prefix_eventSerial_le input C mode accounting policy seed truth tapes hp event hm)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeFieldBits219
