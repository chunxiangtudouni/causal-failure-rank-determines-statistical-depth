module

public import B23_4_RatWordPrep_SeqCmp_WordFinishOperands_132

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

theorem fields_length_le_encode (data : List Datum) :
    (data.flatMap encodeDatum).length≤(encode data).length := by
  simp only [encode,List.length_append,List.length_singleton]
  omega

theorem datum_count_le_fields (data : List Datum) : data.length≤(data.flatMap encodeDatum).length := by
  induction data with
  | nil => rfl
  | cons value data ih =>
    have positive := PSTRTMLength004.datumBits_pos value
    simp only [List.length_cons,List.flatMap_cons,List.length_append,PSTRTMLength004.encodeDatum_length]
    omega

theorem rational_fields_map (values : List Rat) :
    (values.map Datum.rational).flatMap encodeDatum=Channels.fields values := by
  rw [List.flatMap_map]
  rfl

/-- Canonical qualified packets remain linear in the original rational
fields. This charges table buffers to original input, not old work mass. -/
theorem packets_le_fields (values : List Rat) (tail : List Bool) :
    (PacketLists.rats values tail).length≤2*(Channels.fields values).length+tail.length := by
  induction values with
  | nil => simp only [PacketLists.rats,List.foldr_nil,Channels.fields,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons x values ih =>
    change (RatInput.Encoder.packet x (PacketLists.rats values tail)).length≤_
    rw [RatInput.Encoder.packet_length,RootB23.WordOddsBits.ratInput_fieldSize_eq]
    have fieldsStep : (Channels.fields (x::values)).length=
        (encodeDatum (.rational x)).length+(Channels.fields values).length := by
      simp only [Channels.fields,List.flatMap_cons,List.length_append]
    rw [fieldsStep]
    change 2*RootB23.WordOddsBits.width x+6+(PacketLists.rats values tail).length≤
      2*((encodeDatum (.rational x)).length+(Channels.fields values).length)+tail.length
    rw [PSTRTMLength004.encodeDatum_rational_length]
    change 2*RootB23.WordOddsBits.width x+6+(PacketLists.rats values tail).length≤
      2*(2*RootB23.WordOddsBits.width x+4+(Channels.fields values).length)+tail.length
    omega

theorem experiment_channels (E : BinaryExperiment) :
    rawExperiment E=[.natural E.alphabetSize,.rational E.priorOne,.rational E.observationFee]++
      (Channels.channelValues E).map Datum.rational := by
  simp only [rawExperiment,Channels.channelValues,List.map_flatMap,List.map_map,Function.comp_def]

theorem channel_fields_le_input (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (Channels.fields (Channels.channelValues E)).length≤(wordInput E target word).length := by
  have contained : (Channels.fields (Channels.channelValues E)).length≤
      ((rawExperiment E++[Datum.rational target]++rawWord E word).flatMap encodeDatum).length := by
    rw [experiment_channels]
    simp only [List.flatMap_append,rational_fields_map,List.length_append]
    omega
  exact contained.trans (fields_length_le_encode _)

theorem channel_packets_le_input (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (PacketLists.rats (Channels.channelValues E) []).length≤2*(wordInput E target word).length := by
  have total := packets_le_fields (Channels.channelValues E) []
  have raw := channel_fields_le_input E target word
  simp only [List.length_nil,Nat.add_zero] at total
  exact total.trans (Nat.mul_le_mul_left 2 raw)

theorem alphabet_le_input (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    E.alphabetSize≤(wordInput E target word).length := by
  have count := datum_count_le_fields ((Channels.channelValues E).map Datum.rational)
  rw [List.length_map,Channels.channel_count,rational_fields_map] at count
  have raw := channel_fields_le_input E target word
  omega

theorem word_length_le_input (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    word.1≤(wordInput E target word).length := by
  have count := (datum_count_le_fields (rawExperiment E++[Datum.rational target]++rawWord E word)).trans
    (fields_length_le_encode _)
  change (rawExperiment E++[Datum.rational target]++rawWord E word).length≤(wordInput E target word).length at count
  simp only [List.length_append,rawWord,List.length_cons,List.length_map,List.length_finRange] at count
  omega

theorem original_odds_field_quadratic (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    RatInput.Encoder.fieldSize (E.rationalWordOdds word)≤8*((wordInput E target word).length+1)^2 := by
  have bound := WordFold.original_odds_field_bound E target word
  have count := word_length_le_input E target word
  unfold RootB23.WordOddsBits.prefixBound at bound
  calc
    _≤8*(word.1+1)*((wordInput E target word).length+1) := bound
    _≤8*((wordInput E target word).length+1)*((wordInput E target word).length+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 (Nat.add_le_add_right count 1))
    _=8*((wordInput E target word).length+1)^2 := by ring

end B23_4_RatWordPrep.WordFinish.Resources
