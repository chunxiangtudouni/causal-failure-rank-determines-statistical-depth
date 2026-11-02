module

public import B23_4_RatWordPrep_SeqCmp_WordFrontendEnvelope_190
public import B23_4_RatWordPrep_SeqCmp_LookupCountScale_180

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

theorem fields_head_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordFields.Count.originalHeadWork (C:=C) E target word≤(fieldsHeadPolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have targetWidth : RatInput.Encoder.fieldSize target≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.target_width_le_input E target word
  have targetTime := (rat_getter_time target).trans
    (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (Nat.add_le_add_right targetWidth 1) 2))
  have raw := (rawPayload_le_number word.1).trans (Nat.add_le_add_right (word_length_le_input E target word) 1)
  change (PSTRTMNatValue017.rawPayload word.1).length≤B+1 at raw
  have countTime := (nat_getter_time word.1).trans
    (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (Nat.add_le_add_right raw 1) 2))
  change RawNat.time word.1≤32*(B+2)^2 at countTime
  have mass := channel_mass_envelope C E target word
  change Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word≤(channelMassPolynomial C).eval B at mass
  unfold WordFields.Count.originalHeadWork
  change RawGetter.time target+(3*RatInput.Encoder.fieldSize target+14)+RawNat.time word.1+
    (3*(PSTRTMNatValue017.rawPayload word.1).length+6)+
      (2*Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word+6*(PSTRTMNatValue017.rawPayload word.1).length+20)≤
    32*(B+1)^2+(3*B+14)+32*(B+2)^2+(3*(B+1)+6)+(2*(channelMassPolynomial C).eval B+6*(B+1)+20)
  omega

theorem fields_mass_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordFields.Count.originalAllowance (.halt : WordFields.Statement C) E target word≤
      (fieldsMassPolynomial C).eval (wordInput E target word).length := by
  have mass := channel_mass_envelope C E target word
  have head := fields_head_envelope C E target word
  have read := natural_read_envelope E target word
  exact Nat.add_le_add mass (Nat.mul_le_mul_left _ (Nat.add_le_add head read))

theorem fields_time_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordFields.Count.originalBudget (.halt : WordFields.Statement C) E target word≤
      (fieldsTimePolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have front := channel_time_envelope C E target word
  have head := fields_head_envelope C E target word
  have mass := fields_mass_envelope C E target word
  have read := natural_read_envelope E target word
  have move := natural_move_envelope E target word
  change Channels.Count.originalBudget (.halt : Channels.Statement C) E target word≤(channelTimePolynomial C).eval B at front
  change WordFields.Count.originalHeadWork (C:=C) E target word≤(fieldsHeadPolynomial C).eval B at head
  change WordFields.Count.originalAllowance (.halt : WordFields.Statement C) E target word≤(fieldsMassPolynomial C).eval B at mass
  change WordFields.Count.readWork (WordFields.symbolValues E word)≤naturalReadPolynomial.eval B at read
  change WordFields.Count.moveWork (WordFields.symbolValues E word)≤naturalMovePolynomial.eval B at move
  have count : (WordFields.symbolValues E word).length+1≤B+1 := by
    rw [WordFields.symbol_count]
    exact Nat.add_le_add_right (word_length_le_input E target word) 1
  have rounds := Nat.mul_le_mul (Nat.mul_le_mul_left 256 count) (Nat.add_le_add_right mass 1)
  unfold WordFields.Count.originalBudget WordFields.Count.loopBudget
  change Channels.Count.originalBudget (.halt : Channels.Statement C) E target word+
    WordFields.Count.originalHeadWork (C:=C) E target word+
    (256*((WordFields.symbolValues E word).length+1)*(WordFields.Count.originalAllowance (.halt : WordFields.Statement C) E target word+1)+
      WordFields.Count.readWork (WordFields.symbolValues E word)+WordFields.Count.moveWork (WordFields.symbolValues E word))≤
    (channelTimePolynomial C).eval B+(fieldsHeadPolynomial C).eval B+
      256*(B+1)*((fieldsMassPolynomial C).eval B+1)+naturalReadPolynomial.eval B+naturalMovePolynomial.eval B
  omega

theorem layout_time_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordPack.Count.originalLayoutWork (C:=C) E target word≤(layoutTimePolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have mass := fields_mass_envelope C E target word
  change WordFields.Count.originalAllowance (.halt : WordFields.Statement C) E target word≤(fieldsMassPolynomial C).eval B at mass
  have alphabet := alphabet_le_input E target word
  have count : word.1≤B := word_length_le_input E target word
  have raw := (rawPayload_le_number E.alphabetSize).trans (Nat.add_le_add_right alphabet 1)
  change (PSTRTMNatValue017.rawPayload E.alphabetSize).length≤B+1 at raw
  have targetWidth : RatInput.Encoder.fieldSize target≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.target_width_le_input E target word
  have naturalSum := natural_linear_sum (WordFields.symbolValues E word).reverse (B+1) 3 8
    (by intro n member; exact symbol_raw_width E target word n (List.mem_reverse.mp member))
  simp only [List.length_reverse,WordFields.symbol_count] at naturalSum
  have naturalPaid := naturalSum.trans (Nat.mul_le_mul_right (3*(B+1)+8) count)
  have naturalBound : WordPack.Count.naturalWork (WordFields.symbolValues E word).reverse≤B*(3*(B+1)+8)+2 :=
    Nat.add_le_add_right naturalPaid 2
  have rationalSum := Lookup.Count.linear_rat_sum (Channels.channelValues E).reverse B 3 16
    (by intro q member; exact channel_field_le_input E target word q (List.mem_reverse.mp member))
  simp only [List.length_reverse,Channels.channel_count] at rationalSum
  have rationalPaid := rationalSum.trans (Nat.mul_le_mul_right (3*B+16) (Nat.mul_le_mul_left 2 alphabet))
  have rationalBound : WordPack.Count.rationalWork (Channels.channelValues E).reverse≤2*B*(3*B+16)+2 :=
    Nat.add_le_add_right rationalPaid 2
  have tableBound : (PacketLists.rats (Channels.channelValues E) []).length≤2*B := channel_packets_le_input E target word
  unfold WordPack.Count.originalLayoutWork
  change 2*WordFields.Count.originalAllowance (.halt : WordFields.Statement C) E target word+
    3*RatInput.Encoder.fieldSize target+3*(PSTRTMNatValue017.rawPayload E.alphabetSize).length+32+
    WordPack.Count.naturalWork (WordFields.symbolValues E word).reverse+WordPack.Count.rationalWork (Channels.channelValues E).reverse+
    2*(PacketLists.rats (Channels.channelValues E) []).length+4≤
    2*(fieldsMassPolynomial C).eval B+3*B+3*(B+1)+32+
      (B*(3*(B+1)+8)+2)+(2*B*(3*B+16)+2)+4*B+4
  omega

theorem pack_mass_envelope (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordPack.Count.originalMass E target word≤128*((wordInput E target word).length+1)^2 := by
  let B := (wordInput E target word).length
  have count : word.1≤B := word_length_le_input E target word
  have alphabet := alphabet_le_input E target word
  have rawN := (rawPayload_le_number E.alphabetSize).trans (Nat.add_le_add_right alphabet 1)
  have rawWord := (rawPayload_le_number word.1).trans (Nat.add_le_add_right count 1)
  change (PSTRTMNatValue017.rawPayload E.alphabetSize).length≤B+1 at rawN
  have query := WordFold.Count.natural_packets_length (WordFields.symbolValues E word) [] (B+1) (symbol_raw_width E target word)
  simp only [WordFields.symbol_count,List.length_nil,Nat.add_zero] at query
  have queryBound := query.trans (Nat.mul_le_mul_right (2*(B+1)+2) count)
  have tableBound : (PacketLists.rats (Channels.channelValues E) []).length≤2*B := channel_packets_le_input E target word
  have targetWidth : RatInput.Encoder.fieldSize target≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.target_width_le_input E target word
  have priorWidth : RatInput.Encoder.fieldSize E.priorOne≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.priorOne_width_le_input E target word
  have compWidth : RatInput.Encoder.fieldSize (1-E.priorOne)≤2*B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.prior_false_width_le_input E target word
  have feeWidth : RatInput.Encoder.fieldSize E.observationFee≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    apply RootB23.WordOddsBits.word_datum_width_le E target word
    simp [rawExperiment]
  change _≤128*(B+1)^2
  simp only [WordPack.Count.originalMass,natural_packet_length,RatInput.Encoder.packet_length,List.length_nil]
  nlinarith

theorem frontend_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    OddsInit.Count.originalBudget (.halt : OddsInit.Statement C) E target word≤
      (frontendPolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have fields := fields_time_envelope C E target word
  have layout := layout_time_envelope C E target word
  have mass : WordPack.Count.originalMass E target word≤128*(B+1)^2 := pack_mass_envelope E target word
  have priorWidth : RatInput.Encoder.fieldSize E.priorOne≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.priorOne_width_le_input E target word
  have compWidth : RatInput.Encoder.fieldSize (1-E.priorOne)≤2*B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.prior_false_width_le_input E target word
  have feeWidth : RatInput.Encoder.fieldSize E.observationFee≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    apply RootB23.WordOddsBits.word_datum_width_le E target word
    simp [rawExperiment]
  have swap : OddsInit.Count.swapWork E.observationFee E.priorOne (1-E.priorOne)≤32*B+80 := by
    unfold OddsInit.Count.swapWork
    omega
  have scale := Nat.add_le_add_right (Nat.add_le_add mass (Nat.mul_le_mul_left (OddsInit.Count.pushCap (.halt : OddsInit.Statement C)) swap)) 1
  have division := Nat.mul_le_mul_left (7*binaryScaleCoefficient RatMulDiv.divCoefficient+137) (Nat.pow_le_pow_left scale 4)
  have packTime : WordPack.Count.originalBudget (C:=C) E target word≤
      (fieldsTimePolynomial C).eval B+(layoutTimePolynomial C).eval B := Nat.add_le_add fields layout
  exact Nat.add_le_add (Nat.add_le_add packTime swap) division

end B23_4_RatWordPrep.WordFinish.Resources
