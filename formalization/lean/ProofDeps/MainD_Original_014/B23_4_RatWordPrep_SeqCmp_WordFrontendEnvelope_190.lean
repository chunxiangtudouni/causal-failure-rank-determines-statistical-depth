module

public import B23_4_RatWordPrep_SeqCmp_WordPolynomialBudget_188
public import B23_4_RatWordPrep_SeqCmp_OddsInitCountOriginal_172
public import B23_4_RatWordPrep_SeqCmp_WordFoldCountMass_183

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

instance (number : Nat) : OfNat PolynomialBudget number := ⟨.constant number⟩
instance : Add PolynomialBudget := ⟨.add⟩
instance : Mul PolynomialBudget := ⟨.mul⟩
instance : Pow PolynomialBudget Nat := ⟨.power⟩

def inputBudget : PolynomialBudget := .input
def successorBudget : PolynomialBudget := inputBudget+1

noncomputable def channelMassPolynomial (C : Type*) : PolynomialBudget :=
  .constant OriginalPrelude.coefficient*successorBudget^16+
    .constant (Channels.Count.pushCap (.halt : Channels.Statement C))*(2*successorBudget+14+64*successorBudget^3)

noncomputable def channelTimePolynomial (C : Type*) : PolynomialBudget :=
  .constant OriginalPrelude.coefficient*successorBudget^16+2*successorBudget+14+
    256*(2*inputBudget+1)*(channelMassPolynomial C+1)+64*successorBudget^3+34*successorBudget^2

noncomputable def fieldsHeadPolynomial (C : Type*) : PolynomialBudget :=
  32*successorBudget^2+(3*inputBudget+14)+32*(inputBudget+2)^2+(3*successorBudget+6)+
    (2*channelMassPolynomial C+6*successorBudget+20)

def naturalReadPolynomial : PolynomialBudget := 32*inputBudget*(inputBudget+2)^2
def naturalMovePolynomial : PolynomialBudget := inputBudget*(3*successorBudget+6)

noncomputable def fieldsMassPolynomial (C : Type*) : PolynomialBudget :=
  channelMassPolynomial C+.constant (WordFields.Count.pushCap (.halt : WordFields.Statement C))*
    (fieldsHeadPolynomial C+naturalReadPolynomial)

noncomputable def fieldsTimePolynomial (C : Type*) : PolynomialBudget :=
  channelTimePolynomial C+fieldsHeadPolynomial C+
    256*(inputBudget+1)*(fieldsMassPolynomial C+1)+naturalReadPolynomial+naturalMovePolynomial

noncomputable def layoutTimePolynomial (C : Type*) : PolynomialBudget :=
  2*fieldsMassPolynomial C+3*inputBudget+3*successorBudget+32+
    (inputBudget*(3*successorBudget+8)+2)+(2*inputBudget*(3*inputBudget+16)+2)+4*inputBudget+4

noncomputable def frontendPolynomial (C : Type*) : PolynomialBudget :=
  fieldsTimePolynomial C+layoutTimePolynomial C+(32*inputBudget+80)+
    .constant (7*binaryScaleCoefficient RatMulDiv.divCoefficient+137)*
      (128*successorBudget^2+
        .constant (OddsInit.Count.pushCap (.halt : OddsInit.Statement C))*(32*inputBudget+80)+1)^4

theorem symbol_raw_width (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (number : Nat) (member : number∈WordFields.symbolValues E word) :
    (PSTRTMNatValue017.rawPayload number).length≤(wordInput E target word).length+1 := by
  obtain ⟨position,_present,rfl⟩ := List.mem_map.mp member
  exact (rawPayload_le_number _).trans
    (Nat.add_le_add_right ((word.2 position).isLt.le.trans (alphabet_le_input E target word)) 1)

theorem natural_linear_sum (values : List Nat) (width a b : Nat)
    (fields : ∀ n∈values,(PSTRTMNatValue017.rawPayload n).length≤width) :
    (values.map (fun n => a*(PSTRTMNatValue017.rawPayload n).length+b)).sum≤values.length*(a*width+b) := by
  have terms : ∀ term∈values.map (fun n => a*(PSTRTMNatValue017.rawPayload n).length+b),term≤a*width+b := by
    intro term member
    obtain ⟨n,present,rfl⟩ := List.mem_map.mp member
    exact Nat.add_le_add_right (Nat.mul_le_mul_left a (fields n present)) b
  simpa only [List.length_map,Nat.nsmul_eq_mul] using
    List.sum_le_length_nsmul (values.map (fun n => a*(PSTRTMNatValue017.rawPayload n).length+b)) (a*width+b) terms

theorem natural_read_envelope (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordFields.Count.readWork (WordFields.symbolValues E word)≤naturalReadPolynomial.eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have terms : ∀ term∈(WordFields.symbolValues E word).map RawNat.time,term≤32*(B+2)^2 := by
    intro term member
    obtain ⟨n,present,rfl⟩ := List.mem_map.mp member
    exact (nat_getter_time n).trans (Nat.mul_le_mul_left 32
      (Nat.pow_le_pow_left (by have width := symbol_raw_width E target word n present; omega) 2))
  have sum := List.sum_le_length_nsmul ((WordFields.symbolValues E word).map RawNat.time) (32*(B+2)^2) terms
  simp only [List.length_map,Nat.nsmul_eq_mul,WordFields.symbol_count] at sum
  have paid := sum.trans (Nat.mul_le_mul_right _ (word_length_le_input E target word))
  change _≤32*B*(B+2)^2
  exact paid.trans_eq (by ring)

theorem natural_move_envelope (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordFields.Count.moveWork (WordFields.symbolValues E word)≤naturalMovePolynomial.eval (wordInput E target word).length := by
  have sum := natural_linear_sum (WordFields.symbolValues E word) ((wordInput E target word).length+1) 3 6
    (symbol_raw_width E target word)
  rw [WordFields.symbol_count] at sum
  exact sum.trans (Nat.mul_le_mul_right _ (word_length_le_input E target word))

theorem channel_mass_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word≤
      (channelMassPolynomial C).eval (wordInput E target word).length := by
  have raw := (rawPayload_le_number E.alphabetSize).trans (Nat.add_le_add_right (alphabet_le_input E target word) 1)
  have build : Channels.Count.buildWork E.alphabetSize≤2*((wordInput E target word).length+1)+14 := by
    unfold Channels.Count.buildWork
    omega
  have read := channel_readWork_le E target word
  unfold Channels.Count.originalAllowance
  change Channels.Count.preludeBudget E target word+Channels.Count.pushCap (.halt : Channels.Statement C)*_≤
    Channels.Count.preludeBudget E target word+Channels.Count.pushCap (.halt : Channels.Statement C)*_
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add build read)) _

theorem channel_time_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    Channels.Count.originalBudget (.halt : Channels.Statement C) E target word≤
      (channelTimePolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have raw := (rawPayload_le_number E.alphabetSize).trans (Nat.add_le_add_right (alphabet_le_input E target word) 1)
  have build : Channels.Count.buildWork E.alphabetSize≤2*(B+1)+14 := by unfold Channels.Count.buildWork; omega
  have mass := channel_mass_envelope C E target word
  have read := channel_readWork_le E target word
  have move := channel_moveWork_le E target word
  change Channels.Count.readWork (Channels.channelValues E)≤64*(B+1)^3 at read
  change Channels.Count.moveWork (Channels.channelValues E)≤34*(B+1)^2 at move
  change Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word≤(channelMassPolynomial C).eval B at mass
  have count : (Channels.channelValues E).length+1≤2*B+1 := by rw [Channels.channel_count]; have n := alphabet_le_input E target word; omega
  have rounds := Nat.mul_le_mul (Nat.mul_le_mul_left 256 count) (Nat.add_le_add_right mass 1)
  unfold Channels.Count.originalBudget Channels.Count.loopBudget
  change Channels.Count.preludeBudget E target word+Channels.Count.buildWork E.alphabetSize+
    (256*((Channels.channelValues E).length+1)*(Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word+1)+
      Channels.Count.readWork (Channels.channelValues E)+Channels.Count.moveWork (Channels.channelValues E))≤
    Channels.Count.preludeBudget E target word+2*(B+1)+14+
      256*(2*B+1)*((channelMassPolynomial C).eval B+1)+64*(B+1)^3+34*(B+1)^2
  omega

end B23_4_RatWordPrep.WordFinish.Resources
