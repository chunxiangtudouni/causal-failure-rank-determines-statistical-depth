module

public import B23_4_RatWordPrep_SeqCmp_WordFrontendEnvelopeJoin_191
public import B23_4_RatWordPrep_SeqCmp_WordOriginalCount_189

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

noncomputable def lookupMassPolynomial (C : Type*) (truth : Bool) (number mass : PolynomialBudget) : PolynomialBudget :=
  mass+.constant (Lookup.Count.pushCap truth (.halt : Lookup.Statement C))*(2*mass+2*(number+1)+14)

noncomputable def lookupPhasePolynomial (C : Type*) (truth : Bool) (number width mass : PolynomialBudget) : PolynomialBudget :=
  2*mass+2*(number+1)+14+256*(number+1)*(lookupMassPolynomial C truth number mass+1)+number*(3*width+14)

noncomputable def lookupPolynomial (C : Type*) (truth : Bool) (number width mass : PolynomialBudget) : PolynomialBudget :=
  2+lookupPhasePolynomial C truth number width (mass+1)+
    lookupPhasePolynomial C truth number width (lookupMassPolynomial C truth number (mass+1))+
    (6*width+28+2*number*(3*width+16)+4)

noncomputable def firstLookupPolynomial (C : Type*) : PolynomialBudget :=
  lookupPolynomial C false inputBudget inputBudget (128*successorBudget^2)
noncomputable def firstMassPolynomial (C : Type*) : PolynomialBudget :=
  128*successorBudget^2+.constant (WordFold.Count.pushCap (.halt : WordFold.Statement C))*firstLookupPolynomial C
noncomputable def secondLookupPolynomial (C : Type*) : PolynomialBudget :=
  lookupPolynomial C true inputBudget inputBudget (firstMassPolynomial C)
noncomputable def secondMassPolynomial (C : Type*) : PolynomialBudget :=
  firstMassPolynomial C+.constant (WordFold.Count.pushCap (.halt : WordFold.Statement C))*secondLookupPolynomial C
noncomputable def ratioMassPolynomial (C : Type*) : PolynomialBudget := secondMassPolynomial C+32*successorBudget^2
noncomputable def symbolPolynomial (C : Type*) : PolynomialBudget :=
  firstLookupPolynomial C+secondLookupPolynomial C+
    .constant (7*binaryScaleCoefficient RatMulDiv.divCoefficient+137)*(secondMassPolynomial C+1)^4+
    .constant (7*binaryScaleCoefficient RatMulDiv.mulCoefficient+137)*(ratioMassPolynomial C+1)^4+6*successorBudget+12

noncomputable def foldPolynomial (C : Type*) : PolynomialBudget :=
  frontendPolynomial C+2+inputBudget*(symbolPolynomial C+2)

noncomputable def wholePolynomial (C : Type*) : PolynomialBudget :=
  foldPolynomial C+5*successorBudget+10+
    21*.constant tailCoefficient*(2*successorBudget+4+2*inputBudget+28*(16*successorBudget^2+6)+1)^4

theorem lookup_polynomial_bound (C : Type*) (truth : Bool) (number width mass bound : Nat)
    (n w m : PolynomialBudget) (numberBound : number≤n.eval bound) (widthBound : width≤w.eval bound) (massBound : mass≤m.eval bound) :
    Lookup.Count.uniformWork truth (.halt : Lookup.Statement C) number width mass≤(lookupPolynomial C truth n w m).eval bound := by
  change Lookup.Count.uniformWork truth (.halt : Lookup.Statement C) number width mass≤
    Lookup.Count.uniformWork truth (.halt : Lookup.Statement C) (n.eval bound) (w.eval bound) (m.eval bound)
  unfold Lookup.Count.uniformWork Lookup.Count.uniformPhase Lookup.Count.uniformMass Lookup.Count.uniformSetup Lookup.Count.uniformSelected
  gcongr

theorem symbol_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordFold.Count.symbolBudget (.halt : WordFold.Statement C) E.alphabetSize (wordInput E target word).length≤
      (symbolPolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have number : E.alphabetSize ≤ inputBudget.eval B := alphabet_le_input E target word
  have first : WordFold.Count.firstLookup (C:=C) E.alphabetSize B≤(firstLookupPolynomial C).eval B :=
    lookup_polynomial_bound C false E.alphabetSize B (WordFold.Count.massBudget B) B inputBudget inputBudget
      (128*successorBudget^2) number (Nat.le_refl _) (Nat.le_refl _)
  have mass1 : WordFold.Count.firstMass (.halt : WordFold.Statement C) E.alphabetSize B≤(firstMassPolynomial C).eval B :=
    Nat.add_le_add_left (Nat.mul_le_mul_left (WordFold.Count.pushCap (.halt : WordFold.Statement C)) first) _
  have second : WordFold.Count.secondLookup (.halt : WordFold.Statement C) E.alphabetSize B≤(secondLookupPolynomial C).eval B :=
    lookup_polynomial_bound C true E.alphabetSize B _ B inputBudget inputBudget (firstMassPolynomial C) number (Nat.le_refl _) mass1
  have mass2 : WordFold.Count.secondMass (.halt : WordFold.Statement C) E.alphabetSize B≤(secondMassPolynomial C).eval B :=
    Nat.add_le_add mass1 (Nat.mul_le_mul_left (WordFold.Count.pushCap (.halt : WordFold.Statement C)) second)
  have ratio : WordFold.Count.ratioMass (.halt : WordFold.Statement C) E.alphabetSize B≤(ratioMassPolynomial C).eval B :=
    Nat.add_le_add_right mass2 _
  have division := Nat.mul_le_mul_left (7*binaryScaleCoefficient RatMulDiv.divCoefficient+137)
    (Nat.pow_le_pow_left (Nat.add_le_add_right mass2 1) 4)
  have product := Nat.mul_le_mul_left (7*binaryScaleCoefficient RatMulDiv.mulCoefficient+137)
    (Nat.pow_le_pow_left (Nat.add_le_add_right ratio 1) 4)
  change WordFold.Count.firstLookup (C:=C) E.alphabetSize B+WordFold.Count.secondLookup (.halt : WordFold.Statement C) E.alphabetSize B+
    (7*binaryScaleCoefficient RatMulDiv.divCoefficient+137)*(WordFold.Count.secondMass (.halt : WordFold.Statement C) E.alphabetSize B+1)^4+
    (7*binaryScaleCoefficient RatMulDiv.mulCoefficient+137)*(WordFold.Count.ratioMass (.halt : WordFold.Statement C) E.alphabetSize B+1)^4+6*(B+1)+12≤
    (firstLookupPolynomial C).eval B+(secondLookupPolynomial C).eval B+
    (7*binaryScaleCoefficient RatMulDiv.divCoefficient+137)*((secondMassPolynomial C).eval B+1)^4+
    (7*binaryScaleCoefficient RatMulDiv.mulCoefficient+137)*((ratioMassPolynomial C).eval B+1)^4+6*(B+1)+12
  omega

theorem fold_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    WordFold.Count.originalBudget (.halt : WordFold.Statement C) E target word≤(foldPolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have front := frontend_envelope C E target word
  have symbols := symbol_envelope C E target word
  have count : word.1≤B := word_length_le_input E target word
  change OddsInit.Count.originalBudget (.halt : OddsInit.Statement C) E target word≤(frontendPolynomial C).eval B at front
  change WordFold.Count.symbolBudget (.halt : WordFold.Statement C) E.alphabetSize B≤(symbolPolynomial C).eval B at symbols
  have loop := Nat.mul_le_mul count (Nat.add_le_add_right symbols 2)
  change OddsInit.Count.originalBudget (.halt : OddsInit.Statement C) E target word+
    (2+word.1*(WordFold.Count.symbolBudget (.halt : WordFold.Statement C) E.alphabetSize B+2))≤
    (frontendPolynomial C).eval B+2+B*((symbolPolynomial C).eval B+2)
  omega

theorem whole_envelope (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    originalTimeBound (C:=C) E target word≤(wholePolynomial C).eval (wordInput E target word).length := by
  let B := (wordInput E target word).length
  have front := fold_envelope C E target word
  change WordFold.Count.originalBudget (.halt : WordFold.Statement C) E target word≤(foldPolynomial C).eval B at front
  have raw := (rawPayload_le_number E.alphabetSize).trans (Nat.add_le_add_right (alphabet_le_input E target word) 1)
  change (PSTRTMNatValue017.rawPayload E.alphabetSize).length≤B+1 at raw
  change WordFold.Count.originalBudget (.halt : WordFold.Statement C) E target word+
    5*(PSTRTMNatValue017.rawPayload E.alphabetSize).length+10+21*tailCoefficient*(originalTailScale B)^4≤
    (foldPolynomial C).eval B+5*(B+1)+10+21*tailCoefficient*(originalTailScale B)^4
  omega

noncomputable def wholeDegree (C : Type*) : Nat := max 1 (wholePolynomial C).degree

theorem wholeDegree_positive (C : Type*) : 0<wholeDegree C :=
  Nat.lt_of_lt_of_le (by decide : 0<1) (Nat.le_max_left 1 _)

noncomputable def wholeCoefficient (C : Type*) : Nat := (wholePolynomial C).coefficient

theorem original_time_polynomial (C : Type*) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    originalTimeBound (C:=C) E target word≤wholeCoefficient C*((wordInput E target word).length+1)^(wholeDegree C) := by
  have bound := (whole_envelope C E target word).trans ((wholePolynomial C).eval_bound (wordInput E target word).length)
  exact bound.trans (Nat.mul_le_mul_left (wholeCoefficient C)
    (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_right 1 (wholePolynomial C).degree)))

end B23_4_RatWordPrep.WordFinish.Resources
