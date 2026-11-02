module
public import Common.PSTR_TM_MulPassCode_079
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulPassValue080
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulPassCode079

theorem control_specs (m ca cc : Bool) : mode (control m ca cc)=m ∧ aCarry (control m ca cc)=ca ∧ cCarry (control m ca cc)=cc := by
  cases m <;> cases ca <;> cases cc <;> exact ⟨rfl,rfl,rfl⟩

theorem control_eta (r : Fin 8) : control (mode r) (aCarry r) (cCarry r) = r := by
  fin_cases r <;> rfl

theorem next_specs (r : Fin 8) (c a : Bool) : mode (nextControl r c a)=mode r ∧ aCarry (nextControl r c a)=a ∧
    cCarry (nextControl r c a)=PSTRTMBinaryAdd024.carryBit (cCarry r) c (a && mode r) :=
  control_specs _ _ _

theorem result_length (r : Fin 8) (triples : List Triple) : (resultTriples r triples).length=triples.length := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple later ih => obtain ⟨c,a,b⟩ := triple; simp only [resultTriples,List.length_cons,ih]

theorem final_mode (r : Fin 8) (triples : List Triple) : mode (finalControl r triples)=mode r := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    rw [finalControl,ih]
    exact (next_specs r c a).1

theorem bValue_result (r : Fin 8) (triples : List Triple) : bValue (resultTriples r triples)=bValue triples := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    change Nat.bit b (bValue (resultTriples (nextControl r c a) later)) = Nat.bit b (bValue later)
    rw [ih]

/-- BOTH real overflow bits remain in the exact identities. This never
declares a truncated finite-width result equal to an unbounded integer. -/
theorem aValue_result (r : Fin 8) (triples : List Triple) :
    aValue (resultTriples r triples)+2^triples.length*(aCarry (finalControl r triples)).toNat =
      2*aValue triples+(aCarry r).toNat := by
  induction triples generalizing r with
  | nil => simp [resultTriples,finalControl,aValue,PSTRTMIncrement009.valueDigits]
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    have ht := ih (nextControl r c a)
    rw [(next_specs r c a).2.1] at ht
    change Nat.bit (aCarry r) (aValue (resultTriples (nextControl r c a) later)) +
      2^(later.length+1)*(aCarry (finalControl (nextControl r c a) later)).toNat =
      2*Nat.bit a (aValue later)+(aCarry r).toNat
    cases hc : aCarry r <;> cases a <;>
      simp only [Nat.bit,Bool.cond_false,Bool.cond_true,Bool.toNat_false,Bool.toNat_true,Nat.pow_succ] at ht ⊢ <;> nlinarith

theorem cValue_result (r : Fin 8) (triples : List Triple) :
    cValue (resultTriples r triples)+2^triples.length*(cCarry (finalControl r triples)).toNat =
      cValue triples+(mode r).toNat*aValue triples+(cCarry r).toNat := by
  induction triples generalizing r with
  | nil => simp [resultTriples,finalControl,cValue,aValue,PSTRTMIncrement009.valueDigits]
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    have ht := ih (nextControl r c a)
    rw [(next_specs r c a).1,(next_specs r c a).2.2] at ht
    change Nat.bit (sumOutput r c a) (cValue (resultTriples (nextControl r c a) later)) +
      2^(later.length+1)*(cCarry (finalControl (nextControl r c a) later)).toNat =
      Nat.bit c (cValue later)+(mode r).toNat*Nat.bit a (aValue later)+(cCarry r).toNat
    cases hm : mode r <;> cases hc : cCarry r <;> cases c <;> cases a <;>
      simp [sumOutput,PSTRTMBinaryAdd024.sumBit,PSTRTMBinaryAdd024.carryBit,Nat.bit,Nat.pow_succ,hm,hc] at ht ⊢ <;> nlinarith

theorem finalControl_append (r : Fin 8) (first second : List Triple) :
    finalControl r (first++second)=finalControl (finalControl r first) second := by
  induction first generalizing r with
  | nil => rfl
  | cons triple later ih => obtain ⟨c,a,b⟩ := triple; simp only [List.cons_append,finalControl,ih]

/-- The concrete multiplication caller will REALLY append this one zero
column before a pass. Its two computed overflow bits are then false. -/
theorem appended_zero_noOverflow (r : Fin 8) (triples : List Triple) :
    aCarry (finalControl r (triples++[(false,false,false)]))=false ∧
      cCarry (finalControl r (triples++[(false,false,false)]))=false := by
  rw [finalControl_append]
  change aCarry (nextControl (finalControl r triples) false false)=false ∧
    cCarry (nextControl (finalControl r triples) false false)=false
  have hs := next_specs (finalControl r triples) false false
  constructor
  · exact hs.2.1
  · rw [hs.2.2]
    simp [PSTRTMBinaryAdd024.carryBit]

theorem appended_zero_values (triples : List Triple) :
    cValue (triples++[(false,false,false)])=cValue triples ∧
    aValue (triples++[(false,false,false)])=aValue triples ∧
    bValue (triples++[(false,false,false)])=bValue triples := by
  induction triples with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    change Nat.bit c (cValue (later++[(false,false,false)]))=Nat.bit c (cValue later) ∧
      Nat.bit a (aValue (later++[(false,false,false)]))=Nat.bit a (aValue later) ∧
      Nat.bit b (bValue (later++[(false,false,false)]))=Nat.bit b (bValue later)
    rw [ih.1,ih.2.1,ih.2.2]
    exact ⟨rfl,rfl,rfl⟩

theorem actual_padded_pass_values (m : Bool) (triples : List Triple) :
    cValue (resultTriples (control m false false) (triples++[(false,false,false)])) =
      cValue triples+m.toNat*aValue triples ∧
    aValue (resultTriples (control m false false) (triples++[(false,false,false)])) = 2*aValue triples ∧
    bValue (resultTriples (control m false false) (triples++[(false,false,false)])) = bValue triples := by
  have hc := cValue_result (control m false false) (triples++[(false,false,false)])
  have ha := aValue_result (control m false false) (triples++[(false,false,false)])
  have hz := appended_zero_noOverflow (control m false false) triples
  have hv := appended_zero_values triples
  have hs := control_specs m false false
  rw [hz.2,hs.1,hs.2.2,hv.1,hv.2.1] at hc
  rw [hz.1,hs.2.1,hv.2.1] at ha
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hc ha
  exact ⟨hc,ha,(bValue_result _ _).trans hv.2.2⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulPassValue080
