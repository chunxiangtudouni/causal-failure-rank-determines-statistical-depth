module

public import RootB23_WordOddsBits_Input_002

/-! Canonical odds on every valid prefix of the original word, charged
to the complete original wordInput. This is a mathematical size theorem,
not an implementation of the word machine. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB23.WordOddsBits

open PaperProofs.Statistics
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

def prefixWord (E : BinaryExperiment) (word : E.StoppedWord) (k : Nat) (hk : k ≤ word.1) :
    E.StoppedWord :=
  ⟨k,fun j => word.2 ⟨j.val,lt_of_lt_of_le j.isLt hk⟩⟩

@[simp] theorem prefixWord_length (E : BinaryExperiment) (word : E.StoppedWord)
    (k : Nat) (hk : k ≤ word.1) : (prefixWord E word k hk).1 = k := rfl

@[simp] theorem prefixWord_full (E : BinaryExperiment) (word : E.StoppedWord) :
    prefixWord E word word.1 le_rfl = word := by
  cases word
  rfl

def factors (E : BinaryExperiment) (word : E.StoppedWord) : List Rat :=
  List.ofFn (fun j : Fin word.1 => E.channel true (word.2 j) / E.channel false (word.2 j))

@[simp] theorem factors_length (E : BinaryExperiment) (word : E.StoppedWord) :
    (factors E word).length = word.1 := List.length_ofFn

theorem factors_prefix_eq_take (E : BinaryExperiment) (word : E.StoppedWord)
    (k : Nat) (hk : k ≤ word.1) :
    factors E (prefixWord E word k hk) = (factors E word).take k := by
  apply List.ext_getElem
  · simp only [factors_length,prefixWord_length,List.length_take]
    exact (Nat.min_eq_left hk).symm
  · intro j hj hj'
    simp only [factors,List.getElem_ofFn,List.getElem_take,prefixWord]

theorem foldl_mul_eq (xs : List Rat) (init : Rat) :
    xs.foldl (fun a q => a*q) init = init*xs.prod := by
  induction xs generalizing init with
  | nil => simp
  | cons q xs ih =>
    simpa only [List.foldl_cons,List.prod_cons,mul_assoc] using ih (init*q)

theorem rationalWordOdds_eq_foldl (E : BinaryExperiment) (word : E.StoppedWord) :
    E.rationalWordOdds word =
      (factors E word).foldl (fun a q => a*q) (E.prior true / E.prior false) := by
  rw [foldl_mul_eq]
  simp only [BinaryExperiment.rationalWordOdds,factors,List.prod_ofFn,div_eq_mul_inv]
  ring

theorem rationalWordOdds_prefix_eq_foldl_take (E : BinaryExperiment) (word : E.StoppedWord)
    (k : Nat) (hk : k ≤ word.1) :
    E.rationalWordOdds (prefixWord E word k hk) =
      ((factors E word).take k).foldl (fun a q => a*q) (E.prior true / E.prior false) := by
  rw [rationalWordOdds_eq_foldl,factors_prefix_eq_take]

theorem rationalWordOdds_prefix_zero (E : BinaryExperiment) (word : E.StoppedWord) :
    E.rationalWordOdds (prefixWord E word 0 (Nat.zero_le _)) = E.prior true / E.prior false := by
  rw [rationalWordOdds_prefix_eq_foldl_take]
  rfl

/-- No multiplicative growth factor is incurred by repeated canonicalization. -/
theorem odds_prefix_width_additive (E : BinaryExperiment) (word : E.StoppedWord)
    (k : Nat) (hk : k ≤ word.1) :
    width (E.rationalWordOdds (prefixWord E word k hk)) ≤
      width (E.prior true / E.prior false) +
        (((factors E word).take k).map width).sum := by
  rw [rationalWordOdds_prefix_eq_foldl_take]
  exact foldl_mul_width_le _ _

/-- Every channel leaf is in the original table, even for another valid word. -/
theorem factors_width_sum_le_input (E : BinaryExperiment) (p : Rat)
    (word observed : E.StoppedWord) :
    ((factors E observed).map width).sum ≤
      observed.1*(2*(wordInput E p word).length) := by
  have bound := list_width_sum_le (factors E observed) (2*(wordInput E p word).length) (by
    intro q present
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp present
    have ht := channel_width_le_input E p word true (observed.2 j)
    have hf := channel_width_le_input E p word false (observed.2 j)
    have hd := div_width_le (E.channel true (observed.2 j)) (E.channel false (observed.2 j))
    omega)
  simpa only [factors_length] using bound

/-- Both priors are paid for by the single priorOne field of original input. -/
theorem prior_odds_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width (E.prior true / E.prior false) ≤ 3*(wordInput E p word).length := by
  have ht := prior_true_width_le_input E p word
  have hf := prior_false_width_le_input E p word
  have hd := div_width_le (E.prior true) (E.prior false)
  omega

/-- The full original input supplies B; k is only the prefix length. -/
theorem prefix_odds_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord)
    (k : Nat) (hk : k ≤ word.1) :
    width (E.rationalWordOdds (prefixWord E word k hk)) ≤
      (2*k+3)*(wordInput E p word).length := by
  have sumBound := factors_width_sum_le_input E p word (prefixWord E word k hk)
  rw [factors_prefix_eq_take,prefixWord_length] at sumBound
  have total := (odds_prefix_width_additive E word k hk).trans
    (Nat.add_le_add (prior_odds_width_le_input E p word) sumBound)
  calc
    _ ≤ 3*(wordInput E p word).length + k*(2*(wordInput E p word).length) := total
    _ = (2*k+3)*(wordInput E p word).length := by ring

theorem original_odds_width_le_input (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    width (E.rationalWordOdds word) ≤ (2*word.1+3)*(wordInput E p word).length := by
  simpa only [prefixWord_full] using prefix_odds_width_le_input E p word word.1 le_rfl

def prefixBound (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) (k : Nat) : Nat :=
  8*(k+1)*((wordInput E p word).length+1)

/-- One explicit original-input bound for all three comparisons and odds output. -/
theorem prefix_pair_bounds (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord)
    (k : Nat) (hk : k ≤ word.1) :
    let r := E.rationalWordOdds (prefixWord E word k hk)
    RatPair.fieldSize r (p/(1-p)) ≤ prefixBound E p word k ∧
    RatPair.fieldSize ((1-p)/p) r ≤ prefixBound E p word k ∧
    RatPair.fieldSize 1 r ≤ prefixBound E p word k ∧
    RatInput.Encoder.fieldSize r ≤ prefixBound E p word k := by
  dsimp only
  have odds := prefix_odds_width_le_input E p word k hk
  have lower := lower_width_le_input E p word
  have upper := upper_width_le_input E p word
  simp only [ratPair_fieldSize_eq,ratInput_fieldSize_eq,width_one,prefixBound]
  have nonnegative := Nat.zero_le (k*(wordInput E p word).length)
  constructor
  · nlinarith only [odds,lower,nonnegative]
  constructor
  · nlinarith only [odds,upper,nonnegative]
  constructor <;> nlinarith only [odds,nonnegative]

theorem original_pair_bounds (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    RatPair.fieldSize (E.rationalWordOdds word) (p/(1-p)) ≤ prefixBound E p word word.1 ∧
    RatPair.fieldSize ((1-p)/p) (E.rationalWordOdds word) ≤ prefixBound E p word word.1 ∧
    RatPair.fieldSize 1 (E.rationalWordOdds word) ≤ prefixBound E p word word.1 ∧
    RatInput.Encoder.fieldSize (E.rationalWordOdds word) ≤ prefixBound E p word word.1 := by
  simpa only [prefixWord_full] using prefix_pair_bounds E p word word.1 le_rfl

/-- The frozen comparison stage's original scale, with old tails left explicit. -/
theorem prefix_inputScale_le (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord)
    (k : Nat) (hk : k ≤ word.1) (background : RatInput.Stack → List Bool)
    (tail scratch : List Bool) :
    B23_4_RatWordPrep.SeqCmp.Word.inputScale background
      (E.rationalWordOdds (prefixWord E word k hk)) (p/(1-p)) ((1-p)/p) tail scratch ≤
      RatPair.Link.outside background + tail.length + scratch.length +
        32*(k+1)*((wordInput E p word).length+1)+1 := by
  obtain ⟨lower,upper,map,output⟩ := prefix_pair_bounds E p word k hk
  unfold B23_4_RatWordPrep.SeqCmp.Word.inputScale
  dsimp only [prefixBound] at lower upper map output
  nlinarith only [lower,upper,map,output]

end RootB23.WordOddsBits
