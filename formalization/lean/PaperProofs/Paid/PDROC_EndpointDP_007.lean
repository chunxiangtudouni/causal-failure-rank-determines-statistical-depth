module

public import PaperProofs.Paid.PDROC_EndpointDP_002
public import PaperProofs.Paid.PDROC_EndpointBounds_005
public import PaperProofs.Statistics.StoppedInformation
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
open PaperProofs.Statistics PaperProofs.Paid
open PaperProofs.Paid.Parameters

namespace PDROC

/-- Finite iid word mass, in the same exact rational channel as walkUpdate. -/
def endpointWordMass (P : Parameters) (truth : Bool) (n : ℕ) (word : Fin n → Fin 2) : ℚ :=
  ∏ k : Fin n, P.experiment.channel truth (word k)

/-- Analysis completion only; endpointWalkState reads none of its symbols
after the finite word. The runtime rational array is unchanged. -/
noncomputable def endpointWordState (P : Parameters) (level n : ℕ) (word : Fin n → Fin 2) : WalkCell level :=
  endpointWalkState level (P.experiment.completeStoppedWord ⟨n, word⟩) n

theorem endpointWordMass_nonneg (P : Parameters) (truth : Bool) (n : ℕ) (word : Fin n → Fin 2) :
    0 ≤ endpointWordMass P truth n word :=
  Finset.prod_nonneg (fun k _ => (P.experiment.channel_pos truth (word k)).le)

theorem endpointWordMass_zero (P : Parameters) (truth : Bool) (word : Fin 0 → Fin 2) :
    endpointWordMass P truth 0 word = 1 := by
  let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
  change (∏ k : Fin 0, channel (word k)) = 1
  simp

theorem endpointWordMass_snoc (P : Parameters) (truth : Bool) (n : ℕ)
    (word : Fin n → Fin 2) (letter : Fin 2) :
    endpointWordMass P truth (n + 1) (Fin.snoc word letter) =
      endpointWordMass P truth n word * P.experiment.channel truth letter := by
  let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
  let extended : Fin (n + 1) → Fin 2 := Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) word letter
  change (∏ k : Fin (n + 1), channel (extended k)) =
    (∏ k : Fin n, channel (word k)) * channel letter
  rw [Fin.prod_univ_castSucc]
  simp only [extended, Fin.snoc_castSucc, Fin.snoc_last]

theorem endpointWordState_of_prefix (P : Parameters) (level n : ℕ) (word : Fin n → Fin 2)
    (tape : P.experiment.Tape) (hp : ∀ k : Fin n, tape k.val = word k) :
    endpointWalkState level tape n = endpointWordState P level n word := by
  apply endpointWalkState_prefix level n
  intro k hk
  rw [P.experiment.completeStoppedWord_prefix n word k hk]
  exact hp ⟨k, hk⟩

theorem endpointWordState_snoc (P : Parameters) (level n : ℕ) (word : Fin n → Fin 2) (letter : Fin 2) :
    endpointWordState P level (n + 1) (Fin.snoc word letter) =
      walkMove level (endpointWordState P level n word) letter := by
  let complete : (k : ℕ) → (Fin k → Fin 2) → (ℕ → Fin 2) :=
    fun k wordPrefix => P.experiment.completeStoppedWord ⟨k, wordPrefix⟩
  let extended : Fin (n + 1) → Fin 2 := Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) word letter
  change endpointWalkState level (complete (n + 1) extended) (n + 1) =
    walkMove level (endpointWalkState level (complete n word) n) letter
  rw [endpointWalkState_succ]
  have hp : endpointWalkState level (complete (n + 1) extended) n =
      endpointWalkState level (complete n word) n := by
    apply endpointWalkState_prefix level n
    intro k hk
    have hfirst : complete (n + 1) extended k = extended ⟨k, by omega⟩ :=
      P.experiment.completeStoppedWord_prefix (n + 1) extended k (by omega)
    have hsecond : complete n word k = word ⟨k, hk⟩ := P.experiment.completeStoppedWord_prefix n word k hk
    rw [hfirst, hsecond]
    exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => Fin 2) letter word ⟨k, hk⟩
  have hl : complete (n + 1) extended n = letter := by
    have hlast : complete (n + 1) extended n = extended ⟨n, by omega⟩ :=
      P.experiment.completeStoppedWord_prefix (n + 1) extended n (by omega)
    rw [hlast]
    exact Fin.snoc_last (α := fun _ : Fin (n + 1) => Fin 2) letter word
  rw [hp, hl]

/-- Finite-word pushforward mass is a proof object, not a new implementation
of q_m. The theorem below identifies the original Array with this law. -/
noncomputable def endpointWordStateMass (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ)
    (target : WalkCell level) : ℚ :=
  ∑ word : Fin n → Fin 2, if endpointWordState P level n word = target then endpointWordMass P truth n word else 0

theorem endpointWordStateMass_zero (P : Parameters) (level : ℕ) (truth : Bool) (target : WalkCell level) :
    endpointWordStateMass P level truth 0 target = if target.val = level then 1 else 0 := by
  classical
  let empty : Fin 0 → Fin 2 := fun i => Fin.elim0 i
  let : Unique (Fin 0 → Fin 2) := ⟨⟨empty⟩, fun word => funext (fun i => Fin.elim0 i)⟩
  unfold endpointWordStateMass
  rw [Fintype.sum_unique, endpointWordMass_zero]
  change (if (⟨level, by omega⟩ : WalkCell level) = target then (1 : ℚ) else 0) = _
  have he : (⟨level, by omega⟩ : WalkCell level) = target ↔ target.val = level := by
    rw [Fin.ext_iff]
    exact eq_comm
  simp only [he]

/-- Exact finite pushforward summation identity. -/
theorem endpointWordStateMass_expectation (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ)
    (f : WalkCell level → ℚ) :
    (∑ state : WalkCell level, endpointWordStateMass P level truth n state * f state) =
      ∑ word : Fin n → Fin 2, endpointWordMass P truth n word * f (endpointWordState P level n word) := by
  classical
  unfold endpointWordStateMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _hw
  simp only [ite_mul, zero_mul]
  simp

theorem endpointWordStateMass_succ (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ)
    (target : WalkCell level) :
    endpointWordStateMass P level truth (n + 1) target =
      ∑ state : WalkCell level, ∑ letter : Fin 2,
        if walkMove level state letter = target then
          endpointWordStateMass P level truth n state * P.experiment.channel truth letter else 0 := by
  classical
  let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
  let f := fun word : Fin (n + 1) → Fin 2 =>
    if endpointWordState P level (n + 1) word = target then endpointWordMass P truth (n + 1) word else 0
  change (∑ word : Fin (n + 1) → Fin 2, f word) =
    ∑ state : WalkCell level, ∑ letter : Fin 2,
      if walkMove level state letter = target then endpointWordStateMass P level truth n state * channel letter else 0
  calc
    (∑ word : Fin (n + 1) → Fin 2, f word) =
        ∑ pair : Fin 2 × (Fin n → Fin 2), f (Fin.snoc pair.2 pair.1) :=
      (Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 2)) f).symm
    _ = ∑ letter : Fin 2, ∑ word : Fin n → Fin 2,
        endpointWordMass P truth n word *
          (if walkMove level (endpointWordState P level n word) letter = target then channel letter else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro letter _hl
      apply Finset.sum_congr rfl
      intro word _hw
      change (if endpointWordState P level (n + 1) (Fin.snoc word letter) = target then
        endpointWordMass P truth (n + 1) (Fin.snoc word letter) else 0) = _
      have hmass : endpointWordMass P truth (n + 1) (Fin.snoc word letter) =
          endpointWordMass P truth n word * channel letter := endpointWordMass_snoc P truth n word letter
      rw [endpointWordState_snoc, hmass]
      split_ifs <;> ring
    _ = ∑ letter : Fin 2, ∑ state : WalkCell level,
        endpointWordStateMass P level truth n state *
          (if walkMove level state letter = target then channel letter else 0) := by
      apply Finset.sum_congr rfl
      intro letter _hl
      exact (endpointWordStateMass_expectation P level truth n
        (fun state => if walkMove level state letter = target then channel letter else 0)).symm
    _ = ∑ state : WalkCell level, ∑ letter : Fin 2,
        if walkMove level state letter = target then
          endpointWordStateMass P level truth n state * channel letter else 0 := by
      rw [Finset.sum_comm]
      simp only [mul_ite, mul_zero]

/-- Full finite-word law of the ACTUAL original rational Array, with no
assumed Markov/DP correctness field and for both truths. -/
theorem endpointWalkDistribution_eq_wordMass (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ)
    (target : WalkCell level) :
    P.walkDistribution level truth n target = endpointWordStateMass P level truth n target := by
  induction n generalizing target with
  | zero => rw [endpointWalkDistribution_zero, endpointWordStateMass_zero]
  | succ n ih =>
    rw [endpointWalkDistribution_succ, endpointWordStateMass_succ]
    let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
    change (∑ state : WalkCell level, ∑ letter : Fin 2,
      if walkMove level state letter = target then P.walkDistribution level truth n state * channel letter else 0) =
      ∑ state : WalkCell level, ∑ letter : Fin 2,
        if walkMove level state letter = target then endpointWordStateMass P level truth n state * channel letter else 0
    simp_rw [ih]

universe u

open Classical in
/-- Exact finite iid prefix pushforward, derived from the original tape
cylinder law. The classifier is arbitrary; no DP correctness is an input. -/
theorem endpointFinitePrefix_law (E : BinaryExperiment) (truth : Bool) (n : ℕ)
    {Target : Type u} (f : (Fin n → Fin E.alphabetSize) → Target) (target : Target) :
    E.tapeLaw truth {tape | f (fun k : Fin n => tape k.val) = target} =
      ENNReal.ofReal (∑ word : Fin n → Fin E.alphabetSize,
        if f word = target then E.wordProbability truth ⟨n, word⟩ else 0) := by
  classical
  let A := fun word : Fin n → Fin E.alphabetSize =>
    if f word = target then E.prefixEvent ⟨n, word⟩ else (∅ : Set E.Tape)
  have hevent : {tape : E.Tape | f (fun k : Fin n => tape k.val) = target} = ⋃ word, A word := by
    ext tape
    constructor
    · intro h
      let word : Fin n → Fin E.alphabetSize := fun k => tape k.val
      have hw : f word = target := h
      refine Set.mem_iUnion.mpr ⟨word, ?_⟩
      change tape ∈ (if f word = target then E.prefixEvent ⟨n, word⟩ else ∅)
      rw [ite_eq_left hw]
      exact fun _ => rfl
    · intro h
      obtain ⟨word, hw⟩ := Set.mem_iUnion.mp h
      by_cases hf : f word = target
      · have hp : tape ∈ E.prefixEvent ⟨n, word⟩ := by simpa only [A, hf, ite_true] using hw
        have he : (fun k : Fin n => tape k.val) = word := funext hp
        change f (fun k : Fin n => tape k.val) = target
        rw [he]
        exact hf
      · have hempty : tape ∈ (∅ : Set E.Tape) := by simpa only [A, hf, ite_false] using hw
        exact hempty.elim
  have hsub (word : Fin n → Fin E.alphabetSize) : A word ⊆ E.prefixEvent ⟨n, word⟩ := by
    dsimp only [A]
    split_ifs
    · exact fun _ h => h
    · exact Set.empty_subset _
  have hdis : Pairwise (fun word other => Disjoint (A word) (A other)) := by
    intro word other hne
    apply Set.disjoint_left.mpr
    intro tape hw ho
    have hpw := hsub word hw
    have hpo := hsub other ho
    exact hne (funext (fun k => (hpw k).symm.trans (hpo k)))
  have hm (word : Fin n → Fin E.alphabetSize) : MeasurableSet (A word) := by
    dsimp only [A]
    split_ifs
    · exact E.measurableSet_prefixEvent ⟨n, word⟩
    · exact MeasurableSet.empty
  have hmu (word : Fin n → Fin E.alphabetSize) :
      E.tapeLaw truth (A word) = ENNReal.ofReal
        (if f word = target then E.wordProbability truth ⟨n, word⟩ else 0) := by
    dsimp only [A]
    split_ifs
    · exact E.tapeLaw_prefixEvent truth ⟨n, word⟩
    · simp only [measure_empty, ENNReal.ofReal_zero]
  have hnonneg (word : Fin n → Fin E.alphabetSize) :
      0 ≤ if f word = target then E.wordProbability truth ⟨n, word⟩ else 0 := by
    split_ifs
    · exact (E.wordProbability_pos truth ⟨n, word⟩).le
    · exact le_rfl
  rw [hevent, measure_iUnion hdis hm, tsum_fintype]
  simp_rw [hmu]
  exact (ENNReal.ofReal_sum_of_nonneg (fun word _ => hnonneg word)).symm

/-- The rational word products are exactly the original real iid masses. -/
theorem endpointWordMass_cast (P : Parameters) (truth : Bool) (n : ℕ) (word : Fin n → Fin 2) :
    ((endpointWordMass P truth n word : ℚ) : ℝ) = P.experiment.wordProbability truth ⟨n, word⟩ := by
  let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
  change ((∏ k : Fin n, channel (word k) : ℚ) : ℝ) = ∏ k : Fin n, (channel (word k) : ℝ)
  exact Rat.cast_prod Finset.univ (fun k : Fin n => channel (word k))

/-- Exact law of the actual absorbing process under the original infinite
iid tape, retaining both truth-conditional distributions. -/
theorem endpointWalkState_tapeLaw (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ)
    (target : WalkCell level) :
    P.experiment.tapeLaw truth {tape | endpointWalkState level tape n = target} =
      ENNReal.ofReal ((P.walkDistribution level truth n target : ℚ) : ℝ) := by
  classical
  let μ : Measure (ℕ → Fin 2) := P.experiment.tapeLaw truth
  let classify : (Fin n → Fin 2) → WalkCell level := endpointWordState P level n
  let probability : (Fin n → Fin 2) → ℝ := fun word => P.experiment.wordProbability truth ⟨n, word⟩
  change μ {tape : ℕ → Fin 2 | endpointWalkState level tape n = target} = _
  have hp (tape : ℕ → Fin 2) : endpointWalkState level tape n =
      endpointWordState P level n (fun k : Fin n => tape k.val) :=
    endpointWordState_of_prefix P level n (fun k : Fin n => tape k.val) tape (fun _ => rfl)
  have hevent : {tape : ℕ → Fin 2 | endpointWalkState level tape n = target} =
      {tape : ℕ → Fin 2 | endpointWordState P level n (fun k : Fin n => tape k.val) = target} := by
    ext tape
    change (endpointWalkState level tape n = target) ↔
      (endpointWordState P level n (fun k : Fin n => tape k.val) = target)
    rw [hp tape]
  have hprefix : μ {tape : ℕ → Fin 2 | classify (fun k : Fin n => tape k.val) = target} =
      ENNReal.ofReal (∑ word : Fin n → Fin 2, if classify word = target then probability word else 0) := by
    have hraw : μ {tape : ℕ → Fin 2 | classify (fun k : Fin n => tape k.val) = target} =
        ENNReal.ofReal (∑ word : Fin n → Fin 2,
          @ite ℝ (classify word = target) (Classical.propDecidable _) (probability word) 0) :=
      endpointFinitePrefix_law P.experiment truth n classify target
    refine hraw.trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro word _hw
    by_cases hword : classify word = target
    · simp only [hword, ite_true]
    · simp only [hword, ite_false]
  rw [hevent]
  change μ {tape : ℕ → Fin 2 | classify (fun k : Fin n => tape k.val) = target} = _
  rw [hprefix, endpointWalkDistribution_eq_wordMass]
  congr 1
  unfold endpointWordStateMass
  rw [Rat.cast_sum]
  dsimp only [classify]
  apply Finset.sum_congr rfl
  intro word _hw
  split_ifs
  · exact (endpointWordMass_cast P truth n word).symm
  · simp only [Rat.cast_zero]

theorem measurable_endpointWalkState (P : Parameters) (level n : ℕ) :
    Measurable (fun tape : P.experiment.Tape => endpointWalkState level tape n) := by
  change Measurable (fun tape : ℕ → Fin 2 => endpointWalkState level tape n)
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : Measurable (fun pair : WalkCell level × Fin 2 => walkMove level pair.1 pair.2) :=
      measurable_of_countable _
    exact hm.comp (ih.prodMk (measurable_pi_apply n))

def endpointWalkMirrorEquiv (level : ℕ) : WalkCell level ≃ WalkCell level where
  toFun := endpointWalkMirror level
  invFun := endpointWalkMirror level
  left_inv := endpointWalkMirror_involutive level
  right_inv := endpointWalkMirror_involutive level

def endpointWalkFlipEquiv : Fin 2 ≃ Fin 2 where
  toFun := endpointWalkFlipLetter
  invFun := endpointWalkFlipLetter
  left_inv := endpointWalkFlipLetter_involutive
  right_inv := endpointWalkFlipLetter_involutive

/-- Both conditional rational rows are mirror images, for the original
array update. This proves symmetry rather than assuming a Bayes average. -/
theorem endpointWalkDistribution_mirror (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ)
    (target : WalkCell level) :
    P.walkDistribution level (!truth) n (endpointWalkMirror level target) =
      P.walkDistribution level truth n target := by
  classical
  induction n generalizing target with
  | zero =>
    have hcentre : (endpointWalkMirror level target).val = level ↔ target.val = level := by
      have ht := target.isLt
      dsimp only [endpointWalkMirror]
      omega
    simp only [endpointWalkDistribution_zero, hcentre]
  | succ n ih =>
    rw [endpointWalkDistribution_succ, endpointWalkDistribution_succ]
    let channel : Bool → Fin 2 → ℚ := fun bit letter => P.experiment.channel bit letter
    let f := fun (state : WalkCell level) (letter : Fin 2) =>
      if walkMove level state letter = endpointWalkMirror level target then
        P.walkDistribution level (!truth) n state * channel (!truth) letter else 0
    change (∑ state : WalkCell level, ∑ letter : Fin 2, f state letter) =
      ∑ state : WalkCell level, ∑ letter : Fin 2,
        if walkMove level state letter = target then P.walkDistribution level truth n state * channel truth letter else 0
    calc
      (∑ state : WalkCell level, ∑ letter : Fin 2, f state letter) =
          ∑ state : WalkCell level, ∑ letter : Fin 2,
            f (endpointWalkMirror level state) (endpointWalkFlipLetter letter) := by
        calc
          _ = ∑ state : WalkCell level, ∑ letter : Fin 2, f (endpointWalkMirror level state) letter :=
            (Equiv.sum_comp (endpointWalkMirrorEquiv level) (fun state => ∑ letter : Fin 2, f state letter)).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro state _hs
            exact (Equiv.sum_comp endpointWalkFlipEquiv (f (endpointWalkMirror level state))).symm
      _ = ∑ state : WalkCell level, ∑ letter : Fin 2,
          if walkMove level state letter = target then
            P.walkDistribution level truth n state * channel truth letter else 0 := by
        apply Finset.sum_congr rfl
        intro state _hs
        apply Finset.sum_congr rfl
        intro letter _hl
        change (if walkMove level (endpointWalkMirror level state) (endpointWalkFlipLetter letter) = endpointWalkMirror level target then
          P.walkDistribution level (!truth) n (endpointWalkMirror level state) *
            channel (!truth) (endpointWalkFlipLetter letter) else 0) = _
        have hchannel : channel (!truth) (endpointWalkFlipLetter letter) =
            channel truth letter := endpointWalkFlipLetter_channel P.binarySymmetric truth letter
        rw [endpointWalkMove_mirror, ih state, hchannel]
        have he : endpointWalkMirror level (walkMove level state letter) = endpointWalkMirror level target ↔
            walkMove level state letter = target := by
          constructor
          · intro h
            have hh := congrArg (endpointWalkMirror level) h
            simpa only [endpointWalkMirror_involutive] using hh
          · exact congrArg (endpointWalkMirror level)
        simp only [he]

/-- Original terminal MAP loss, with an independent fair original tie bit. -/
def endpointTerminalLoss (level : ℕ) (truth : Bool) (state : WalkCell level) : ℚ :=
  if state.val = level then 1 / 2 else if decide (level ≤ state.val) = truth then 0 else 1

theorem endpointTerminalLoss_true (level : ℕ) (state : WalkCell level) :
    endpointTerminalLoss level true state =
      if state.val < level then 1 else if state.val = level then 1 / 2 else 0 := by
  by_cases he : state.val = level
  · simp [endpointTerminalLoss, he]
  · by_cases hl : state.val < level
    · have hn : ¬ level ≤ state.val := by omega
      simp [endpointTerminalLoss, he, hl, hn]
    · have hn : level ≤ state.val := by omega
      simp [endpointTerminalLoss, he, hl, hn]

theorem endpointTerminalLoss_false (level : ℕ) (state : WalkCell level) :
    endpointTerminalLoss level false state =
      if level < state.val then 1 else if state.val = level then 1 / 2 else 0 := by
  by_cases he : state.val = level
  · simp [endpointTerminalLoss, he]
  · by_cases hl : level < state.val
    · have hn : level ≤ state.val := by omega
      simp [endpointTerminalLoss, he, hl, hn]
    · have hn : ¬ level ≤ state.val := by omega
      simp [endpointTerminalLoss, he, hl, hn]

theorem endpointTerminalLoss_mirror (level : ℕ) (truth : Bool) (state : WalkCell level) :
    endpointTerminalLoss level (!truth) (endpointWalkMirror level state) = endpointTerminalLoss level truth state := by
  have hs := state.isLt
  cases truth <;>
    simp only [Bool.not_false, Bool.not_true, endpointTerminalLoss_true, endpointTerminalLoss_false, endpointWalkMirror]
  all_goals split_ifs <;> simp_all <;> omega

theorem endpointWalkLoss_sum_mirror (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ) :
    (∑ state : WalkCell level, P.walkDistribution level (!truth) n state * endpointTerminalLoss level (!truth) state) =
      ∑ state : WalkCell level, P.walkDistribution level truth n state * endpointTerminalLoss level truth state := by
  classical
  calc
    _ = ∑ state : WalkCell level,
        P.walkDistribution level (!truth) n (endpointWalkMirror level state) *
          endpointTerminalLoss level (!truth) (endpointWalkMirror level state) :=
      (Equiv.sum_comp (endpointWalkMirrorEquiv level) (fun state =>
        P.walkDistribution level (!truth) n state * endpointTerminalLoss level (!truth) state)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro state _hs
      rw [endpointWalkDistribution_mirror, endpointTerminalLoss_mirror]

/-- The stored true-row rational q_m is the terminal loss for either
conditional row, including half-mass at a terminal tie. -/
theorem endpointWalkLoss_sum_eq_cappedError (P : Parameters) (m : ℕ) (truth : Bool) :
    (∑ state : WalkCell (m + 1), P.walkDistribution (m + 1) truth P.certificate.Q state *
      endpointTerminalLoss (m + 1) truth state) = P.cappedError m := by
  have ht : (∑ state : WalkCell (m + 1), P.walkDistribution (m + 1) true P.certificate.Q state *
      endpointTerminalLoss (m + 1) true state) = P.cappedError m := by
    simp only [endpointTerminalLoss_true, PaperProofs.Paid.Parameters.cappedError]
  cases truth with
  | false => exact (endpointWalkLoss_sum_mirror P (m + 1) true P.certificate.Q).trans ht
  | true => exact ht

/-- The decision classifier used by the original capped MAP rule. -/
def endpointTerminalDecision (level : ℕ) (tie : Bool) (state : WalkCell level) : Bool :=
  if state.val = level then tie else decide (level ≤ state.val)

theorem endpointTerminalLoss_nonneg (level : ℕ) (truth : Bool) (state : WalkCell level) :
    0 ≤ endpointTerminalLoss level truth state := by
  unfold endpointTerminalLoss
  split_ifs <;> norm_num

/-- Integrating the original fair tie gives the rational terminal loss,
including exactly one half at the centre. -/
theorem endpointTerminalLoss_fair (level : ℕ) (truth : Bool) (state : WalkCell level) :
    (1 / 2 : ℝ≥0∞) * (if endpointTerminalDecision level true state ≠ truth then 1 else 0) +
      (1 / 2 : ℝ≥0∞) * (if endpointTerminalDecision level false state ≠ truth then 1 else 0) =
        ENNReal.ofReal ((endpointTerminalLoss level truth state : ℚ) : ℝ) := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  cases truth <;> by_cases hc : state.val = level <;>
    by_cases hs : level ≤ state.val <;>
    norm_num [endpointTerminalDecision, endpointTerminalLoss, hc, hs]
  all_goals first
    | simpa only [one_div] using hhalf.symm
    | simpa only [one_div] using (ENNReal.add_halves (1 : ℝ≥0∞))

theorem endpointFairGuess_lintegral (f : Bool → ℝ≥0∞) :
    (∫⁻ tie, f tie ∂BinarySymmetric.Parameters.fairGuessLaw) =
      (1 / 2 : ℝ≥0∞) * f true + (1 / 2 : ℝ≥0∞) * f false := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  simp only [BinarySymmetric.Parameters.fairGuessLaw, BinarySymmetric.Parameters.rocCoinLaw,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  norm_num
  simpa only [one_div] using congrArg (fun weight : ℝ≥0∞ => weight * f true + weight * f false) hhalf

/-- All functions of the actual absorbed state have the exact finite-row
expectation, derived from the tape pushforward rather than a DP oracle. -/
theorem endpointWalkState_lintegral (P : Parameters) (level : ℕ) (truth : Bool) (n : ℕ)
    (f : WalkCell level → ℝ≥0∞) :
    (∫⁻ tape, f (endpointWalkState level tape n) ∂P.experiment.tapeLaw truth) =
      ∑ state : WalkCell level,
        f state * ENNReal.ofReal ((P.walkDistribution level truth n state : ℚ) : ℝ) := by
  have hm := measurable_endpointWalkState P level n
  rw [← lintegral_map (measurable_of_countable f) hm, lintegral_fintype]
  apply Finset.sum_congr rfl
  intro state _hs
  rw [Measure.map_apply hm (measurableSet_singleton state)]
  change f state * P.experiment.tapeLaw truth {tape | endpointWalkState level tape n = state} = _
  rw [endpointWalkState_tapeLaw]

/-- The original capped test's error indicator for a fixed original tie
bit is a function of its absorbed state at precisely the original Q. -/
theorem endpointCapped_fixedTie_error_lintegral (P : Parameters) (m : ℕ) (truth tie : Bool) :
    (∫⁻ tape, (if (P.cappedTest m).rule.decision tie tape ≠ truth then 1 else 0 : ℝ≥0∞)
      ∂P.experiment.tapeLaw truth) =
        ∑ state : WalkCell (m + 1),
          (if endpointTerminalDecision (m + 1) tie state ≠ truth then 1 else 0 : ℝ≥0∞) *
            ENNReal.ofReal ((P.walkDistribution (m + 1) truth P.certificate.Q state : ℚ) : ℝ) := by
  let μ : Measure (ℕ → Fin 2) := P.experiment.tapeLaw truth
  let decision : Bool → (ℕ → Fin 2) → Bool := (P.cappedTest m).rule.decision
  change (∫⁻ tape : ℕ → Fin 2, (if decision tie tape ≠ truth then 1 else 0 : ℝ≥0∞) ∂μ) = _
  have hd (tape : ℕ → Fin 2) : decision tie tape =
      endpointTerminalDecision (m + 1) tie (endpointWalkState (m + 1) tape P.certificate.Q) :=
    endpointWalkState_capped_decision P m tie tape
  simp_rw [hd]
  exact endpointWalkState_lintegral P (m + 1) truth P.certificate.Q
    (fun state => if endpointTerminalDecision (m + 1) tie state ≠ truth then 1 else 0)

/-- Exact error of the frozen capped MAP test for each truth separately.
This retains the original finite cap, original fair tie, and actual array q_m. -/
theorem endpointCapped_conditionalError (P : Parameters) (m : ℕ) (truth : Bool) :
    P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw
      (P.cappedTest m) truth = ENNReal.ofReal ((P.cappedError m : ℚ) : ℝ) := by
  classical
  let A : Set (Bool × P.experiment.Tape) :=
    {sample | (P.cappedTest m).rule.decision sample.1 sample.2 ≠ truth}
  have hA : MeasurableSet A :=
    ((P.cappedTest m).measurable_decision (measurableSet_singleton truth)).compl
  let f : Bool × P.experiment.Tape → ℝ≥0∞ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  have herror : P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw
      (P.cappedTest m) truth =
        ∫⁻ tie, ∫⁻ tape, f (tie, tape) ∂P.experiment.tapeLaw truth
          ∂BinarySymmetric.Parameters.fairGuessLaw := by
    change P.experiment.conditionalLaw BinarySymmetric.Parameters.fairGuessLaw truth A = _
    rw [← lintegral_indicator_one hA]
    exact lintegral_prod _ hf.aemeasurable
  rw [herror, endpointFairGuess_lintegral]
  have hfixed (tie : Bool) : (∫⁻ tape, f (tie, tape) ∂P.experiment.tapeLaw truth) =
      ∑ state : WalkCell (m + 1),
        (if endpointTerminalDecision (m + 1) tie state ≠ truth then 1 else 0 : ℝ≥0∞) *
          ENNReal.ofReal ((P.walkDistribution (m + 1) truth P.certificate.Q state : ℚ) : ℝ) := by
    change (∫⁻ tape, A.indicator 1 (tie, tape) ∂P.experiment.tapeLaw truth) = _
    simp only [A, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    exact endpointCapped_fixedTie_error_lintegral P m truth tie
  rw [hfixed true, hfixed false, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ state : WalkCell (m + 1),
        ENNReal.ofReal ((P.walkDistribution (m + 1) truth P.certificate.Q state : ℚ) : ℝ) *
          ENNReal.ofReal ((endpointTerminalLoss (m + 1) truth state : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro state _hs
      rw [← mul_assoc, ← mul_assoc, ← add_mul, endpointTerminalLoss_fair]
      exact mul_comm _ _
    _ = ENNReal.ofReal ((∑ state : WalkCell (m + 1),
        P.walkDistribution (m + 1) truth P.certificate.Q state *
          endpointTerminalLoss (m + 1) truth state : ℚ) : ℝ) := by
      rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro state _hs
        have hn : 0 ≤ ((P.walkDistribution (m + 1) truth P.certificate.Q state : ℚ) : ℝ) := by
          exact_mod_cast endpointWalkDistribution_nonneg P (m + 1) truth P.certificate.Q state
        rw [Rat.cast_mul, ENNReal.ofReal_mul hn]
      · intro state _hs
        exact_mod_cast mul_nonneg
          (endpointWalkDistribution_nonneg P (m + 1) truth P.certificate.Q state)
          (endpointTerminalLoss_nonneg (m + 1) truth state)
    _ = ENNReal.ofReal ((P.cappedError m : ℚ) : ℝ) := by
      rw [endpointWalkLoss_sum_eq_cappedError]

/-- The two actual-DP facts consumed by the original bounded-endpoint
assembly. There is no presumed q-law, truncation-tail, or calibration premise. -/
theorem endpointDP_error_and_nonneg (P : Parameters) (m : ℕ) :
    (∀ truth : Bool,
      P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw
        (P.cappedTest m) truth = ENNReal.ofReal ((P.cappedError m : ℚ) : ℝ)) ∧
      0 ≤ P.cappedError m :=
  ⟨endpointCapped_conditionalError P m, endpointCappedError_nonneg P m⟩

end PDROC
