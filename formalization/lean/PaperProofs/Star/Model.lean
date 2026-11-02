module

public import PaperProofs.Statistics.BinarySymmetric
public import PaperProofs.Common.NativeContracts
public import PaperProofs.Common.NormalCharges
public import PaperProofs.Structure.UsedGame
public import PaperProofs.Structure.LaminarTree
public import PaperProofs.Retained.Game
public import PaperProofs.Statistics.Coefficient

/-! Frozen introduction.tex:18--55 and star-proofs.tex:9--35.
All Native values below retain the original full policy class and actual fees.
The ordered-rank/coefficient propositions are obligations, never input fields.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal

namespace PaperProofs.Star

open Common

inductive Order where
  | universalFirst
  | singletonsFirst
  deriving DecidableEq

/-- `none` labels the universal stage; `some r` labels singleton r. -/
def label (q : ℕ) (order : Order) (i : Fin (q + 1)) : Option (Fin q) :=
  match order with
  | .universalFirst => if h : i.val = 0 then none else some ⟨i.val - 1, by omega⟩
  | .singletonsFirst => if h : i.val < q then some ⟨i.val, h⟩ else none

def universalIndex (q : ℕ) : Order → Fin (q + 1)
  | .universalFirst => ⟨0, by omega⟩
  | .singletonsFirst => ⟨q, by omega⟩

def singletonIndex (q : ℕ) : Order → Fin q → Fin (q + 1)
  | .universalFirst, r => ⟨r.val + 1, by omega⟩
  | .singletonsFirst, r => ⟨r.val, by omega⟩

theorem label_universalIndex (q : ℕ) (order : Order) :
    label q order (universalIndex q order) = none := by
  cases order <;> simp [label, universalIndex]

theorem label_singletonIndex (q : ℕ) (order : Order) (r : Fin q) :
    label q order (singletonIndex q order r) = some r := by
  cases order <;> simp [label, singletonIndex]

theorem label_injective (q : ℕ) (order : Order) : Function.Injective (label q order) := by
  intro i j hij
  apply Fin.ext
  cases order with
  | universalFirst =>
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · omega

    · simp [label, hi, hj] at hij
    · simp [label, hi, hj] at hij
    · have h := congrArg (Option.map Fin.val) hij
      simp [label, hi, hj] at h
      omega
  | singletonsFirst =>
    by_cases hi : i.val < q <;> by_cases hj : j.val < q
    · have h := congrArg (Option.map Fin.val) hij
      simp [label, hi, hj] at h
      exact h
    · simp [label, hi, hj] at hij
    · simp [label, hi, hj] at hij
    · omega

def labelEquiv (q : ℕ) (order : Order) : Fin (q + 1) ≃ Option (Fin q) where
  toFun := label q order
  invFun := fun l => match l with
    | none => universalIndex q order
    | some r => singletonIndex q order r
  left_inv := by
    intro i
    apply label_injective q order
    cases hi : label q order i with
    | none => exact label_universalIndex q order
    | some r => exact label_singletonIndex q order r
  right_inv := by
    intro l
    cases l with
    | none => exact label_universalIndex q order
    | some r => exact label_singletonIndex q order r

def eligibility (q : ℕ) (order : Order) (i : Fin (q + 1)) : Finset (Fin q) :=
  match label q order i with
  | none => Finset.univ
  | some r => {r}

def starInstance (q : ℕ) (order : Order) : Instance where
  toolCount := q
  compatibility := List.ofFn (eligibility q order)

theorem stageCount_eq (q : ℕ) (order : Order) : (starInstance q order).stageCount = q + 1 := by
  simp [starInstance, Instance.stageCount]

def stageEquiv (q : ℕ) (order : Order) : (starInstance q order).Stage ≃ Fin (q + 1) :=
  finCongr (stageCount_eq q order)

def universalStage (q : ℕ) (order : Order) : (starInstance q order).Stage :=
  (stageEquiv q order).symm (universalIndex q order)

def singletonStage (q : ℕ) (order : Order) (r : Fin q) : (starInstance q order).Stage :=
  (stageEquiv q order).symm (singletonIndex q order r)

def stageLabel (q : ℕ) (order : Order) (i : (starInstance q order).Stage) : Option (Fin q) :=
  label q order (stageEquiv q order i)

theorem stageLabel_injective (q : ℕ) (order : Order) : Function.Injective (stageLabel q order) :=
  (label_injective q order).comp (stageEquiv q order).injective

theorem stageLabel_universal (q : ℕ) (order : Order) :
    stageLabel q order (universalStage q order) = none := by
  simp only [stageLabel, universalStage, Equiv.apply_symm_apply, label_universalIndex]

theorem stageLabel_singleton (q : ℕ) (order : Order) (r : Fin q) :
    stageLabel q order (singletonStage q order r) = some r := by
  simp only [stageLabel, singletonStage, Equiv.apply_symm_apply, label_singletonIndex]

/-- Reordering preserves the underlying universal/singleton stage label. -/
def orderEquiv (q : ℕ) (left right : Order) :
    (starInstance q left).Stage ≃ (starInstance q right).Stage :=
  (stageEquiv q left).trans ((labelEquiv q left).trans
    ((labelEquiv q right).symm.trans (stageEquiv q right).symm))

theorem orderEquiv_label (q : ℕ) (left right : Order) (i : (starInstance q left).Stage) :
    stageLabel q right (orderEquiv q left right i) = stageLabel q left i := by
  change (labelEquiv q right) ((labelEquiv q right).symm ((labelEquiv q left) (stageEquiv q left i))) = _
  exact Equiv.apply_symm_apply _ _

theorem eligible_formula (q : ℕ) (order : Order) (i : (starInstance q order).Stage) :
    (starInstance q order).eligible i = match stageLabel q order i with
      | none => Finset.univ
      | some r => {r} := by
  change (List.ofFn (eligibility q order)).get i = _
  exact List.get_ofFn (eligibility q order) i

theorem eligible_universal (q : ℕ) (order : Order) :
    (starInstance q order).eligible (universalStage q order) = Finset.univ := by
  rw [eligible_formula, stageLabel_universal]

theorem eligible_singleton (q : ℕ) (order : Order) (r : Fin q) :
    (starInstance q order).eligible (singletonStage q order r) = {r} := by
  rw [eligible_formula, stageLabel_singleton]

theorem laminar (q : ℕ) (order : Order) :
    Structure.LaminarTree.LaminarSchedule (starInstance q order).compatibility := by
  intro left hl right hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  unfold eligibility
  cases hi : label q order i with
  | none => exact Or.inr (Or.inr (Finset.subset_univ _))
  | some r =>
    cases hj : label q order j with
    | none => exact Or.inr (Or.inl (Finset.subset_univ _))
    | some s =>
      by_cases hrs : r = s
      · subst s; exact Or.inr (Or.inl (Finset.Subset.refl _))
      · exact Or.inl (Finset.disjoint_singleton.mpr (by simpa using hrs))

/-- Direct real matching, using one singleton omitted by the error set if
the universal stage itself is erroneous. No rank or matroid axiom is used. -/
theorem matchable_iff_card_le (q : ℕ) (hq : 0 < q) (order : Order)
    (errors : Finset (starInstance q order).Stage) :
    Retained.Matchable (starInstance q order) errors ↔ errors.card ≤ q := by
  constructor
  · exact Retained.Matchable.card_le_tools
  · intro hcard
    have htotal : (Finset.univ : Finset (starInstance q order).Stage).card = q + 1 := by
      simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
      exact stageCount_eq q order
    obtain ⟨missing, _, hmissing⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show errors.card < (Finset.univ : Finset (starInstance q order).Stage).card by omega)
    let fallback : Fin q := (stageLabel q order missing).getD ⟨0, hq⟩
    let assigned : {i : (starInstance q order).Stage // i ∈ errors} → Fin q :=
      fun i => (stageLabel q order i.val).getD fallback
    refine ⟨assigned, ?_, ?_⟩
    · intro i j heq
      change @Eq (Fin q) (assigned i) (assigned j) at heq
      apply Subtype.ext
      apply stageLabel_injective q order
      cases hi : stageLabel q order i.val with
      | none =>
        cases hj : stageLabel q order j.val with
        | none => rfl
        | some r =>
          have hr : fallback = r := by simpa only [assigned, hi, hj, Option.getD_none,
            Option.getD_some] using heq
          cases hm : stageLabel q order missing with
          | none =>
            have him := stageLabel_injective q order (hi.trans hm.symm)
            exact False.elim (hmissing (him ▸ i.property))
          | some s =>
            have hrs : s = r := by simpa only [fallback, hm, Option.getD_some] using hr
            have hjm : j.val = missing := stageLabel_injective q order (by simp only [hj, hm, hrs])
            exact False.elim (hmissing (hjm ▸ j.property))
      | some r =>
        cases hj : stageLabel q order j.val with
        | none =>
          have hr : r = fallback := by simpa only [assigned, hi, hj, Option.getD_none,
            Option.getD_some] using heq
          cases hm : stageLabel q order missing with
          | none =>
            have hjm := stageLabel_injective q order (hj.trans hm.symm)
            exact False.elim (hmissing (hjm ▸ j.property))
          | some s =>
            have hrs : r = s := by simpa only [fallback, hm, Option.getD_some] using hr
            have him : i.val = missing := stageLabel_injective q order (by simp only [hi, hm, hrs])
            exact False.elim (hmissing (him ▸ i.property))
        | some s =>
          have hrs : r = s := by simpa only [assigned, hi, hj, Option.getD_some] using heq
          exact congrArg some hrs
    · intro i
      rw [eligible_formula]
      change assigned i ∈ (match stageLabel q order i.val with
        | none => Finset.univ | some r => {r} : Finset (Fin q))
      cases hi : stageLabel q order i.val with
      | none => exact Finset.mem_univ _
      | some r =>
        simp only [assigned, hi, Option.getD_some]
        exact Finset.mem_singleton_self r

theorem circuit_iff_univ (q : ℕ) (hq : 0 < q) (order : Order)
    (errors : Finset (starInstance q order).Stage) :
    Retained.Circuit (starInstance q order) errors ↔ errors = Finset.univ := by
  have htotal : (Finset.univ : Finset (starInstance q order).Stage).card = q + 1 := by
    simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
    exact stageCount_eq q order
  constructor
  · intro hc
    have hbad : q < errors.card := by
      exact Nat.lt_of_not_ge (fun h => hc.1 ((matchable_iff_card_le q hq order errors).mpr h))
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    omega
  · rintro rfl
    refine ⟨?_, ?_⟩
    · intro hm
      have := (matchable_iff_card_le q hq order Finset.univ).mp hm
      omega

    · intro smaller hproper
      apply (matchable_iff_card_le q hq order smaller).mpr
      have := Finset.card_lt_card hproper
      omega

theorem order_matchable_iff (q : ℕ) (hq : 0 < q) (left right : Order)
    (errors : Finset (starInstance q left).Stage) :
    Retained.Matchable (starInstance q right) (errors.image (orderEquiv q left right)) ↔
      Retained.Matchable (starInstance q left) errors := by
  rw [matchable_iff_card_le q hq right, matchable_iff_card_le q hq left,
    Finset.card_image_of_injective errors (orderEquiv q left right).injective]

theorem girth_eq (q : ℕ) (hq : 0 < q) (order : Order) :
    Retained.girth (starInstance q order) = (q + 1 : ℕ) := by
  have hcircuits : Retained.circuits (starInstance q order) = {Finset.univ} := by
    ext errors
    simp only [Retained.mem_circuits, Finset.mem_singleton, circuit_iff_univ q hq order]
  rw [Retained.girth, hcircuits, Finset.inf_singleton]
  congr 1
  simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
  exact stageCount_eq q order

def firstStage (q : ℕ) (order : Order) : (starInstance q order).Stage :=
  (stageEquiv q order).symm ⟨0, by omega⟩

theorem firstStage_le (q : ℕ) (order : Order) (i : (starInstance q order).Stage) :
    firstStage q order ≤ i := by
  change 0 ≤ i.val
  exact Nat.zero_le _

theorem girthHeads_eq (q : ℕ) (hq : 0 < q) (order : Order) :
    Retained.girthHeads (starInstance q order) = {firstStage q order} := by
  classical
  ext i
  rw [Retained.mem_girthHeads, Finset.mem_singleton]
  constructor
  · rintro ⟨errors, ⟨hc, _, hhead⟩, _⟩
    have hfull := (circuit_iff_univ q hq order errors).mp hc
    subst errors
    exact le_antisymm (hhead _ (Finset.mem_univ _)) (firstStage_le q order i)
  · rintro rfl
    refine ⟨Finset.univ, ⟨(circuit_iff_univ q hq order Finset.univ).mpr rfl,
      Finset.mem_univ _, fun j _ => firstStage_le q order j⟩, ?_⟩
    rw [girth_eq q hq order]
    congr 1
    simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
    exact stageCount_eq q order

theorem retained_initial_rank (q : ℕ) (hq : 0 < q) (order : Order) :
    Retained.errorRank (starInstance q order) (Retained.stagesFrom (starInstance q order) 0) ∅ =
      (q + 1 : ℕ) := by
  rw [Retained.initial_errorRank_eq_girth, girth_eq q hq order]

structure Parameters where
  tools : ℕ
  tools_ge_two : 2 ≤ tools
  channel : Statistics.BinarySymmetric.Parameters
  correctionFee : ℚ
  correctionFee_nonneg : 0 ≤ correctionFee

namespace Parameters

def input (P : Parameters) (order : Order) : StatisticalInput (starInstance P.tools order) where
  experiment := fun _ => P.channel.experiment
  correctionFee := fun _ _ => P.correctionFee
  correctionFee_nonneg := fun _ _ => P.correctionFee_nonneg

theorem observationFee_eq (P : Parameters) (order : Order) (i : (starInstance P.tools order).Stage) :
    (P.input order).fees.observation i = P.channel.reviewFee := rfl

theorem correctionFee_eq (P : Parameters) (order : Order)
    (i : (starInstance P.tools order).Stage) (r : (starInstance P.tools order).Tool) :
    (P.input order).fees.correction i r = P.correctionFee := rfl

theorem local_coefficient_eq (P : Parameters) (order : Order) (i : (starInstance P.tools order).Stage) :
    ((P.input order).experiment i).coefficient = P.channel.a := P.channel.coefficient_eq_a

theorem experiments_agree (P : Parameters) (left right : Order)
    (i : (starInstance P.tools left).Stage) (j : (starInstance P.tools right).Stage) :
    (P.input left).experiment i = (P.input right).experiment j := rfl

/-- I keeps its original execution-deadline parameter: current allocation
does not mean current payment. The three builders share quota/H/H0 verbatim. -/
def currentContract (P : Parameters) (order : Order) (execution : Deadline)
    (quota : (starInstance P.tools order).Stage → ℕ) (H H0 : ℕ) :
    {C : Contract (starInstance P.tools order) // C.IsCurrentAllocation} :=
  ⟨⟨.early, .currentWindow, execution, quota, H, H0⟩, rfl, rfl⟩

def earlyRetainedContract (P : Parameters) (order : Order)
    (quota : (starInstance P.tools order).Stage → ℕ) (H H0 : ℕ) :
    {C : Contract (starInstance P.tools order) // C.IsEarlyRetained} :=
  ⟨⟨.early, .terminalBarrier, .terminalBarrier, quota, H, H0⟩, rfl, rfl, rfl⟩

def lateRetainedContract (P : Parameters) (order : Order)
    (quota : (starInstance P.tools order).Stage → ℕ) (H H0 : ℕ) :
    {C : Contract (starInstance P.tools order) // C.IsLateRetained} :=
  ⟨⟨.late, .terminalBarrier, .terminalBarrier, quota, H, H0⟩, rfl, rfl, rfl⟩

/-- Full randomized visible-history constrained infimum of actual variable
charges. Independent normal charges remain the existing NormalCharges interface. -/
noncomputable def value (P : Parameters) (order : Order) (C : Contract (starInstance P.tools order))
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting (starInstance P.tools order))
    (δ : ℝ≥0∞) : ℝ≥0∞ := Native.value (P.input order) C mode accounting δ

noncomputable def currentValue (P : Parameters) (order : Order)
    (C : {C : Contract (starInstance P.tools order) // C.IsCurrentAllocation})
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting (starInstance P.tools order))
    (δ : ℝ≥0∞) : ℝ≥0∞ := P.value order C.val mode accounting δ

noncomputable def earlyRetainedValue (P : Parameters) (order : Order)
    (C : {C : Contract (starInstance P.tools order) // C.IsEarlyRetained})
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting (starInstance P.tools order))
    (δ : ℝ≥0∞) : ℝ≥0∞ := P.value order C.val mode accounting δ

noncomputable def lateRetainedValue (P : Parameters) (order : Order)
    (C : {C : Contract (starInstance P.tools order) // C.IsLateRetained})
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting (starInstance P.tools order))
    (δ : ℝ≥0∞) : ℝ≥0∞ := P.value order C.val mode accounting δ

theorem uncappedValue_le_nativeValue (P : Parameters) (order : Order)
    (C : Contract (starInstance P.tools order))
    (accounting : Native.NormalAccounting (starInstance P.tools order)) (δ : ℝ≥0∞) :
    P.value order C .uncapped accounting δ ≤ P.value order C .native accounting δ :=
  Native.value_uncapped_le_native (P.input order) C accounting δ

/-- C02 claims over the original independent allocation-game semantics and
the existing ordered symbolic coefficient. These are not assumptions on P. -/
def OrderedRankCoefficientClaims (P : Parameters) : Prop :=
  Structure.initialRank (starInstance P.tools .universalFirst) = 2 ∧
  (P.input .universalFirst).orderedCoefficient (starInstance P.tools .universalFirst).tools = P.channel.a ∧
  Structure.initialRank (starInstance P.tools .singletonsFirst) = (P.tools + 1 : ℕ) ∧
  (P.input .singletonsFirst).orderedCoefficient (starInstance P.tools .singletonsFirst).tools = P.channel.a

end Parameters
end PaperProofs.Star
