module

public import PaperProofs.Common.WorldFreshness
public import PaperProofs.Common.NativeRun
public import Mathlib.Data.Nat.Find

/-!
The actual native entry history, including runs that never enter a stage.
Its factorization through the private seed and earlier hidden stages is an
explicit outstanding causal obligation. The conditional freshness theorem
uses that factorization together with the already-proved independent world;
it does not assume the desired independence under a renamed hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PaperProofs.Common.Native

variable {I : Instance}

abbrev EntryHistory (I : Instance) := Option (List (VisibleEvent I))

instance : MeasurableSpace (EntryHistory I) := ⊤
instance : MeasurableSingletonClass (EntryHistory I) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section Entry

variable {Seed : Type*}

/-- The visible history at the first interpreter clock with the requested cursor.
No entry gives `none`; no eventual-success or finite-stopping assumption is used. -/
noncomputable def entryHistory (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (next : I.Stage) (sample : Seed × input.World) : EntryHistory I := by
  classical
  exact if h : ∃ n : ℕ, (run input C mode accounting policy sample n).cursor = next.val
    then some (run input C mode accounting policy sample (Nat.find h)).history
    else none

theorem entryHistory_none_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (next : I.Stage) (sample : Seed × input.World) :
    entryHistory input C mode accounting policy next sample = none ↔
      ¬ ∃ n : ℕ, (run input C mode accounting policy sample n).cursor = next.val := by
  classical
  by_cases h : ∃ n : ℕ, (run input C mode accounting policy sample n).cursor = next.val
  · simp [entryHistory, h]
  · simp [entryHistory, h]

theorem entryHistory_some_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (next : I.Stage) (sample : Seed × input.World) (history : List (VisibleEvent I)) :
    entryHistory input C mode accounting policy next sample = some history ↔
      ∃ n : ℕ,
        (run input C mode accounting policy sample n).cursor = next.val ∧
        (∀ k < n, (run input C mode accounting policy sample k).cursor ≠ next.val) ∧
        (run input C mode accounting policy sample n).history = history := by
  classical
  constructor
  · intro hh
    by_cases he : ∃ n : ℕ, (run input C mode accounting policy sample n).cursor = next.val
    · have hhistory : (run input C mode accounting policy sample (Nat.find he)).history = history := by
        simpa [entryHistory, he] using hh
      exact ⟨Nat.find he, Nat.find_spec he, fun _ hk => Nat.find_min he hk, hhistory⟩
    · simp [entryHistory, he] at hh
  · rintro ⟨n, hn, hbefore, hhistory⟩
    have he : ∃ k : ℕ, (run input C mode accounting policy sample k).cursor = next.val := ⟨n, hn⟩
    have hfind : Nat.find he = n := (Nat.find_eq_iff he).mpr ⟨hn, hbefore⟩
    simp [entryHistory, he, hfind, hhistory]

theorem entryHistory_stageZero (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (next : I.Stage) (hzero : next.val = 0) (sample : Seed × input.World) :
    entryHistory input C mode accounting policy next sample = some [] := by
  apply (entryHistory_some_iff input C mode accounting policy next sample []).mpr
  refine ⟨0, ?_, ?_, rfl⟩
  · simpa only [run, initial] using hzero.symm
  · intro k hk
    exact ((Nat.not_lt_zero k) hk).elim

variable [MeasurableSpace Seed]

theorem measurable_entryHistory (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (next : I.Stage) :
    Measurable (entryHistory input C mode accounting policy next) := by
  have hcursor (n : ℕ) : MeasurableSet {sample : Seed × input.World |
      (run input C mode accounting policy sample n).cursor = next.val} :=
    (measurable_run input C mode accounting policy hpolicy n)
      (MeasurableSpace.measurableSet_top (s := {s : State I | s.cursor = next.val}))
  apply measurable_to_countable'
  intro outcome
  cases outcome with
  | none =>
    have heq : (entryHistory input C mode accounting policy next) ⁻¹' {none} =
        (⋃ n : ℕ, {sample : Seed × input.World |
          (run input C mode accounting policy sample n).cursor = next.val})ᶜ := by
      ext sample
      simp only [Set.mem_preimage, Set.mem_singleton_iff, entryHistory_none_iff,
        Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [heq]
    exact (MeasurableSet.iUnion hcursor).compl
  | some history =>
    have hhistory (n : ℕ) : MeasurableSet {sample : Seed × input.World |
        (run input C mode accounting policy sample n).history = history} :=
      (measurable_run input C mode accounting policy hpolicy n)
        (MeasurableSpace.measurableSet_top (s := {s : State I | s.history = history}))
    have heq : (entryHistory input C mode accounting policy next) ⁻¹' {some history} =
        ⋃ n : ℕ, {sample : Seed × input.World |
            (run input C mode accounting policy sample n).cursor = next.val} ∩
          ((⋂ k : ℕ, {sample : Seed × input.World |
            k < n → (run input C mode accounting policy sample k).cursor ≠ next.val}) ∩
          {sample : Seed × input.World |
            (run input C mode accounting policy sample n).history = history}) := by
      ext sample
      simp only [Set.mem_preimage, Set.mem_singleton_iff, entryHistory_some_iff,
        Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    refine (hcursor n).inter ((MeasurableSet.iInter fun k => ?_).inter (hhistory n))
    by_cases hk : k < n
    · have hs : {sample : Seed × input.World |
          k < n → (run input C mode accounting policy sample k).cursor ≠ next.val} =
          {sample : Seed × input.World |
            (run input C mode accounting policy sample k).cursor = next.val}ᶜ := by
        ext sample
        simp [hk]
      rw [hs]
      exact (hcursor k).compl
    · simp [hk]

end Entry

/-- Causal factorization statement, proved from actual steps in NativeCausality,
quantified over the same arbitrary small
private-seed spaces and legal measurable policies as the native value comparator.
This is not an assumed input field and contains no independence assertion. -/
def NativePreBirthFactorization (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) : Prop :=
  ∀ (Seed : Type) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (policy : Policy input C mode accounting Seed) (next : I.Stage),
      ∃ record : Seed × input.PastWorld next → EntryHistory I,
        Measurable record ∧ ∀ sample : Seed × input.World,
          entryHistory input C mode accounting policy.rule next sample =
            record (input.preBirthView next sample)

section Freshness

variable {Seed : Type} [MeasurableSpace Seed]

theorem entryHistory_independent_next_of_factorization (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (hfactor : NativePreBirthFactorization input C mode accounting)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    IndepFun (entryHistory input C mode accounting policy.rule next)
      (fun sample : Seed × input.World => sample.2 next) (input.seededWorldLaw ν) := by
  obtain ⟨record, hrecord, hpointwise⟩ := hfactor Seed ‹MeasurableSpace Seed› policy next
  have heq : entryHistory input C mode accounting policy.rule next =
      (fun sample => record (input.preBirthView next sample)) := funext hpointwise
  rw [heq]
  exact input.preBirthRecord_independent_next ν next record hrecord

theorem entryHistory_next_marginal (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample => sample.2 next) = input.stageLaw next :=
  input.seededWorldLaw_coordinate ν next

theorem entryHistory_jointLaw_of_factorization (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (hfactor : NativePreBirthFactorization input C mode accounting)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample =>
        (entryHistory input C mode accounting policy.rule next sample, sample.2 next)) =
      ((input.seededWorldLaw ν).map (entryHistory input C mode accounting policy.rule next)).prod
        (input.stageLaw next) := by
  have hnext : Measurable (fun sample : Seed × input.World => sample.2 next) :=
    (measurable_pi_apply next).comp measurable_snd
  have hind := entryHistory_independent_next_of_factorization input C mode accounting
    hfactor policy ν next
  have hentry := measurable_entryHistory input C mode accounting policy.rule policy.measurable_rule next
  rw [hind.map_prod_eq_prod_map_map hentry.aemeasurable hnext.aemeasurable,
    input.seededWorldLaw_coordinate]

/-- The clock-zero boundary case of causal factorization is already unconditional. -/
theorem entryHistory_stageZero_record (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (next : I.Stage) (hzero : next.val = 0) :
    ∃ record : Seed × input.PastWorld next → EntryHistory I,
      Measurable record ∧ ∀ sample : Seed × input.World,
        entryHistory input C mode accounting policy.rule next sample =
          record (input.preBirthView next sample) := by
  refine ⟨fun _ => some [], measurable_const, ?_⟩
  intro sample
  exact entryHistory_stageZero input C mode accounting policy.rule next hzero sample

end Freshness

end PaperProofs.Common.Native
