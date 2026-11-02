module

public import PaperProofs.Common.NativeProtocol
public import PaperProofs.Common.World
public import PaperProofs.Common.Value
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
Actual seeded native execution and its probability/cost interface.

Discrete state, actions and visible histories are countable. A finite frontier
of potential tape symbols is used only to factor the system transition for
measurability; it is not passed to the policy. The protocol equivalence below
ensures that a step consumes only the observation of its actual review action.

Malformed actions have a total failure completion. `LegalRule` must separately
prove that this completion is never used on a reached active legal path.
Infinite observation paths retain the supremum of every charged finite prefix;
an incomplete run is not converted to an infinite number of paid observations.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

instance : MeasurableSpace (Ledger I) := ⊤
instance : MeasurableSingletonClass (Ledger I) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
instance : MeasurableSpace (State I) := ⊤
instance : MeasurableSingletonClass (State I) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
instance : MeasurableSpace (Action I) := ⊤
instance : MeasurableSingletonClass (Action I) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
instance : MeasurableSpace (VisibleEvent I) := ⊤
instance : MeasurableSingletonClass (VisibleEvent I) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
instance : MeasurableSpace (List (VisibleEvent I)) := ⊤
instance : MeasurableSingletonClass (List (VisibleEvent I)) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

abbrev Frontier (input : StatisticalInput I) :=
  (i : I.Stage) → Fin (input.experiment i).alphabetSize

def worldTapes (input : StatisticalInput I) (world : input.World) : ReviewTapes input :=
  input.reviewAt world

def frontierOf (input : StatisticalInput I) (s : State I) (world : input.World) : Frontier input :=
  fun i ↦ input.reviewAt world i (s.ledger.reviews i).toNat

def frozenTapes (input : StatisticalInput I) (frontier : Frontier input) : ReviewTapes input :=
  fun i _ ↦ frontier i

theorem step_world_frontier_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (world : input.World)
    (s s' : State I) (action : Action I) :
    Step input C mode accounting (worldTapes input world) s action s' ↔
      Step input C mode accounting (frozenTapes input (frontierOf input s world)) s action s' := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

/-- A transition selected from the actual protocol graph, with explicit failure
completion only when no native transition exists. This is a semantics, not an
efficient-controller implementation or an oracle granted to a policy. -/
noncomputable def nextFromFrontier (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (frontier : Frontier input) : State I := by
  classical
  exact if s.halted then s else
    if h : ∃ s', Step input C mode accounting (frozenTapes input frontier) s action s'
    then Classical.choose h else stopState s true

theorem nextFromFrontier_eq_of_step (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s s' : State I)
    (action : Action I) (frontier : Frontier input) (hactive : s.halted = false)
    (hstep : Step input C mode accounting (frozenTapes input frontier) s action s') :
    nextFromFrontier input C mode accounting s action frontier = s' := by
  classical
  have hex : ∃ next, Step input C mode accounting (frozenTapes input frontier) s action next :=
    ⟨s', hstep⟩
  simp only [nextFromFrontier, hactive, Bool.false_eq_true, ↓reduceIte, dite_eq_left hex]
  exact step_deterministic input C mode accounting _ (Classical.choose_spec hex) hstep

theorem measurable_frontierOf (input : StatisticalInput I) :
    Measurable (fun p : State I × input.World ↦ frontierOf input p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro s
  exact measurable_pi_iff.mpr fun i ↦ input.measurable_reviewAt i (s.ledger.reviews i).toNat

theorem measurable_initial_world (input : StatisticalInput I) :
    Measurable (fun world : input.World ↦ initial (input.truthAt world)) := by
  have htruth : Measurable (fun world : input.World ↦ input.truthAt world) :=
    measurable_pi_iff.mpr fun i ↦ input.measurable_truthAt i
  exact (measurable_of_countable (fun truth : I.Stage → Bool ↦ initial truth)).comp htruth

section Policy

variable {Seed : Type*} [MeasurableSpace Seed]

def MeasurableRule (policy : PolicyRule I Seed) : Prop :=
  Measurable (fun p : Seed × List (VisibleEvent I) ↦ policy p.1 p.2)

/-- All policies are conditional on arbitrary private randomness. Measurability
and native legality are the only admissibility constraints; no risk, MAP,
successful-path, Markov, or performance condition is inserted here. -/
structure Policy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (Seed : Type*) [MeasurableSpace Seed] where
  rule : PolicyRule I Seed
  measurable_rule : MeasurableRule rule
  legal : LegalRule input C mode accounting rule

noncomputable def run (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) : ℕ → State I
  | 0 => initial (input.truthAt sample.2)
  | n + 1 =>
    let s := run input C mode accounting policy sample n
    nextFromFrontier input C mode accounting s (policy sample.1 s.history)
      (frontierOf input s sample.2)

theorem measurable_run (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (n : ℕ) :
    Measurable (fun sample : Seed × input.World ↦ run input C mode accounting policy sample n) := by
  induction n with
  | zero => exact (measurable_initial_world input).comp measurable_snd
  | succ n ih =>
    have hh : Measurable (fun sample : Seed × input.World ↦
        (run input C mode accounting policy sample n).history) :=
      (measurable_of_countable (fun s : State I ↦ s.history)).comp ih
    have ha := hpolicy.comp (measurable_fst.prodMk hh)
    have hf := (measurable_frontierOf input).comp (ih.prodMk measurable_snd)
    have hn : Measurable (fun p : State I × Action I × Frontier input ↦
        nextFromFrontier input C mode accounting p.1 p.2.1 p.2.2) :=
      measurable_of_countable _
    exact hn.comp (ih.prodMk (ha.prodMk hf))

/-- Eventual successful completion; every incomplete or abandoned run fails. -/
def runSuccess (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) : Prop :=
  ∃ n, (run input C mode accounting policy sample n).halted = true ∧
    (run input C mode accounting policy sample n).ledger.success C

noncomputable def runActualBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ n, (run input C mode accounting policy sample n).ledger.actualBill input.fees

theorem measurable_runActualBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) :
    Measurable (runActualBill input C mode accounting policy) := by
  apply Measurable.iSup
  intro n
  exact (measurable_of_countable (fun s : State I ↦ s.ledger.actualBill input.fees)).comp
    (measurable_run input C mode accounting policy hpolicy n)

theorem measurableSet_runSuccess (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) :
    MeasurableSet {sample | runSuccess input C mode accounting policy sample} := by
  have hset (n : ℕ) : MeasurableSet {sample : Seed × input.World |
      (run input C mode accounting policy sample n).halted = true ∧
        (run input C mode accounting policy sample n).ledger.success C} :=
    (measurable_run input C mode accounting policy hpolicy n)
      (MeasurableSpace.measurableSet_top (s := {s : State I |
        s.halted = true ∧ s.ledger.success C}))
  have heq : {sample | runSuccess input C mode accounting policy sample} =
      ⋃ n : ℕ, {sample : Seed × input.World |
        (run input C mode accounting policy sample n).halted = true ∧
          (run input C mode accounting policy sample n).ledger.success C} := by
    ext sample
    simp [runSuccess]
  rw [heq]
  exact MeasurableSet.iUnion hset

noncomputable def risk (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (ν : Measure Seed) : ℝ≥0∞ :=
  input.seededWorldLaw ν {sample | ¬ runSuccess input C mode accounting policy sample}

noncomputable def expectedBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (ν : Measure Seed) : ℝ≥0∞ :=
  ∫⁻ sample, runActualBill input C mode accounting policy sample ∂input.seededWorldLaw ν

/-- Same protocol/rights/payment contract; only `mode` changes when caps are relaxed.
This is a real-policy infimum, not a Bellman recurrence. The private-seed and
nonreturned-action representation theorems are in NativeSeed/NativePartial;
normal-charge and constructed-controller call certificates are separate. -/
noncomputable def value (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Seed : Type), ⨅ (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ⨅ (ν : Measure Seed) (_h : IsProbabilityMeasure ν),
      ⨅ p : {p : Policy input C mode accounting Seed // risk input C mode accounting p.rule ν ≤ δ},
        expectedBill input C mode accounting p.val.rule ν

end Policy

end PaperProofs.Common.Native
