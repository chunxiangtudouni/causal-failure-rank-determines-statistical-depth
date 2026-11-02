module

public import PaperProofs.Common.Model
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.ENat.Lattice

set_option autoImplicit false
set_option warningAsError true

/-!
Finite semantics for `prices.tex:98-106`: a retained error set is matchable
exactly when it admits distinct compatible actual tools. Circuits, girth and
minimum-circuit heads below are defined from this predicate itself. The
matroid representation/exchange propositions are stated independently and
remain proof obligations; they are not fields of the input instance.
No efficient general girth oracle or native terminal controller is asserted.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Retained

open Common

abbrev Matching (I : Instance) (errors : Finset I.Stage) := hallMatchingsOn I.eligible errors

def Matchable (I : Instance) (errors : Finset I.Stage) : Prop :=
  (hallMatchingsOn I.eligible errors).Nonempty

instance matchable_decidable (I : Instance) : DecidablePred (Matchable I) :=
  fun _ => by unfold Matchable hallMatchingsOn Set.Nonempty Function.Injective; infer_instance

theorem matchable_iff_matching (I : Instance) (errors : Finset I.Stage) :
    Matchable I errors ↔ Nonempty (Matching I errors) := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f, hf⟩⟩
  · rintro ⟨⟨f, hf⟩⟩
    exact ⟨f, hf⟩

/-- Reuses Mathlib's finite Hall theorem on the actual error-index subtype. -/
theorem matchable_iff_hall (I : Instance) (errors : Finset I.Stage) :
    Matchable I errors ↔
      ∀ s : Finset {i : I.Stage // i ∈ errors},
        s.card ≤ (s.biUnion (fun i => I.eligible i.val)).card := by
  exact (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun i : {i : I.Stage // i ∈ errors} => I.eligible i.val)).symm

theorem matchable_empty (I : Instance) : Matchable I ∅ := by
  unfold Matchable hallMatchingsOn Set.Nonempty
  refine ⟨fun i : {i : I.Stage // i ∈ (∅ : Finset I.Stage)} =>
    False.elim ((Finset.notMem_empty i.val) i.property), ?_, ?_⟩
  · intro i
    exact False.elim ((Finset.notMem_empty i.val) i.property)
  · intro i
    exact False.elim ((Finset.notMem_empty i.val) i.property)

theorem Matchable.subset {I : Instance} {small large : Finset I.Stage}
    (hlarge : Matchable I large) (hsubset : small ⊆ large) : Matchable I small := by
  rcases hlarge with ⟨f, hf⟩
  let restricted := hallMatchingsOn.restrict I.eligible hsubset ⟨f, hf⟩
  exact ⟨restricted.val, restricted.property⟩

theorem Matchable.card_le_tools {I : Instance} {errors : Finset I.Stage}
    (h : Matchable I errors) : errors.card ≤ I.toolCount := by
  rcases h with ⟨f, hinj, _⟩
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Instance.Tool, Fintype.card_fin] using hcard

def Circuit (I : Instance) (errors : Finset I.Stage) : Prop :=
  ¬ Matchable I errors ∧ ∀ smaller : Finset I.Stage, smaller ⊂ errors → Matchable I smaller

instance circuit_decidable (I : Instance) : DecidablePred (Circuit I) :=
  fun _ => by unfold Circuit; infer_instance

theorem Circuit.nonempty {I : Instance} {errors : Finset I.Stage} (h : Circuit I errors) :
    errors.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  exact h.1 (hempty ▸ matchable_empty I)

theorem Circuit.card_pos {I : Instance} {errors : Finset I.Stage} (h : Circuit I errors) :
    0 < errors.card := Finset.card_pos.mpr h.nonempty

/-- Minimal unmatchable subsets exist by finite cardinal minimization; this
does not rely on, or prove, the exchange axiom. -/
theorem exists_circuit_subset {I : Instance} {errors : Finset I.Stage}
    (h : ¬ Matchable I errors) : ∃ circuit ⊆ errors, Circuit I circuit := by
  have hex : ∃ n : ℕ, ∃ subset : Finset I.Stage,
      subset ⊆ errors ∧ subset.card = n ∧ ¬ Matchable I subset :=
    ⟨errors.card, errors, Finset.Subset.refl _, rfl, h⟩
  obtain ⟨circuit, hsub, hcard, hbad⟩ := Nat.find_spec hex
  refine ⟨circuit, hsub, hbad, ?_⟩
  intro smaller hproper
  by_contra hbadSmall
  have hmin : Nat.find hex ≤ smaller.card := Nat.find_min' hex
    ⟨smaller, hproper.subset.trans hsub, rfl, hbadSmall⟩
  have hlt := Finset.card_lt_card hproper
  rw [hcard] at hlt
  omega

def circuits (I : Instance) : Finset (Finset I.Stage) :=
  Finset.univ.powerset.filter (Circuit I)

theorem mem_circuits (I : Instance) (errors : Finset I.Stage) :
    errors ∈ circuits I ↔ Circuit I errors := by simp [circuits]

/-- Infinity is the minimum over no circuits. The finite fold here is a
semantic definition and makes no polynomial-time oracle claim. -/
noncomputable def girth (I : Instance) : ℕ∞ :=
  (circuits I).inf (fun errors => (errors.card : ℕ∞))

theorem girth_le_card {I : Instance} {errors : Finset I.Stage} (h : Circuit I errors) :
    girth I ≤ (errors.card : ℕ∞) :=
  Finset.inf_le ((mem_circuits I errors).mpr h)

theorem one_le_girth (I : Instance) : 1 ≤ girth I := by
  apply Finset.le_inf
  intro errors herrors
  have hpos := ((mem_circuits I errors).mp herrors).card_pos
  exact_mod_cast hpos

theorem girth_eq_top_iff_no_circuit (I : Instance) :
    girth I = ⊤ ↔ ∀ errors, ¬ Circuit I errors := by
  constructor
  · intro htop errors hc
    have hle := girth_le_card hc
    rw [htop] at hle
    exact ENat.natCast_ne_top _ (top_le_iff.mp hle)
  · intro hnone
    have hempty : circuits I = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro errors hmem
      exact hnone errors ((mem_circuits I errors).mp hmem)
    simp only [girth, hempty, Finset.inf_empty]

theorem girth_eq_top_iff_matchable_univ (I : Instance) :
    girth I = ⊤ ↔ Matchable I Finset.univ := by
  rw [girth_eq_top_iff_no_circuit]
  constructor
  · intro hnone
    by_contra hbad
    obtain ⟨circuit, _, hcircuit⟩ := exists_circuit_subset hbad
    exact hnone circuit hcircuit
  · intro hall errors hbad
    exact hbad.1 (hall.subset (Finset.subset_univ errors))

theorem minimum_circuit_exists (I : Instance) (hfinite : girth I ≠ ⊤) :
    ∃ errors, Circuit I errors ∧ girth I = (errors.card : ℕ∞) := by
  have hnonempty : (circuits I).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    exact hfinite (by simp only [girth, hempty, Finset.inf_empty])
  obtain ⟨errors, hmem, heq⟩ := Finset.exists_mem_eq_inf
    (circuits I) hnonempty (fun errors => (errors.card : ℕ∞))
  exact ⟨errors, (mem_circuits I errors).mp hmem, heq⟩

def CircuitHead (I : Instance) (errors : Finset I.Stage) (i : I.Stage) : Prop :=
  Circuit I errors ∧ i ∈ errors ∧ ∀ j ∈ errors, i ≤ j

noncomputable def girthHeads (I : Instance) : Finset I.Stage := by
  classical
  exact Finset.univ.filter (fun i => ∃ errors, CircuitHead I errors i ∧
    (errors.card : ℕ∞) = girth I)

theorem mem_girthHeads (I : Instance) (i : I.Stage) :
    i ∈ girthHeads I ↔ ∃ errors, CircuitHead I errors i ∧ (errors.card : ℕ∞) = girth I := by
  simp [girthHeads]

theorem girthHeads_nonempty (I : Instance) (hfinite : girth I ≠ ⊤) :
    (girthHeads I).Nonempty := by
  obtain ⟨errors, hcircuit, hgirth⟩ := minimum_circuit_exists I hfinite
  let first := errors.min' hcircuit.nonempty
  refine ⟨first, (mem_girthHeads I first).mpr ⟨errors, ?_, hgirth.symm⟩⟩
  exact ⟨hcircuit, Finset.min'_mem _ _, fun j hj => Finset.min'_le _ _ hj⟩

/-- Exact outstanding R01 matroid-encoding obligation. It is not assumed by
the definitions or elementary matching/circuit results above. -/
def TransversalMatroidCorrespondence (I : Instance) : Prop :=
  ∃ M : Matroid I.Stage, M.E = Set.univ ∧
    ∀ errors : Finset I.Stage, M.Indep (errors : Set I.Stage) ↔ Matchable I errors

/-- The finite exchange theorem remains a separate proof obligation. -/
def MatchingAugmentation (I : Instance) : Prop :=
  ∀ small large : Finset I.Stage, Matchable I small → Matchable I large →
    small.card < large.card → ∃ i ∈ large \ small, Matchable I (insert i small)

end PaperProofs.Retained
