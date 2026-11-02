module

public import PaperProofs.Structure.RawCandidateOrder
public import PaperProofs.Structure.AlgorithmClaims

/-! Pure flag invariant for the actual all-later-candidates retention
scan.  Empty supports and already-zero flags still admit every scan step;
there is no early exit or assumption of distinct input stages. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateRetentionFlags

open RawCandidateOrder AlgorithmClaims

def support (q : Nat) (full : List (Finset (Fin q))) (index : Nat) : Finset (Fin q) :=
  (candidateSupports q full).getD index ∅

/-- `upto` is the next candidate to scan; all later candidates strictly
below it have already been compared with `index`. -/
def PartialKeep (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat) : Prop :=
  (support q full index).Nonempty ∧
    ∀ later < upto, index < later → support q full later ≠ support q full index

instance (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat) :
    Decidable (PartialKeep q full index upto) := by
  unfold PartialKeep
  infer_instance

def partialFlag (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat) : Nat :=
  bit (decide (PartialKeep q full index upto))

theorem partialKeep_initial (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    PartialKeep q full index (index + 1) ↔ (support q full index).Nonempty := by
  constructor
  · exact And.left
  · intro hnonempty
    exact ⟨hnonempty, fun _ hlater hafter => by omega⟩

theorem partialFlag_initial (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    partialFlag q full index (index + 1) = bit (decide (support q full index).Nonempty) := by
  simp only [partialFlag, partialKeep_initial]

theorem partialKeep_step (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat)
    (hafter : index < upto) :
    PartialKeep q full index (upto + 1) ↔
      PartialKeep q full index upto ∧ support q full upto ≠ support q full index := by
  constructor
  · rintro ⟨hnonempty, hcompared⟩
    exact ⟨⟨hnonempty, fun later hlater hi => hcompared later (by omega) hi⟩,
      hcompared upto (by omega) hafter⟩
  · rintro ⟨⟨hnonempty, hcompared⟩, hnew⟩
    refine ⟨hnonempty, ?_⟩
    intro later hlater hi
    by_cases heq : later = upto
    · simpa only [heq] using hnew
    · exact hcompared later (by omega) hi

theorem partialFlag_step (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat)
    (hafter : index < upto) :
    partialFlag q full index (upto + 1) =
      if support q full index = support q full upto then 0 else partialFlag q full index upto := by
  simp only [partialFlag, partialKeep_step q full index upto hafter]
  by_cases heq : support q full index = support q full upto
  · simp [heq, bit]
  · have hne : support q full upto ≠ support q full index := Ne.symm heq
    simp [heq, hne]

theorem partialKeep_full (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    PartialKeep q full index (full.length + q + 1) ↔ keepCandidate q full index = true := by
  rw [keepCandidate_iff_no_later_index]
  constructor
  · rintro ⟨hnonempty, hcompared⟩
    exact ⟨hnonempty, fun later hi hlater => hcompared later hlater hi⟩
  · rintro ⟨hnonempty, hcompared⟩
    exact ⟨hnonempty, fun later hlater hi => hcompared later hi hlater⟩

theorem partialFlag_full (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    partialFlag q full index (full.length + q + 1) = bit (keepCandidate q full index) := by
  simp only [partialFlag, partialKeep_full, Bool.decide_eq_true]

theorem differenceCount_eq_zero_iff {q : Nat} (left right : Finset (Fin q)) :
    (left \ right).card + (right \ left).card = 0 ↔ left = right := by
  constructor
  · intro hzero
    obtain ⟨hl, hr⟩ := Nat.add_eq_zero_iff.mp hzero
    exact Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hl))
      (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hr))
  · rintro rfl
    simp

/-- The machine tests the two directed-difference counters, rather than
calling a set-equality oracle. -/
theorem partialFlag_step_of_differenceCount (q : Nat) (full : List (Finset (Fin q)))
    (index upto : Nat) (hafter : index < upto) :
    partialFlag q full index (upto + 1) =
      if (support q full index \ support q full upto).card +
          (support q full upto \ support q full index).card = 0 then 0
      else partialFlag q full index upto := by
  rw [partialFlag_step q full index upto hafter]
  simp only [differenceCount_eq_zero_iff]

/-- The specialized sequential scan: the seed is the original nonempty
bit, and step `count` compares exactly the next raw ID `index+1+count`. -/
def retentionFlag (q : Nat) (full : List (Finset (Fin q))) (index : Nat) : Nat → Nat
  | 0 => bit (decide (support q full index).Nonempty)
  | count + 1 => if support q full index = support q full (index + 1 + count) then 0
      else retentionFlag q full index count

theorem retentionFlag_eq_partialFlag (q : Nat) (full : List (Finset (Fin q)))
    (index count : Nat) :
    retentionFlag q full index count = partialFlag q full index (index + 1 + count) := by
  induction count with
  | zero => simpa only [retentionFlag, Nat.add_zero] using (partialFlag_initial q full index).symm
  | succ count ih =>
    rw [retentionFlag, ih, show index + 1 + (count + 1) = (index + 1 + count) + 1 by omega,
      partialFlag_step q full index (index + 1 + count) (by omega)]

theorem retentionFlag_full (q : Nat) (full : List (Finset (Fin q))) (index : Nat)
    (hindex : index < full.length + q + 1) :
    retentionFlag q full index (full.length + q + 1 - (index + 1)) = bit (keepCandidate q full index) := by
  rw [retentionFlag_eq_partialFlag,
    show index + 1 + (full.length + q + 1 - (index + 1)) = full.length + q + 1 by omega,
    partialFlag_full]

end PaperProofs.Structure.LaminarTree.RawCandidateRetentionFlags
