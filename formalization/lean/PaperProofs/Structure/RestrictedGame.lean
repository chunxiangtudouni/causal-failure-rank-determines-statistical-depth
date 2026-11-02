module

public import PaperProofs.Common.SuffixInput
public import PaperProofs.Structure.Game
public import Mathlib.Data.Finset.Basic

/-!
Restricting every eligibility set to R is the same independent causal game
as starting with only the remaining tools intersected with R. This proof uses
the operational game's proved budget recurrence, never a capacity table.
The resulting bridge applies to the actual common suffix input for every n.
-/

@[expose] public section

namespace PaperProofs.Structure

variable {Tool : Type*} [DecidableEq Tool]

theorem safe_restrict_iff (schedule : List (Finset Tool)) (restriction remaining : Finset Tool)
    (budget : Nat) :
    Safe (schedule.map (fun eligible => eligible ∩ restriction)) remaining budget ↔
      Safe schedule (remaining ∩ restriction) budget := by
  induction schedule generalizing remaining budget with
  | nil => simp only [List.map_nil, safe_terminal]
  | cons eligible later ih =>
    cases budget with
    | zero => exact ⟨fun _ => safe_zero _ _, fun _ => safe_zero _ _⟩
    | succ budget =>
      rw [List.map_cons, safe_cons_succ_iff, safe_cons_succ_iff]
      constructor
      · rintro ⟨hgood, tool, htool, hbad⟩
        refine ⟨(ih remaining (budget + 1)).mp hgood, tool, ?_, ?_⟩
        · simpa only [Finset.mem_inter, and_assoc, and_left_comm, and_comm] using htool
        · simpa only [Finset.erase_inter] using (ih (remaining.erase tool) budget).mp hbad
      · rintro ⟨hgood, tool, htool, hbad⟩
        refine ⟨(ih remaining (budget + 1)).mpr hgood, tool, ?_, ?_⟩
        · simpa only [Finset.mem_inter, and_assoc, and_left_comm, and_comm] using htool
        · apply (ih (remaining.erase tool) budget).mpr
          simpa only [Finset.erase_inter] using hbad

theorem errorRank_restrict (schedule : List (Finset Tool)) (restriction remaining : Finset Tool) :
    errorRank (schedule.map (fun eligible => eligible ∩ restriction)) remaining =
      errorRank schedule (remaining ∩ restriction) := by
  classical
  unfold errorRank
  simp only [safe_restrict_iff]

end PaperProofs.Structure

namespace PaperProofs.Common

theorem Instance.suffixRestricted_safe (I : Instance) (next : Nat) (remaining : Finset I.Tool)
    (budget : Nat) :
    Structure.Safe (I.suffixRestricted next remaining).compatibility
      (I.suffixRestricted next remaining).tools budget ↔
        Structure.Safe (I.compatibility.drop next) remaining budget := by
  change Structure.Safe ((I.compatibility.drop next).map (fun eligible => eligible ∩ remaining))
    Finset.univ budget ↔ _
  simpa only [Finset.univ_inter] using
    Structure.safe_restrict_iff (I.compatibility.drop next) remaining Finset.univ budget

theorem Instance.suffixRestricted_rank (I : Instance) (next : Nat) (remaining : Finset I.Tool) :
    Structure.errorRank (I.suffixRestricted next remaining).compatibility
      (I.suffixRestricted next remaining).tools =
        Structure.errorRank (I.compatibility.drop next) remaining := by
  change Structure.errorRank ((I.compatibility.drop next).map (fun eligible => eligible ∩ remaining))
    Finset.univ = _
  simpa only [Finset.univ_inter] using
    Structure.errorRank_restrict (I.compatibility.drop next) remaining Finset.univ

end PaperProofs.Common
