module

public import PaperProofs.Paid.CalibratedBackend
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid
open PaperProofs.Paid.Parameters

namespace PDROC

/-- The literal additive cell update used by the original walkUpdate. -/
def endpointArrayBump (row : Array ℚ) (index : ℕ) (amount : ℚ) : Array ℚ :=
  row.setIfInBounds index (row.getD index 0 + amount)

@[simp] theorem endpointArrayBump_size (row : Array ℚ) (index : ℕ) (amount : ℚ) :
    (endpointArrayBump row index amount).size = row.size := by
  simp only [endpointArrayBump, Array.size_setIfInBounds]

/-- Repeated targets accumulate; absorbed boundary commands are not deduplicated. -/
theorem endpointArrayBump_getD (row : Array ℚ) (index query : ℕ) (amount : ℚ)
    (hi : index < row.size) :
    (endpointArrayBump row index amount).getD query 0 =
      row.getD query 0 + if index = query then amount else 0 := by
  unfold endpointArrayBump
  rw [Array.getD_eq_getD_getElem?]
  by_cases he : index = query
  · subst query
    rw [Array.getElem?_setIfInBounds_self_of_lt hi]
    simp only [Option.getD_some, ite_true]
  · rw [Array.getElem?_setIfInBounds_ne he]
    simp only [← Array.getD_eq_getD_getElem?, he, ite_false, add_zero]

def endpointArrayScatter {n : ℕ} (commands : List (Fin n × ℚ)) (initial : Array ℚ) : Array ℚ :=
  commands.foldl (fun row command => endpointArrayBump row command.1.val command.2) initial

@[simp] theorem endpointArrayScatter_size {n : ℕ} (commands : List (Fin n × ℚ)) (initial : Array ℚ) :
    (endpointArrayScatter commands initial).size = initial.size := by
  induction commands generalizing initial with
  | nil => rfl
  | cons command rest ih =>
    change (endpointArrayScatter rest (endpointArrayBump initial command.1.val command.2)).size = initial.size
    exact (ih _).trans (endpointArrayBump_size initial command.1.val command.2)

/-- Exact getD semantics for the actual in-place additive scatter fold. -/
theorem endpointArrayScatter_getD {n : ℕ} (commands : List (Fin n × ℚ)) (initial : Array ℚ)
    (hsize : initial.size = n) (query : ℕ) :
    (endpointArrayScatter commands initial).getD query 0 = initial.getD query 0 +
      (commands.map (fun command => if command.1.val = query then command.2 else 0)).sum := by
  induction commands generalizing initial with
  | nil => simp only [endpointArrayScatter, List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons command rest ih =>
    change (endpointArrayScatter rest (endpointArrayBump initial command.1.val command.2)).getD query 0 = _
    rw [ih _ (by rw [endpointArrayBump_size, hsize])]
    have hi : command.1.val < initial.size := by rw [hsize]; exact command.1.isLt
    rw [endpointArrayBump_getD initial command.1.val query command.2 hi]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The original state/letter loop labels with their original rational mass. -/
def endpointWalkCommands (P : Parameters) (level : ℕ) (truth : Bool) (previous : Array ℚ) :
    List (WalkCell level × ℚ) :=
  (List.finRange (2 * level + 1)).flatMap (fun state =>
    (List.finRange 2).map (fun letter =>
      (walkMove level state letter, previous.getD state.val 0 * P.experiment.channel truth letter)))

theorem endpointWalkCommands_length (P : Parameters) (level : ℕ) (truth : Bool) (previous : Array ℚ) :
    (endpointWalkCommands P level truth previous).length = 2 * (2 * level + 1) := by
  simp [endpointWalkCommands, List.length_flatMap, Nat.mul_comm]

/-- This is an identity for the frozen walkUpdate code, not a replacement DP. -/
theorem walkUpdate_eq_endpointScatter (P : Parameters) (level : ℕ) (truth : Bool) (previous : Array ℚ) :
    P.walkUpdate level truth previous =
      endpointArrayScatter (endpointWalkCommands P level truth previous) (Array.replicate (2 * level + 1) 0) := by
  unfold PaperProofs.Paid.Parameters.walkUpdate endpointArrayScatter endpointWalkCommands endpointArrayBump
  simp only [List.foldl_flatMap, List.foldl_map]

@[simp] theorem endpointWalkUpdate_size (P : Parameters) (level : ℕ) (truth : Bool) (previous : Array ℚ) :
    (P.walkUpdate level truth previous).size = 2 * level + 1 := by
  simp only [walkUpdate_eq_endpointScatter, endpointArrayScatter_size, Array.size_replicate]

@[simp] theorem endpointWalkRow_size (P : Parameters) (level : ℕ) (truth : Bool) (steps : ℕ) :
    (P.walkRow level truth steps).size = 2 * level + 1 := by
  cases steps with
  | zero => simp only [PaperProofs.Paid.Parameters.walkRow, Array.size_ofFn]
  | succ steps => exact endpointWalkUpdate_size P level truth (P.walkRow level truth steps)

/-- Actual array getD equals the complete incoming command mass. Both
outgoing letters of an absorbed boundary state are counted separately. -/
theorem endpointWalkUpdate_getD_commands (P : Parameters) (level : ℕ) (truth : Bool) (previous : Array ℚ)
    (target : WalkCell level) :
    (P.walkUpdate level truth previous).getD target.val 0 =
      ((endpointWalkCommands P level truth previous).map
        (fun command => if command.1.val = target.val then command.2 else 0)).sum := by
  rw [walkUpdate_eq_endpointScatter, endpointArrayScatter_getD _ _ (by simp) target.val]
  have hz : (Array.replicate (2 * level + 1) (0 : ℚ)).getD target.val 0 = 0 := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, target.isLt, ite_true, Option.getD_some]
  rw [hz, zero_add]

theorem endpoint_sum_map_flatMap {α β : Type*} (xs : List α) (f : α → List β) (g : β → ℚ) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  rfl

theorem endpoint_sum_finRange (n : ℕ) (f : Fin n → ℚ) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  rw [← List.sum_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

/-- The original row starts at the centre, for either truth and every level. -/
theorem endpointWalkDistribution_zero (P : Parameters) (level : ℕ) (truth : Bool) (state : WalkCell level) :
    P.walkDistribution level truth 0 state = if state.val = level then 1 else 0 := by
  simp only [PaperProofs.Paid.Parameters.walkDistribution, PaperProofs.Paid.Parameters.walkRow,
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, state.isLt, ↓reduceDIte, Option.getD_some]

/-- Exact incoming transition recurrence of the frozen independent rational
array DP, for both truths. No stochastic or capped-test law is assumed. -/
theorem endpointWalkDistribution_succ (P : Parameters) (level : ℕ) (truth : Bool) (steps : ℕ)
    (target : WalkCell level) :
    P.walkDistribution level truth (steps + 1) target =
      ∑ state : WalkCell level, ∑ letter : Fin 2,
        if walkMove level state letter = target then
          P.walkDistribution level truth steps state * P.experiment.channel truth letter else 0 := by
  let previous := P.walkRow level truth steps
  let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
  change (P.walkUpdate level truth previous).getD target.val 0 =
    ∑ state : WalkCell level, ∑ letter : Fin 2,
      if walkMove level state letter = target then previous.getD state.val 0 * channel letter else 0
  rw [endpointWalkUpdate_getD_commands]
  change (List.map
    (fun command : WalkCell level × ℚ => if command.1.val = target.val then command.2 else 0)
    (List.flatMap (fun state : WalkCell level =>
      List.map (fun letter : Fin 2 =>
        (walkMove level state letter, previous.getD state.val 0 * channel letter))
        (List.finRange 2)) (List.finRange (2 * level + 1)))).sum = _
  rw [endpoint_sum_map_flatMap, endpoint_sum_finRange]
  apply Finset.sum_congr rfl
  intro state _hs
  rw [List.map_map, endpoint_sum_finRange]
  apply Finset.sum_congr rfl
  intro letter _hl
  change (if (walkMove level state letter).val = target.val then previous.getD state.val 0 * channel letter else 0) =
    (if walkMove level state letter = target then previous.getD state.val 0 * channel letter else 0)
  simp only [Fin.ext_iff]

end PDROC
