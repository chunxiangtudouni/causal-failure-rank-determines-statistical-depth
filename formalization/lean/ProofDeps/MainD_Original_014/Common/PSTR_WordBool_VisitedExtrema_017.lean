module

public import Common.PSTR_WordBool_BoolStackEndpoints_016

/-! Exact extrema of the ORIGINAL visited-space scan. No bound in elapsed
trace length is substituted for the actual range. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.VisitedExtrema

open Turing
open PaperProofs.Common.Native.RationalControllerComputation (displacement visitedSpace)

theorem seed_le_fold_max (values : List Int) (seed : Int) : seed ≤ values.foldl max seed := by
  induction values generalizing seed with
  | nil => exact le_rfl
  | cons head tail ih => exact (le_max_left seed head).trans (ih (max seed head))

theorem fold_min_le_seed (values : List Int) (seed : Int) : values.foldl min seed ≤ seed := by
  induction values generalizing seed with
  | nil => exact le_rfl
  | cons head tail ih => exact (ih (min seed head)).trans (min_le_left seed head)

theorem member_le_fold_max (values : List Int) (seed value : Int) (present : value ∈ values) :
    value ≤ values.foldl max seed := by
  induction values generalizing seed with
  | nil => simp at present
  | cons head tail ih =>
    rcases List.mem_cons.mp present with same | later
    · subst value
      exact (le_max_right seed head).trans (seed_le_fold_max tail (max seed head))
    · exact ih (max seed head) later

theorem fold_min_le_member (values : List Int) (seed value : Int) (present : value ∈ values) :
    values.foldl min seed ≤ value := by
  induction values generalizing seed with
  | nil => simp at present
  | cons head tail ih =>
    rcases List.mem_cons.mp present with same | later
    · subst value
      exact (fold_min_le_seed tail (min seed head)).trans (min_le_right seed head)
    · exact ih (min seed head) later

variable {states : Nat}

def positions (machine : TM0.Machine Bool (Fin (states + 1)))
    (trace : List (TM0.Cfg Bool (Fin (states + 1)))) : List Int :=
  (trace.map (displacement machine)).scanl (· + ·) 0

def high (machine : TM0.Machine Bool (Fin (states + 1))) (inputLength : Nat)
    (trace : List (TM0.Cfg Bool (Fin (states + 1)))) : Int :=
  (positions machine trace).foldl max (inputLength : Int)

def low (machine : TM0.Machine Bool (Fin (states + 1)))
    (trace : List (TM0.Cfg Bool (Fin (states + 1)))) : Int :=
  (positions machine trace).foldl min 0

theorem position_bounds (machine : TM0.Machine Bool (Fin (states + 1))) (inputLength : Nat)
    (trace : List (TM0.Cfg Bool (Fin (states + 1)))) (position : Int)
    (present : position ∈ positions machine trace) :
    low machine trace ≤ position ∧ position ≤ high machine inputLength trace :=
  ⟨fold_min_le_member _ _ _ present, member_le_fold_max _ _ _ present⟩

theorem seed_bounds (machine : TM0.Machine Bool (Fin (states + 1))) (inputLength : Nat)
    (trace : List (TM0.Cfg Bool (Fin (states + 1)))) :
    low machine trace ≤ 0 ∧ (inputLength : Int) ≤ high machine inputLength trace :=
  ⟨fold_min_le_seed _ _, seed_le_fold_max _ _⟩

theorem range_nonnegative (machine : TM0.Machine Bool (Fin (states + 1))) (inputLength : Nat)
    (trace : List (TM0.Cfg Bool (Fin (states + 1)))) :
    0 ≤ high machine inputLength trace - low machine trace := by
  have bounds := seed_bounds machine inputLength trace
  omega

theorem original_space (machine : TM0.Machine Bool (Fin (states + 1))) (inputLength : Nat)
    (trace : List (TM0.Cfg Bool (Fin (states + 1)))) :
    visitedSpace machine inputLength trace =
      (high machine inputLength trace - low machine trace).toNat + 1 := rfl

end PaperProofs.Common.Native.PSTRWordBool.VisitedExtrema
