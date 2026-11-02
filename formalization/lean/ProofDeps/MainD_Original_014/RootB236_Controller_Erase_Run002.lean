module

public import RootB236_Controller_Erase_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.Erase

open Turing
variable {C : Type*}

def restoreTrace (background : Stack → List Bool) (context : C) :
    Bool → Bool → List Bool → List Bool → List Bool → List (State C)
  | present, saved, [], mask, count =>
      [state background (some 1) (context,present,saved) mask count [],
       state background none (context,false,false) mask count []]
  | present, saved, bit::parked, mask, count =>
      state background (some 1) (context,present,saved) mask count (bit::parked) ::
        restoreTrace background context true bit parked (bit::mask) (true::count)

theorem restore_head (background : Stack → List Bool) (context : C) (present saved : Bool)
    (parked mask count : List Bool) :
    (restoreTrace background context present saved parked mask count).head? =
      some (state background (some 1) (context,present,saved) mask count parked) := by
  cases parked <;> rfl

theorem restore_nonempty (background : Stack → List Bool) (context : C) (present saved : Bool)
    (parked mask count : List Bool) : restoreTrace background context present saved parked mask count ≠ [] := by
  intro empty
  have head := restore_head background context present saved parked mask count
  rw [empty] at head
  cases head

theorem restore_chain (background : Stack → List Bool) (context : C) (present saved : Bool)
    (parked mask count : List Bool) :
    (restoreTrace background context present saved parked mask count).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction parked generalizing present saved mask count with
  | nil => exact List.isChain_cons_cons.mpr ⟨step_halt background context present saved mask count, by simp⟩
  | cons bit later ih =>
      apply List.isChain_cons.mpr
      refine ⟨?_, ih _ _ _ _⟩
      intro next first
      rw [restore_head] at first
      have same := (Option.mem_some_iff.mp first).symm
      subst next
      exact step_restore background context present saved bit mask count later

theorem restore_last (background : Stack → List Bool) (context : C) (present saved : Bool)
    (parked mask count : List Bool) :
    (restoreTrace background context present saved parked mask count).getLast? =
      some (state background none (context,false,false) (parked.reverse++mask)
        (List.replicate parked.length true++count) []) := by
  induction parked generalizing present saved mask count with
  | nil => rfl
  | cons bit later ih =>
      rw [restoreTrace, List.getLast?_cons_of_ne_nil (restore_nonempty _ _ _ _ _ _ _), ih]
      simp only [List.reverse_cons, List.length_cons, List.append_assoc,
        List.nil_append, List.replicate_succ', List.cons_append]

theorem restore_length (background : Stack → List Bool) (context : C) (present saved : Bool)
    (parked mask count : List Bool) :
    (restoreTrace background context present saved parked mask count).length = parked.length + 2 := by
  induction parked generalizing present saved mask count with
  | nil => rfl
  | cons bit later ih => simp only [restoreTrace, List.length_cons, ih]

def actualTrace (background : Stack → List Bool) (context : C) :
    Bool → Bool → List Bool → Bool → List Bool → List Bool → List (State C)
  | present, saved, [], head, suffix, parked =>
      state background (some 0) (context,present,saved) (head::suffix) [] parked ::
        restoreTrace background context false head parked (false::suffix) []
  | present, saved, bit::skipped, head, suffix, parked =>
      state background (some 0) (context,present,saved) (bit::skipped++head::suffix)
        (List.replicate (skipped.length+1) true) parked ::
        actualTrace background context true bit skipped head suffix (bit::parked)

theorem actual_head (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix parked : List Bool) :
    (actualTrace background context present saved skipped head suffix parked).head? =
      some (state background (some 0) (context,present,saved) (skipped++head::suffix)
        (List.replicate skipped.length true) parked) := by
  cases skipped <;> rfl

theorem actual_nonempty (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix parked : List Bool) :
    actualTrace background context present saved skipped head suffix parked ≠ [] := by
  intro empty
  have first := actual_head background context present saved skipped head suffix parked
  rw [empty] at first
  cases first

theorem actual_chain (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix parked : List Bool) :
    (actualTrace background context present saved skipped head suffix parked).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction skipped generalizing present saved parked with
  | nil =>
      apply List.isChain_cons.mpr
      refine ⟨?_, restore_chain _ _ _ _ _ _ _⟩
      intro next first
      rw [restore_head] at first
      have same := (Option.mem_some_iff.mp first).symm
      subst next
      exact step_erase background context present saved head suffix parked
  | cons bit later ih =>
      apply List.isChain_cons.mpr
      refine ⟨?_, ih _ _ _⟩
      intro next first
      rw [actual_head] at first
      have same := (Option.mem_some_iff.mp first).symm
      subst next
      simpa only [List.replicate_succ, List.cons_append] using
        step_walk background context present saved bit (later++head::suffix)
          (List.replicate later.length true) parked

theorem actual_last (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix parked : List Bool) :
    (actualTrace background context present saved skipped head suffix parked).getLast? =
      some (state background none (context,false,false) (parked.reverse++skipped++false::suffix)
        (List.replicate (skipped.length+parked.length) true) []) := by
  induction skipped generalizing present saved parked with
  | nil =>
      rw [actualTrace, List.getLast?_cons_of_ne_nil (restore_nonempty _ _ _ _ _ _ _), restore_last]
      simp
  | cons bit later ih =>
      rw [actualTrace, List.getLast?_cons_of_ne_nil (actual_nonempty _ _ _ _ _ _ _ _), ih]
      have countEq : later.length+(bit::parked).length = (bit::later).length+parked.length := by
        simp only [List.length_cons]
        omega
      rw [countEq]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem actual_length (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix parked : List Bool) :
    (actualTrace background context present saved skipped head suffix parked).length =
      2*skipped.length+parked.length+3 := by
  induction skipped generalizing present saved parked with
  | nil => simp only [actualTrace, List.length_cons, restore_length, List.length_nil]; omega
  | cons bit later ih => simp only [actualTrace, List.length_cons, ih]; omega

theorem actual (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix : List Bool) :
    ∃ (run : List (State C)) (final : State C),
      run.head? = some (state background (some 0) (context,present,saved)
        (skipped++head::suffix) (List.replicate skipped.length true) []) ∧
      run.IsChain (fun before after => TM2.step program before=some after) ∧
      run.getLast? = some final ∧
      final = state background none (context,false,false)
        (skipped++false::suffix) (List.replicate skipped.length true) [] ∧
      run.length = 2*skipped.length+3 ∧ final.l=none ∧ TM2.step program final=none := by
  refine ⟨actualTrace background context present saved skipped head suffix [],
    state background none (context,false,false) (skipped++false::suffix)
      (List.replicate skipped.length true) [], actual_head _ _ _ _ _ _ _ _,
    actual_chain _ _ _ _ _ _ _ _, ?_, rfl, ?_, rfl, rfl⟩
  · simpa only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] using
      actual_last background context present saved skipped head suffix []
  · simpa only [List.length_nil, Nat.add_zero] using
      actual_length background context present saved skipped head suffix []

end RootB236.Controller.Erase
