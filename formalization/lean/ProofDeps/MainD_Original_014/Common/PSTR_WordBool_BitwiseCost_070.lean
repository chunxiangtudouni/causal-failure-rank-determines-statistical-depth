module

public import Common.PSTR_WordBool_BitwiseRun_069
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Current-data workspace on the SAME concrete AND/OR run. The source
clock is exactly3w+3 transitions; work-stack mass never exceeds3w. Every
other stack is physically framed. Internal snapshots use the actual fixed
syntax push bound2, not elapsed computation time. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.Bitwise

open Turing PSTRWordVM
open scoped BigOperators

def WorkBound (background : Stack → List Bool) (bound : Nat) (current : State) : Prop :=
  ∃ (point : Label) (memory : Store) (left right reversed room used : List Bool),
    current = state background point memory left right reversed room used ∧
      left.length + right.length + reversed.length + room.length + used.length ≤ bound

theorem work_mono {background : Stack → List Bool} {small large : Nat} {current : State}
    (within : WorkBound background small current) (larger : small ≤ large) : WorkBound background large current := by
  obtain ⟨point, memory, left, right, reversed, room, used, same, bound⟩ := within
  exact ⟨point, memory, left, right, reversed, room, used, same, bound.trans larger⟩

theorem forward_bound (isOr : Bool) (background : Stack → List Bool) (memory : Store)
    (pairs : List (Bool × Bool)) (reversed : List Bool) (used : Nat) :
    ∀ current ∈ forwardTrace isOr background memory pairs reversed used,
      WorkBound background (3 * pairs.length + reversed.length + used) current := by
  induction pairs generalizing memory reversed used with
  | nil =>
    intro current present
    simp [forwardTrace] at present
    rcases present with same | same
    · subst current
      exact ⟨0, memory, [], [], reversed, [], List.replicate used true, rfl, by simp⟩
    · subst current
      exact ⟨1, (false, false), [], [], reversed, [], List.replicate used true, rfl, by simp⟩
  | cons pair later ih =>
    intro current present
    rw [forwardTrace] at present
    rcases List.mem_cons.mp present with same | rest
    · subst current
      refine ⟨0, memory, (pair :: later).map Prod.fst, (pair :: later).map Prod.snd,
        reversed, List.replicate (later.length + 1) true, List.replicate used true, rfl, ?_⟩
      simp only [List.length_map, List.length_cons, List.length_replicate]
      omega
    · have bound := ih pair (combine isOr pair.1 pair.2 :: reversed) (used + 1) current rest
      apply work_mono bound
      simp only [List.length_cons]
      omega

theorem reverse_bound (background : Stack → List Bool) (memory : Store)
    (reversed result : List Bool) (used : Nat) :
    ∀ current ∈ reverseTrace background memory reversed result used,
      WorkBound background (reversed.length + result.length + used) current := by
  induction reversed generalizing memory result with
  | nil =>
    intro current present
    simp [reverseTrace] at present
    rcases present with same | same
    · subst current
      exact ⟨1, memory, result, [], [], [], List.replicate used true, rfl, by simp⟩
    · subst current
      exact ⟨2, (false, false), result, [], [], [], List.replicate used true, rfl, by simp⟩
  | cons bit later ih =>
    intro current present
    rw [reverseTrace] at present
    rcases List.mem_cons.mp present with same | rest
    · subst current
      refine ⟨1, memory, result, [], bit :: later, [], List.replicate used true, rfl, ?_⟩
      simp only [List.length_cons, List.length_nil, List.length_replicate]
      omega
    · have bound := ih (true, bit) (bit :: result) current rest
      apply work_mono bound
      simp only [List.length_cons]
      omega

theorem restore_bound (background : Stack → List Bool) (memory : Store)
    (result : List Bool) (room used : Nat) :
    ∀ current ∈ restoreTrace background memory result room used,
      WorkBound background (result.length + room + used) current := by
  induction used generalizing memory room with
  | zero =>
    intro current present
    simp [restoreTrace] at present
    rcases present with same | same
    · subst current
      exact ⟨2, memory, result, [], [], List.replicate room true, [], rfl, by simp⟩
    · subst current
      exact ⟨3, (false, false), result, [], [], List.replicate room true, [], rfl, by simp⟩
  | succ used ih =>
    intro current present
    rw [restoreTrace] at present
    rcases List.mem_cons.mp present with same | rest
    · subst current
      exact ⟨2, memory, result, [], [], List.replicate room true, List.replicate (used + 1) true, rfl, by simp⟩
    · have bound := ih (true, true) (room + 1) current rest
      apply work_mono bound
      omega

theorem actual_bound (isOr : Bool) (background : Stack → List Bool) (memory : Store)
    (pairs : List (Bool × Bool)) :
    ∀ current ∈ actualTrace isOr background memory pairs, WorkBound background (3 * pairs.length) current := by
  intro current present
  rw [actualTrace] at present
  rcases List.mem_append.mp present with early | last
  · rcases List.mem_append.mp early with first | second
    · simpa only [List.length_nil, Nat.add_zero] using forward_bound isOr background memory pairs [] 0 current first
    · have bound := reverse_bound background (false, false) (outputs isOr pairs).reverse [] pairs.length
        current (List.mem_of_mem_tail second)
      apply work_mono bound
      simp only [List.length_reverse, outputs, List.length_map, List.length_nil]
      omega
  · have bound := restore_bound background (false, false) (outputs isOr pairs) 0 pairs.length
      current (List.mem_of_mem_tail last)
    apply work_mono bound
    simp only [outputs, List.length_map]
    omega

theorem work_stack_bound (background : Stack → List Bool) (bound : Nat) (current : State)
    (within : WorkBound background bound current) (point : Stack) :
    (current.stk point).length ≤ (background point).length + bound := by
  obtain ⟨label, memory, left, right, reversed, room, used, same, mass⟩ := within
  subst current
  by_cases atLeft : point = 3
  · subst point
    change left.length ≤ _
    omega
  by_cases atRight : point = 4
  · subst point
    change right.length ≤ _
    omega
  by_cases atReverse : point = 7
  · subst point
    change reversed.length ≤ _
    omega
  by_cases atRoom : point = 11
  · subst point
    change room.length ≤ _
    omega
  by_cases atUsed : point = 12
  · subst point
    change used.length ≤ _
    omega
  change (cells background left right reversed room used point).length ≤ _
  rw [cells_frame background left right reversed room used point atLeft atRight atReverse atRoom atUsed]
  omega

def backgroundMass (background : Stack → List Bool) : Nat := ∑ point : Stack, (background point).length

theorem background_point_le (background : Stack → List Bool) (point : Stack) :
    (background point).length ≤ backgroundMass background := by
  change (background point).length ≤ ∑ other : Stack, (background other).length
  exact Finset.single_le_sum (f := fun other : Stack => (background other).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ point)

theorem actual_frame (isOr : Bool) (background : Stack → List Bool) (memory : Store)
    (pairs : List (Bool × Bool)) (current : State) (present : current ∈ actualTrace isOr background memory pairs)
    (point : Stack) (notLeft : point ≠ 3) (notRight : point ≠ 4) (notReverse : point ≠ 7)
    (notRoom : point ≠ 11) (notUsed : point ≠ 12) : current.stk point = background point := by
  obtain ⟨label, flags, left, right, reversed, room, used, same, _bound⟩ := actual_bound isOr background memory pairs current present
  subst current
  exact cells_frame background left right reversed room used point notLeft notRight notReverse notRoom notUsed

theorem actual_inner_bound (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (pairs : List (Bool × Bool)) (current : State)
    (present : current ∈ actualTrace isOr background memory pairs)
    (label : Label) (proper : label ≠ 3)
    (snapshot : AuxWorkspace.Snapshot (Γ := Alphabet) (σ := Store))
    (node : snapshot ∈ AuxWorkspace.nodes (program isOr caller label) current.var current.stk) (point : Stack) :
    (snapshot.2 point).length ≤ backgroundMass background + 3 * pairs.length + 2 := by
  have boundedStacks : ∀ point, (current.stk point).length ≤ backgroundMass background + 3 * pairs.length := by
    intro point
    exact (work_stack_bound background _ current (actual_bound isOr background memory pairs current present) point).trans
      (Nat.add_le_add_right (background_point_le background point) _)
  have bounded := AuxWorkspace.node_bound (program isOr caller label) current.var current.stk
    (backgroundMass background + 3 * pairs.length) boundedStacks snapshot node point
  exact bounded.trans (Nat.add_le_add_left (program_pushes isOr caller label proper) _)

theorem actual_word_call {width : Nat} (isOr : Bool) (caller : Statement)
    (background : Stack → List Bool) (memory : Store) (left right : BitVec width) :
    ∃ trace : List State,
      trace.head? = some (state background 0 memory (WordBank.bits left) (WordBank.bits right) []
        (List.replicate width true) []) ∧
      trace.IsChain (fun before after => TM2.step (program isOr caller) before = some after) ∧
      trace.getLast? = some (state background 3 (false, false) (WordBank.bits (wordResult isOr left right)) [] []
        (List.replicate width true) []) ∧
      trace.length = 3 * width + 4 ∧
      (∀ current ∈ trace, ∀ point, (current.stk point).length ≤ (background point).length + 3 * width) ∧
      (∀ current ∈ trace, ∀ point, point ≠ 3 → point ≠ 4 → point ≠ 7 → point ≠ 11 → point ≠ 12 →
        current.stk point = background point) := by
  let pairs := pairBits left right
  have length : pairs.length = width := List.length_ofFn
  have run := actual_run isOr caller background memory pairs
  have leftBits : pairs.map Prod.fst = WordBank.bits left := pairBits_left left right
  have rightBits : pairs.map Prod.snd = WordBank.bits right := pairBits_right left right
  have resultBits : outputs isOr pairs = WordBank.bits (wordResult isOr left right) := outputs_pairBits isOr left right
  rw [leftBits, rightBits, resultBits, length] at run
  refine ⟨actualTrace isOr background memory pairs, run.1, run.2.1, run.2.2.1, run.2.2.2, ?_, ?_⟩
  · intro current present point
    simpa only [length] using work_stack_bound background _ current (actual_bound isOr background memory pairs current present) point
  · intro current present point a b c d e
    exact actual_frame isOr background memory pairs current present point a b c d e

end PaperProofs.Common.Native.PSTRWordBool.Bitwise
