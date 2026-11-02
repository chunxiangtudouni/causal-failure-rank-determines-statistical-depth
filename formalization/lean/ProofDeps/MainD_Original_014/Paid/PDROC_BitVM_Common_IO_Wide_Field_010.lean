module

public import Paid.PDROC_BitVM_Common_IO_Wide_Counter_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

def peekStore (saved : Store) (bit : Bool) : Store :=
  { saved with marked := bit, next := if bit then 1 else 2 }

def unaryStore (saved : Store) (bit : Bool) : Store :=
  { saved with bit := bit, marked := bit, next := if bit then 1 else 2 }

/-- The unary branch observes the genuine next raw bit, retaining the
cursor location. This is two real moves and one actual finite load. -/
theorem prepare_unary (saved : Store) (bit : Bool) (left suffix : List Bool) :
    TM1.step program (state 2 saved left (true :: bit :: suffix)) =
      some (state 9 (peekStore saved bit) left (true :: bit :: suffix)) := by
  simp [TM1.step, TM1.stepAux, program, PDROC.BitVM.Common.IO.Bootstrap.program,
    state, peekStore, Tape.mk₂]

theorem unary_emit_path (saved : Store) (bit : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 2 saved (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix))
      (state (if bit then 2 else 5) (unaryStore saved bit)
        (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, bit)])) (true :: suffix)),
      path.posts.length ≤ 2 * gap + 2 * rows.length + 8 := by
  obtain ⟨⟨posts, chain, last⟩, bound⟩ := program_emit_one_bit (peekStore saved bit) bit gap rows suffix
  have lengthBound : posts.length ≤ 2 * gap + 2 * rows.length + 7 := bound
  let later : ActualPath (TM1.step program)
      (state 9 (peekStore saved bit) (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix))
      (state (if bit then 2 else 5) (unaryStore saved bit)
        (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, bit)])) (true :: suffix)) :=
    ⟨posts,
      by simpa [state] using chain,
      by cases bit <;> simpa [state, peekStore, unaryStore, PDROC.BitVM.Common.IO.Bootstrap.dispatch] using last⟩
  have edge := prepare_unary saved bit (List.replicate gap false ++ true :: leftRows 29 rows) suffix
  refine ⟨(ActualPath.single edge).trans later, ?_⟩
  simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
  omega

/-- A mathematical bound on a proved path, not a program argument. -/
def unaryCost (count gap rows : Nat) : Nat := (count + 1) * (2 * gap + 2 * rows + 2 * count + 8)

theorem unaryCost_step (count gap rows : Nat) :
    unaryCost (count + 1) gap rows = 2 * gap + 2 * rows + 8 + unaryCost count (gap + 1) (rows + 1) := by
  unfold unaryCost
  ring

/-- The unbounded unary header is processed by a real finite loop.
Its TRUE cells are appended as actual col3 marks; its delimiter is emitted
unmarked. No width is placed in the finite Store. -/
theorem unary_header_path (saved : Store) (count gap : Nat) (rows : List (Bool × Bool))
    (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 2 saved (List.replicate gap false ++ true :: leftRows 29 rows)
        (true :: (List.replicate count true ++ false :: suffix)))
      (state 5 (unaryStore saved false)
        (List.replicate (gap + count + 1) false ++
          true :: leftRows 29 (rows ++ List.replicate count (true, true) ++ [(false, false)]))
        (true :: suffix)),
      path.posts.length ≤ unaryCost count gap rows.length := by
  induction count generalizing saved gap rows with
  | zero =>
    simp only [List.replicate_zero]
    rw [List.append_nil]
    simp only [unaryCost, Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.one_mul]
    exact unary_emit_path saved false gap rows suffix
  | succ count ih =>
    obtain ⟨first, firstBound⟩ := unary_emit_path saved true gap rows
      (List.replicate count true ++ false :: suffix)
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (unaryStore saved true) (gap + 1) (rows ++ [(true, true)])
    have lengthBound : posts.length ≤ unaryCost count (gap + 1) (rows.length + 1) := by
      simpa only [List.length_append, List.length_cons, List.length_nil] using bound
    let later : ActualPath (TM1.step program)
        (state 2 (unaryStore saved true)
          (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(true, true)]))
          (true :: (List.replicate count true ++ false :: suffix)))
        (state 5 (unaryStore saved false)
          (List.replicate (gap + (count + 1) + 1) false ++
            true :: leftRows 29 (rows ++ List.replicate (count + 1) (true, true) ++ [(false, false)]))
          (true :: suffix)) :=
      ⟨posts, chain, by
        cases saved
        simpa [unaryStore, List.replicate_succ, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last⟩
    let joined := first.trans later
    refine ⟨⟨joined.posts, ?_, joined.last⟩, ?_⟩
    · simpa only [List.replicate_succ, List.cons_append] using joined.chain
    · have length : joined.posts.length = first.posts.length + posts.length := by
        exact ActualPath.trans_length first later
      rw [length, unaryCost_step]
      exact Nat.add_le_add firstBound lengthBound

def unmarkedRows (word : List Bool) : List (Bool × Bool) := word.map (fun bit => (bit, false))

theorem clearFirstMark_unmarked (word : List Bool) : clearFirstMark (unmarkedRows word) = none := by
  induction word with
  | nil => rfl
  | cons bit word ih => simpa [unmarkedRows, clearFirstMark] using ih

theorem clearFirstMark_prefix (word : List Bool) (rows : List (Bool × Bool)) :
    clearFirstMark (unmarkedRows word ++ rows) =
      (clearFirstMark rows).map (fun changed => unmarkedRows word ++ changed) := by
  induction word with
  | nil => simp [unmarkedRows]
  | cons bit word ih =>
    simp only [unmarkedRows, List.map_cons, List.cons_append, clearFirstMark] at ih ⊢
    rw [ih]
    cases clearFirstMark rows <;> rfl

theorem counterResult_unmarked (word : List Bool) :
    counterResultRows (unmarkedRows word) = unmarkedRows word ∧
      counterResultNext (unmarkedRows word) = 4 := by
  simp [counterResultRows, counterResultNext, clearFirstMark_unmarked]

theorem counterResult_marked (before after : List Bool) (count : Nat) :
    counterResultRows (unmarkedRows before ++ List.replicate (count + 1) (true, true) ++ unmarkedRows after) =
        unmarkedRows (before ++ [true]) ++ List.replicate count (true, true) ++ unmarkedRows after ∧
      counterResultNext (unmarkedRows before ++ List.replicate (count + 1) (true, true) ++ unmarkedRows after) = 3 := by
  have found : clearFirstMark
        (unmarkedRows before ++ List.replicate (count + 1) (true, true) ++ unmarkedRows after) =
      some (unmarkedRows (before ++ [true]) ++ List.replicate count (true, true) ++ unmarkedRows after) := by
    rw [List.append_assoc, clearFirstMark_prefix]
    simp [List.replicate_succ, clearFirstMark, unmarkedRows, List.map_append, List.append_assoc]
  simp only [counterResultRows, counterResultNext, found, Option.getD_some, Option.isSome_some, ite_true]
  constructor <;> trivial

def payloadStore (saved : Store) (bit : Bool) : Store :=
  { saved with bit := bit, marked := false, next := 2 }

theorem prepare_payload (saved : Store) (left right : List Bool) :
    TM1.step program (state 3 saved left right) =
      some (state 9 { saved with marked := false, next := 2 } left right) := by
  rfl

theorem payload_emit_path (saved : Store) (bit : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 3 saved (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix))
      (state 5 (payloadStore saved bit)
        (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, false)])) (true :: suffix)),
      path.posts.length ≤ 2 * gap + 2 * rows.length + 8 := by
  obtain ⟨⟨posts, chain, last⟩, bound⟩ :=
    program_emit_one_bit { saved with marked := false, next := 2 } bit gap rows suffix
  have lengthBound : posts.length ≤ 2 * gap + 2 * rows.length + 7 := bound
  let later : ActualPath (TM1.step program)
      (state 9 { saved with marked := false, next := 2 }
        (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix))
      (state 5 (payloadStore saved bit)
        (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, false)])) (true :: suffix)) :=
    ⟨posts, by simpa [state] using chain,
      by simpa [state, payloadStore, PDROC.BitVM.Common.IO.Bootstrap.dispatch] using last⟩
  have edge := prepare_payload saved (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix)
  refine ⟨(ActualPath.single edge).trans later, ?_⟩
  simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
  omega

def payloadCost (count gap rows : Nat) : Nat :=
  count * (4 * gap + 4 * rows + 4 * count + 14) + 2 * gap + 2 * rows + 6

theorem payloadCost_step (count gap rows : Nat) :
    payloadCost (count + 1) gap rows =
      4 * gap + 4 * rows + 14 + payloadCost count (gap + 1) (rows + 1) := by
  unfold payloadCost
  ring

end PDROC.BitVM.Common.IO.Wide
