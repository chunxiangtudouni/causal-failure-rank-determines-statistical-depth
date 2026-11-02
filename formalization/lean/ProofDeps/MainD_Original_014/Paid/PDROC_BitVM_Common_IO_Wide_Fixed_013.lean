module

public import Paid.PDROC_BitVM_Common_IO_Wide_NatField_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

def fixedStore (saved : Store) : Store :=
  { saved with remaining := PDROC.BitVM.Common.IO.Bootstrap.decrement saved.remaining, marked := false, next := 0 }

def fixedReadStore (saved : Store) (bit : Bool) : Store := { fixedStore saved with bit := bit }

theorem fixed_positive (saved : Store) (positive : 0 < saved.remaining.val) (left right : List Bool) :
    TM1.step program (state 1 saved left right) = some (state 9 (fixedStore saved) left right) := by
  have nonzero : saved.remaining ≠ 0 := by
    intro zero
    have zeroValue : saved.remaining.val = 0 := congrArg Fin.val zero
    omega
  simp [TM1.step, TM1.stepAux, program, PDROC.BitVM.Common.IO.Bootstrap.program,
    state, fixedStore, nonzero]

theorem fixed_zero (saved : Store) (zero : saved.remaining = 0) (left right : List Bool) :
    TM1.step program (state 1 saved left right) = some (state 2 saved left right) := by
  simp [TM1.step, TM1.stepAux, program, PDROC.BitVM.Common.IO.Bootstrap.program, state, zero]

theorem fixed_emit_path (saved : Store) (positive : 0 < saved.remaining.val) (bit : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 1 saved (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix))
      (state 1 (fixedReadStore saved bit)
        (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, false)])) (true :: suffix)),
      path.posts.length ≤ 2 * gap + 2 * rows.length + 8 := by
  obtain ⟨⟨posts, chain, last⟩, bound⟩ := program_emit_one_bit (fixedStore saved) bit gap rows suffix
  have lengthBound : posts.length ≤ 2 * gap + 2 * rows.length + 7 := bound
  let later : ActualPath (TM1.step program)
      (state 9 (fixedStore saved) (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix))
      (state 1 (fixedReadStore saved bit)
        (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, false)])) (true :: suffix)) :=
    ⟨posts, by simpa [state] using chain,
      by simpa [state, fixedReadStore, fixedStore, PDROC.BitVM.Common.IO.Bootstrap.dispatch] using last⟩
  have edge := fixed_positive saved positive (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix)
  refine ⟨(ActualPath.single edge).trans later, ?_⟩
  simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
  omega

def fixedCost (count gap rows : Nat) : Nat := count * (2 * gap + 2 * rows + 2 * count + 6) + 1

theorem fixedCost_step (count gap rows : Nat) :
    fixedCost (count + 1) gap rows = 2 * gap + 2 * rows + 8 + fixedCost count (gap + 1) (rows + 1) := by
  unfold fixedCost
  ring

/-- Only fixed header/tag/sign counts enter this Fin9 controller.
The raw numeric widths are handled separately by physical col3 marks. -/
theorem fixed_word_path (saved : Store) (gap : Nat) (before word suffix : List Bool)
    (wordLength : saved.remaining.val = word.length) :
    ∃ final : Store, ∃ path : ActualPath (TM1.step program)
      (state 1 saved (List.replicate gap false ++ true :: leftRows 29 (unmarkedRows before))
        (true :: (word ++ suffix)))
      (state 2 final (List.replicate (gap + word.length) false ++ true :: leftRows 29 (unmarkedRows (before ++ word)))
        (true :: suffix)),
      final.field = saved.field ∧ final.remaining = 0 ∧
      path.posts.length ≤ fixedCost word.length gap before.length := by
  induction word generalizing saved gap before with
  | nil =>
    simp only [List.length_nil, List.nil_append, Nat.add_zero]
    rw [List.append_nil]
    have zero : saved.remaining = 0 := Fin.ext (by simpa using wordLength)
    refine ⟨saved, ActualPath.single (fixed_zero saved zero _ _), rfl, zero, ?_⟩
    simp [fixedCost, ActualPath.single]
  | cons bit word ih =>
    have positive : 0 < saved.remaining.val := by simp only [List.length_cons] at wordLength; omega
    obtain ⟨first, firstBound⟩ := fixed_emit_path saved positive bit gap (unmarkedRows before) (word ++ suffix)
    have nextLength : (fixedReadStore saved bit).remaining.val = word.length := by
      simp only [fixedReadStore, fixedStore, PDROC.BitVM.Common.IO.Bootstrap.decrement]
      simp only [List.length_cons] at wordLength
      omega
    obtain ⟨final, ⟨posts, chain, last⟩, field, remaining, bound⟩ :=
      ih (fixedReadStore saved bit) (gap + 1) (before ++ [bit]) nextLength
    have lengthBound : posts.length ≤ fixedCost word.length (gap + 1) (before.length + 1) := by
      simpa using bound
    let later : ActualPath (TM1.step program)
        (state 1 (fixedReadStore saved bit)
          (List.replicate (gap + 1) false ++ true :: leftRows 29 (unmarkedRows before ++ [(bit, false)]))
          (true :: (word ++ suffix)))
        (state 2 final (List.replicate (gap + (bit :: word).length) false ++
          true :: leftRows 29 (unmarkedRows (before ++ bit :: word))) (true :: suffix)) :=
      ⟨posts,
        by simpa [unmarkedRows, List.map_append] using chain,
        by simpa [unmarkedRows, List.map_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last⟩
    let joined := first.trans later
    refine ⟨final, ⟨joined.posts, ?_, joined.last⟩, ?_, remaining, ?_⟩
    · simpa only [List.cons_append] using joined.chain
    · simpa [fixedReadStore, fixedStore] using field
    · have count : joined.posts.length = first.posts.length + posts.length := ActualPath.trans_length first later
      rw [count]
      simp only [List.length_cons, fixedCost_step]
      have firstCount : first.posts.length ≤ 2 * gap + 2 * before.length + 8 := by simpa [unmarkedRows] using firstBound
      exact Nat.add_le_add firstCount lengthBound

def cursorState (label : Label) (saved : Store) (done rest : List Bool) : TM1.Cfg Bool Label Store :=
  state label saved (List.replicate (done.length + 1) false ++ true :: leftRows 29 (unmarkedRows done)) (true :: rest)

end PDROC.BitVM.Common.IO.Wide
