module

public import Paid.PDROC_BitVM_Common_IO_Wide_Field_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

def fieldRows (before : List Bool) (count : Nat) (after : List Bool) : List (Bool × Bool) :=
  unmarkedRows before ++ List.replicate count (true, true) ++ unmarkedRows after

theorem fieldRows_length (before after : List Bool) (count : Nat) :
    (fieldRows before count after).length = before.length + count + after.length := by
  simp [fieldRows, unmarkedRows, List.append_assoc, Nat.add_assoc]

theorem fieldRows_zero (before after : List Bool) :
    fieldRows before 0 after = unmarkedRows (before ++ after) := by
  simp [fieldRows, unmarkedRows, List.map_append]

theorem fieldRows_payload (before after : List Bool) (count : Nat) (bit : Bool) :
    fieldRows before count after ++ [(bit, false)] = fieldRows before count (after ++ [bit]) := by
  simp [fieldRows, unmarkedRows, List.map_append, List.append_assoc]

theorem counter_marked_path (saved : Store) (gap count : Nat) (before after : List Bool) (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 5 saved (List.replicate gap false ++ true :: leftRows 29 (fieldRows before (count + 1) after)) (true :: suffix))
      (state 3 { saved with next := 3 }
        (List.replicate gap false ++ true :: leftRows 29 (fieldRows (before ++ [true]) count after)) (true :: suffix)),
      path.posts.length ≤ 2 * gap + 2 * (fieldRows before (count + 1) after).length + 6 := by
  obtain ⟨⟨posts, chain, last⟩, bound⟩ := counter_full_path saved gap (fieldRows before (count + 1) after) suffix
  have rowResult := counterResult_marked before after count
  change counterResultRows (fieldRows before (count + 1) after) = fieldRows (before ++ [true]) count after ∧
    counterResultNext (fieldRows before (count + 1) after) = 3 at rowResult
  rw [rowResult.1, rowResult.2] at last
  refine ⟨⟨posts, chain, ?_⟩, bound⟩
  simpa [PDROC.BitVM.Common.IO.Bootstrap.dispatch] using last

theorem counter_unmarked_path (saved : Store) (gap : Nat) (word suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 5 saved (List.replicate gap false ++ true :: leftRows 29 (unmarkedRows word)) (true :: suffix))
      (state 4 { saved with next := 4 }
        (List.replicate gap false ++ true :: leftRows 29 (unmarkedRows word)) (true :: suffix)),
      path.posts.length ≤ 2 * gap + 2 * word.length + 6 := by
  obtain ⟨⟨posts, chain, last⟩, bound⟩ := counter_full_path saved gap (unmarkedRows word) suffix
  have rowResult := counterResult_unmarked word
  refine ⟨⟨posts, chain, ?_⟩, ?_⟩
  · simpa [state, rowResult.1, rowResult.2, PDROC.BitVM.Common.IO.Bootstrap.dispatch] using last
  · simpa [unmarkedRows] using bound

/-- Whole real payload loop. Each iteration observes/decrements a real
header mark, consumes one real source bit, and appends its actual row.
Only endpoint/store projections are existential, never supplied as an
answer, width, fuel or successful run premise to the finite machine. -/
theorem payload_loop_path (saved : Store) (markedFalse : saved.marked = false)
    (gap : Nat) (before after digits suffix : List Bool) :
    ∃ final : Store, ∃ path : ActualPath (TM1.step program)
      (state 5 saved (List.replicate gap false ++ true :: leftRows 29 (fieldRows before digits.length after))
        (true :: (digits ++ suffix)))
      (state 4 final (List.replicate (gap + digits.length) false ++ true ::
        leftRows 29 (unmarkedRows (before ++ List.replicate digits.length true ++ after ++ digits))) (true :: suffix)),
      final.field = saved.field ∧ final.remaining = saved.remaining ∧ final.marked = false ∧ final.next = 4 ∧
      path.posts.length ≤ payloadCost digits.length gap (fieldRows before digits.length after).length := by
  induction digits generalizing saved gap before after with
  | nil =>
    obtain ⟨path, bound⟩ := counter_unmarked_path saved gap (before ++ after) suffix
    refine ⟨{ saved with next := 4 }, ?_⟩
    refine ⟨⟨path.posts, ?_, ?_⟩, rfl, rfl, markedFalse, rfl, ?_⟩
    · simpa [fieldRows_zero] using path.chain
    · simpa [fieldRows_zero] using path.last
    · simpa [payloadCost, fieldRows_length, List.length_append] using bound
  | cons bit digits ih =>
    obtain ⟨first, firstBound⟩ := counter_marked_path saved gap digits.length before after (bit :: (digits ++ suffix))
    obtain ⟨⟨secondPosts, secondChain, secondLast⟩, secondBound⟩ :=
      payload_emit_path { saved with next := 3 } bit gap (fieldRows (before ++ [true]) digits.length after) (digits ++ suffix)
    have secondCount : secondPosts.length ≤
        2 * gap + 2 * (fieldRows before (digits.length + 1) after).length + 8 := by
      simpa [fieldRows_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using secondBound
    let second : ActualPath (TM1.step program)
        (state 3 { saved with next := 3 }
          (List.replicate gap false ++ true :: leftRows 29 (fieldRows (before ++ [true]) digits.length after))
          (true :: bit :: (digits ++ suffix)))
        (state 5 (payloadStore { saved with next := 3 } bit)
          (List.replicate (gap + 1) false ++ true ::
            leftRows 29 (fieldRows (before ++ [true]) digits.length (after ++ [bit])))
          (true :: (digits ++ suffix))) :=
      ⟨secondPosts, secondChain, by simpa only [fieldRows_payload] using secondLast⟩
    obtain ⟨final, ⟨laterPosts, laterChain, laterLast⟩, field, remaining, marked, next, laterBound⟩ :=
      ih (payloadStore { saved with next := 3 } bit) (by simp [payloadStore]) (gap + 1)
        (before ++ [true]) (after ++ [bit])
    have laterCount : laterPosts.length ≤ payloadCost digits.length (gap + 1)
        ((fieldRows before (digits.length + 1) after).length + 1) := by
      simpa [fieldRows_length, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using laterBound
    let later : ActualPath (TM1.step program)
        (state 5 (payloadStore { saved with next := 3 } bit)
          (List.replicate (gap + 1) false ++ true ::
            leftRows 29 (fieldRows (before ++ [true]) digits.length (after ++ [bit])))
          (true :: (digits ++ suffix)))
        (state 4 final (List.replicate (gap + (bit :: digits).length) false ++ true ::
          leftRows 29 (unmarkedRows (before ++ List.replicate (bit :: digits).length true ++ after ++ (bit :: digits))))
          (true :: suffix)) :=
      ⟨laterPosts, laterChain, by
        simpa [List.replicate_succ, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using laterLast⟩
    let joined := (first.trans second).trans later
    refine ⟨final, ⟨joined.posts, ?_, joined.last⟩, ?_, ?_, marked, next, ?_⟩
    · simpa only [List.length_cons, List.cons_append] using joined.chain
    · simpa [payloadStore] using field
    · simpa [payloadStore] using remaining
    · have count : joined.posts.length = first.posts.length + secondPosts.length + laterPosts.length := by
        exact (ActualPath.trans_length (first.trans second) later).trans
          (congrArg (· + laterPosts.length) (ActualPath.trans_length first second))
      rw [count]
      simp only [List.length_cons, payloadCost_step]
      have firstTwo : first.posts.length + secondPosts.length ≤
          4 * gap + 4 * (fieldRows before (digits.length + 1) after).length + 14 := by omega
      exact Nat.add_le_add firstTwo laterCount

end PDROC.BitVM.Common.IO.Wide
