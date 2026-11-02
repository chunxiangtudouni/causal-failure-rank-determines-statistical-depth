module

public import Paid.PDROC_BitVM_Common_IO_Wide_Payload_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

def rawField (digits : List Bool) : List Bool := List.replicate digits.length true ++ false :: digits

def natFieldCost (count gap rows : Nat) : Nat :=
  unaryCost count gap rows + payloadCost count (gap + count + 1) (rows + count + 1)

/-- Real unary counting AND the complete payload loop. The incoming
rows are already genuine emitted data; no width, answer, run or working
tape is supplied to the program. All resulting marks are actually FALSE. -/
theorem nat_field_path (saved : Store) (gap : Nat) (before digits suffix : List Bool) :
    ∃ final : Store, ∃ path : ActualPath (TM1.step program)
      (state 2 saved (List.replicate gap false ++ true :: leftRows 29 (unmarkedRows before))
        (true :: (rawField digits ++ suffix)))
      (state 4 final (List.replicate (gap + (rawField digits).length) false ++
        true :: leftRows 29 (unmarkedRows (before ++ rawField digits))) (true :: suffix)),
      final.field = saved.field ∧ final.remaining = saved.remaining ∧ final.marked = false ∧ final.next = 4 ∧
      path.posts.length ≤ natFieldCost digits.length gap before.length := by
  obtain ⟨first, firstBound⟩ := unary_header_path saved digits.length gap (unmarkedRows before) (digits ++ suffix)
  obtain ⟨final, ⟨posts, chain, last⟩, field, remaining, marked, next, bound⟩ :=
    payload_loop_path (unaryStore saved false) (by rfl) (gap + digits.length + 1) before [false] digits suffix
  have payloadBound : posts.length ≤ payloadCost digits.length (gap + digits.length + 1)
      (before.length + digits.length + 1) := by
    simpa [fieldRows_length] using bound
  let later : ActualPath (TM1.step program)
      (state 5 (unaryStore saved false)
        (List.replicate (gap + digits.length + 1) false ++ true ::
          leftRows 29 (unmarkedRows before ++ List.replicate digits.length (true, true) ++ [(false, false)]))
        (true :: (digits ++ suffix)))
      (state 4 final (List.replicate (gap + (rawField digits).length) false ++
        true :: leftRows 29 (unmarkedRows (before ++ rawField digits))) (true :: suffix)) :=
    ⟨posts,
      by simpa [fieldRows, unmarkedRows] using chain,
      by simpa [fieldRows, unmarkedRows, rawField, List.length_append, List.length_replicate, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last⟩
  let joined := first.trans later
  refine ⟨final, ⟨joined.posts, ?_, ?_⟩, ?_, ?_, marked, next, ?_⟩
  · simpa [rawField, List.append_assoc] using joined.chain
  · simpa [rawField, List.append_assoc] using joined.last
  · simpa [unaryStore] using field
  · simpa [unaryStore] using remaining
  · have count : joined.posts.length = first.posts.length + posts.length :=
      ActualPath.trans_length first later
    rw [count]
    have firstCount : first.posts.length ≤ unaryCost digits.length gap before.length := by
      simpa [unmarkedRows] using firstBound
    exact Nat.add_le_add firstCount payloadBound

theorem rawField_length (digits : List Bool) : (rawField digits).length = 2 * digits.length + 1 := by
  simp [rawField]
  omega

theorem natFieldCost_coarse (count gap rows : Nat) :
    natFieldCost count gap rows ≤ 64 * (count + 1) * (gap + rows + count + 2) := by
  unfold natFieldCost unaryCost payloadCost
  nlinarith [Nat.zero_le (count * gap), Nat.zero_le (count * rows), Nat.zero_le (count * count)]

end PDROC.BitVM.Common.IO.Wide
