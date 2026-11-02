module

public import Paid.PDROC_BitVM_Common_IO_Output_Finish_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing

abbrev DataRow := Bool × OtherTail

/-- Remaining source cells, top to bottom, already on the real tape.
The genuine original bottomTRUE is last. No runtime counter is stored. -/
def unreadLeft : List DataRow → List Bool
  | [] => []
  | row :: rest => (presentRow rest.isEmpty row.1 row.2).reverse ++ unreadLeft rest

def readingStore (seen : Bool) (current : DataRow) (rest : List DataRow) : Store :=
  ⟨current.1, rest.isEmpty, seen⟩

attribute [local implicit_reducible] readingStore

def readingState (seen : Bool) (current : DataRow) (rest : List DataRow)
    (above : List RowTail) (emitted : List Bool) : TM1.Cfg Bool Label Store :=
  cfg 4 (readingStore seen current rest)
    (readyTape (fullArchive (unreadLeft rest) (sourceTail current.1 current.2) above) emitted)

def runCost (rest above emitted : Nat) : Nat :=
  (rest + 1) * (2 * above + 2 * emitted + 2 * rest + 8) + 64 * (emitted + rest + 2)^2

theorem runCost_step (rest above emitted : Nat) :
    runCost (rest + 1) above emitted =
      2 * above + 2 * emitted + 8 + runCost rest (above + 1) (emitted + 1) := by
  unfold runCost
  ring

/-- Entire actual extraction loop, controlled only by real read bottom
flags. Each iteration shuttles a genuine read bit, returns to the SAME
cursor, actually clears/marks the next row, and continues the same trace.
At bottom the real inverse codec/header scan/HALT completes the output.
No successful-run, width, trace, fuel or output-answer premise is used. -/
theorem read_all_path (seen : Bool) (current : DataRow) (rest : List DataRow)
    (above : List RowTail) (emitted : List Bool) :
    ∃ final : TM1.Cfg Bool Label Store, ∃ path : ActualPath (TM1.step program)
      (readingState seen current rest above emitted) final,
      final.l = none ∧ final.Tape.right₀ = ListBlank.mk (emitted ++ (current :: rest).map Prod.fst) ∧
      path.posts.length ≤ runCost rest.length above.length emitted.length := by
  induction rest generalizing current above emitted with
  | nil =>
    obtain ⟨first, firstLength⟩ := one_bit_return_path (readingStore seen current []) []
      (sourceTail current.1 current.2) above emitted
    obtain ⟨final, second, halted, _, right, bound⟩ :=
      finish_decode_path (readingStore seen current []) rfl [] (sourceTail current.1 current.2)
        above (emitted ++ [current.1])
    let joined := first.trans second
    refine ⟨final, joined, halted, ?_, ?_⟩
    · simpa using right
    · have secondBound : second.posts.length ≤ above.length + 3 + 64 * (emitted.length + 2)^2 := by
        simpa using bound
      have joinedLength : joined.posts.length = first.posts.length + second.posts.length := by
        exact List.length_append
      rw [joinedLength]
      unfold runCost
      simp only [List.length_nil, Nat.add_zero]
      omega
  | cons next rest ih =>
    obtain ⟨first, firstLength⟩ := one_bit_return_path (readingStore seen current (next :: rest))
      (unreadLeft (next :: rest)) (sourceTail current.1 current.2) above emitted
    obtain ⟨second, secondLength⟩ := advance_ready_path (readingStore seen current (next :: rest)) rfl
      rest.isEmpty next.1 next.2 (unreadLeft rest) (sourceTail current.1 current.2) above (emitted ++ [current.1])
    obtain ⟨final, later, halted, right, bound⟩ :=
      ih next (sourceTail current.1 current.2 :: above) (emitted ++ [current.1])
    let advance : ActualPath (TM1.step program)
        (cfg 7 (readingStore seen current (next :: rest))
          (cursorTape (unreadLeft (next :: rest)) (sourceTail current.1 current.2) above (emitted ++ [current.1])))
        (readingState seen next rest (sourceTail current.1 current.2 :: above) (emitted ++ [current.1])) := second
    let joined := (first.trans advance).trans later
    refine ⟨final, joined, halted, ?_, ?_⟩
    · simpa [List.append_assoc] using right
    · have laterBound : later.posts.length ≤ runCost rest.length (above.length + 1) (emitted.length + 1) := by
        simpa using bound
      have advanceLength : advance.posts.length = above.length + 4 := secondLength
      have joinedLength : joined.posts.length = first.posts.length + advance.posts.length + later.posts.length := by
        calc
          joined.posts.length = (first.trans advance).posts.length + later.posts.length := List.length_append
          _ = first.posts.length + advance.posts.length + later.posts.length :=
            congrArg (fun length => length + later.posts.length) List.length_append
      rw [joinedLength]
      simp only [List.length_cons, runCost_step]
      omega

end PDROC.BitVM.Common.IO.Output
