module

public import Paid.PDROC_BitVM_Common_IO_Output_Loop_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing

/-- Proof-only descriptions of old occupied rows ABOVE the output
stack. Their actual slot0 presence is absent; some other stack is live.
The complete64 old data cells remain in the tape and in every path. -/
structure AbsentRow where
  row : OccupiedRow
  absent : row.pairs.head? = some (false, false)

def absentTail (row : AbsentRow) : RowTail :=
  ⟨pairBits row.row.pairs, by simp [pairBits_length, row.row.width]⟩

def absentTails (rows : List AbsentRow) : List RowTail := rows.map absentTail

theorem absent_flat (rows : List AbsentRow) :
    flatRows (absentTails rows) = occupiedRows (rows.map AbsentRow.row) := by
  simp [flatRows, absentTails, occupiedRows, occupiedBits, absentTail, rowBits, List.flatMap_map]

theorem absent_two_cells (row : AbsentRow) :
    ∃ suffix : List Bool, occupiedBits row.row = false :: false :: suffix := by
  cases pairs : row.row.pairs with
  | nil =>
    have missing := row.absent
    simp [pairs] at missing
  | cons pair rest =>
    have head : pair = (false, false) := by simpa [pairs] using row.absent
    subst pair
    exact ⟨false :: pairBits rest, by simp [occupiedBits, pairs, pairBits]⟩

theorem blank_pairs_bits : pairBits blankPairs = List.replicate 64 false := rfl

theorem tape_false_padding (left right : List Bool) (count : Nat) :
    Tape.mk₂ left (right ++ List.replicate count false) = Tape.mk₂ left right := by
  have blank : ListBlank.mk (right ++ List.replicate count false) = ListBlank.mk right :=
    Quotient.sound' (Or.inr ⟨count, rfl⟩)
  unfold Tape.mk₂
  rw [blank]

theorem absent_frame_head (rows : List AbsentRow) :
    ∃ suffix : List Bool,
      occupiedRows (rows.map AbsentRow.row) ++ false :: pairBits blankPairs =
        false :: false :: suffix := by
  cases rows with
  | nil => exact ⟨List.replicate 63 false, rfl⟩
  | cons row rest =>
    obtain ⟨suffix, shape⟩ := absent_two_cells row
    refine ⟨suffix ++ occupiedRows (rest.map AbsentRow.row) ++ false :: pairBits blankPairs, ?_⟩
    simp only [List.map_cons, occupiedRows, List.flatMap_cons, shape, List.cons_append]

def sourceDescriptors : List DataRow → List PresentRow
  | [] => []
  | current :: rest => sourceDescriptors rest ++ [(rest.isEmpty, current.1, current.2)]

theorem sourceDescriptors_length (rows : List DataRow) :
    (sourceDescriptors rows).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons current rest ih => simp [sourceDescriptors, ih]

theorem sourceDescriptors_bits (rows : List DataRow) :
    presentRows (sourceDescriptors rows) = (unreadLeft rows).reverse := by
  induction rows with
  | nil => rfl
  | cons current rest ih =>
    have shape : presentRows (sourceDescriptors (current :: rest)) =
        presentRows (sourceDescriptors rest) ++ presentRow rest.isEmpty current.1 current.2 := by
      simp [sourceDescriptors, presentRows, List.flatMap_append]
    rw [shape, ih]
    simp [unreadLeft, List.reverse_append]

theorem ready_empty_anchor (archive : List Bool) :
    readyTape archive [] =
      (fun old : Tape Bool => old.move .right)^[4] (Tape.mk₂ archive [true]) := by
  rw [readyTape_unpadded]
  apply congrArg ((fun old : Tape Bool => old.move .right)^[4])
  exact tape_false_padding archive [true] 2

theorem blank_anchor (archive : List Bool) :
    Tape.mk₂ archive (true :: pairBits blankPairs) = Tape.mk₂ archive [true] := by
  rw [blank_pairs_bits]
  exact tape_false_padding archive [true] 64

/-- The complete actual initialization, starting at the true bottom
of ALL old encoded rows. It scans to the actual output top, reads/marks
that row, probes every remaining occupied row, observes the real blank,
installs its anchor beyond ALL old data, and reaches the loop at q4.
All lengths here describe the existing tape; none is a runtime input. -/
theorem initial_reading_path (saved : Store) (current : DataRow) (rest : List DataRow)
    (rows : List AbsentRow) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 0 saved (Tape.mk₁ ((unreadLeft (current :: rest)).reverse ++ flatRows (absentTails rows))))
      (readingState false current rest (absentTails rows) []),
      path.posts.length = rest.length + rows.length + 4 := by
  obtain ⟨suffix, absentShape⟩ := absent_frame_head rows
  obtain ⟨⟨firstPosts, firstChain, firstLast⟩, firstLength⟩ :=
    install_top_path saved (sourceDescriptors rest) rest.isEmpty current.1 current.2 [] suffix
  have firstBound : firstPosts.length = rest.length + 3 := by simpa [sourceDescriptors_length] using firstLength
  have sourceShape : presentRows (sourceDescriptors rest ++ [(rest.isEmpty, current.1, current.2)]) =
      (unreadLeft (current :: rest)).reverse := sourceDescriptors_bits (current :: rest)
  let padded := occupiedRows (rows.map AbsentRow.row) ++ false :: pairBits blankPairs
  let marked := { saved with bottom := rest.isEmpty, bit := current.1 }
  let left := (presentRow true current.1 current.2).reverse ++ unreadLeft rest
  have padding : Tape.mk₂ [] ((unreadLeft (current :: rest)).reverse ++ padded) =
      Tape.mk₁ ((unreadLeft (current :: rest)).reverse ++ flatRows (absentTails rows)) := by
    rw [absent_flat]
    simpa [padded, blank_pairs_bits, List.replicate_succ, List.append_assoc, Tape.mk₁] using
      tape_false_padding [] ((unreadLeft (current :: rest)).reverse ++
        occupiedRows (rows.map AbsentRow.row)) 65
  let first : ActualPath (TM1.step program)
      (cfg 0 saved (Tape.mk₁ ((unreadLeft (current :: rest)).reverse ++ flatRows (absentTails rows))))
      (cfg 2 marked (Tape.mk₂ left padded)) :=
    ⟨firstPosts,
      by simpa only [sourceShape, ← absentShape, ← padding] using firstChain,
      by simpa only [sourceShape, sourceDescriptors_bits, List.reverse_reverse, List.append_nil,
        ← absentShape, left, marked, ← padding] using firstLast⟩
  obtain ⟨⟨lastPosts, lastChain, lastLast⟩, lastLength⟩ :=
    end_rows_path marked (rows.map AbsentRow.row) left []
  have lastBound : lastPosts.length = rows.length + 1 := by simpa using lastLength
  let later : ActualPath (TM1.step program) (cfg 2 marked (Tape.mk₂ left padded))
      (readingState false current rest (absentTails rows) []) :=
    ⟨lastPosts,
      by simpa only [padded, List.append_nil] using lastChain,
      by simpa [readingState, readingStore, scannedStore, marked, fullArchive, sourceTail_bits,
        left, padded, absent_flat, ready_empty_anchor, blank_anchor, List.append_assoc] using lastLast⟩
  refine ⟨first.trans later, ?_⟩
  simp only [ActualPath.trans, first, later, List.length_append]
  omega

/-- A coarse fixed quadratic budget; no per-cell multiplication of an
operand bit bound is used. This counts actual source transitions, whose
physical movements are then paid by the fixed SupportClock compiler. -/
theorem runCost_quadratic (rest above emitted : Nat) :
    runCost rest above emitted ≤ 128 * (above + emitted + 2 * rest + 2)^2 := by
  let cap := above + emitted + 2 * rest + 2
  have restBound : rest + 1 ≤ cap := by dsimp [cap]; omega
  have linearBound : 2 * above + 2 * emitted + 2 * rest + 8 ≤ 4 * cap := by dsimp [cap]; omega
  have squareBound : (emitted + rest + 2)^2 ≤ cap^2 := by
    apply Nat.pow_le_pow_left
    dsimp [cap]
    omega
  have product := Nat.mul_le_mul restBound linearBound
  have other := Nat.mul_le_mul_left 64 squareBound
  unfold runCost
  nlinarith

/-- Initialization and every extraction/decode transition belong to
one selected actual path from the whole initial tape, with true HALT and
only the requested naked output at right0. The old archive is traversed,
never supplied as a work bound or erased for free. -/
theorem framed_output_path (saved : Store) (current : DataRow) (rest : List DataRow)
    (rows : List AbsentRow) :
    ∃ final : TM1.Cfg Bool Label Store, ∃ path : ActualPath (TM1.step program)
      (cfg 0 saved (Tape.mk₁ ((unreadLeft (current :: rest)).reverse ++ flatRows (absentTails rows)))) final,
      final.l = none ∧ final.Tape.right₀ = ListBlank.mk ((current :: rest).map Prod.fst) ∧
      path.posts.length ≤ rest.length + rows.length + 4 +
        128 * (rows.length + 2 * rest.length + 2)^2 := by
  obtain ⟨first, firstLength⟩ := initial_reading_path saved current rest rows
  obtain ⟨final, second, halt, right, bound⟩ := read_all_path false current rest (absentTails rows) []
  let joined := first.trans second
  refine ⟨final, joined, halt, by simpa using right, ?_⟩
  have secondBound : second.posts.length ≤ 128 * (rows.length + 2 * rest.length + 2)^2 := by
    have numeric := runCost_quadratic rest.length rows.length 0
    have clean : second.posts.length ≤ runCost rest.length rows.length 0 := by
      simpa [absentTails] using bound
    simpa using clean.trans numeric
  simp only [joined, ActualPath.trans, List.length_append]
  omega

end PDROC.BitVM.Common.IO.Output
