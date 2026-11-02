module

public import Paid.PDROC_BitVM_Common_IO_Wide_Primitives_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

abbrev EmitPath (extraPairs : Nat) (marked : Bool) := ActualPath (TM1.step (emitProgram extraPairs marked))

def leftRows (extraPairs : Nat) (rows : List (Bool × Bool)) : List Bool :=
  rows.flatMap (fun row => (temporaryRow extraPairs row.1 row.2).reverse)

def physicalRows (extraPairs : Nat) (rows : List (Bool × Bool)) : List Bool :=
  rows.flatMap (fun row => temporaryRow extraPairs row.1 row.2)

theorem physicalRows_cons (extraPairs : Nat) (row : Bool × Bool) (rows : List (Bool × Bool)) :
    physicalRows extraPairs (row :: rows) = temporaryRow extraPairs row.1 row.2 ++ physicalRows extraPairs rows := by
  simp only [physicalRows, List.flatMap_cons]

theorem leftRows_append (extraPairs : Nat) (first second : List (Bool × Bool)) :
    leftRows extraPairs (first ++ second) = leftRows extraPairs first ++ leftRows extraPairs second := by
  simp only [leftRows, List.flatMap_append]

theorem leftRows_singleton (extraPairs : Nat) (row : Bool × Bool) :
    leftRows extraPairs [row] = (temporaryRow extraPairs row.1 row.2).reverse := by
  simp only [leftRows, List.flatMap_cons, List.flatMap_nil, List.append_nil]

def rowScan (extraPairs : Nat) (saved : Bool) (rows : List (Bool × Bool)) (right : List Bool) : EmitState :=
  emitState (some 2) saved (leftRows extraPairs rows).tail ((leftRows extraPairs rows).headI :: right)

theorem rowScan_skip (extraPairs : Nat) (marked saved bit oldMark : Bool)
    (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.step (emitProgram extraPairs marked) (rowScan extraPairs saved ((bit, oldMark) :: rows) right) =
      some (rowScan extraPairs saved rows (temporaryRow extraPairs bit oldMark ++ right)) := by
  cases rows with
  | nil =>
    simpa [rowScan, leftRows, temporaryRow, List.reverse_append] using
      emit_skip_last_row extraPairs marked saved bit oldMark right
  | cons row rows =>
    obtain ⟨nextBit, nextMark⟩ := row
    simpa [rowScan, leftRows, temporaryRow, List.reverse_append, List.append_assoc] using
      emit_skip_row extraPairs marked saved bit oldMark true
        ((rowPrefix extraPairs nextBit nextMark).reverse ++ leftRows extraPairs rows) right

theorem scan_write_path (extraPairs : Nat) (marked bit : Bool)
    (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : EmitPath extraPairs marked (rowScan extraPairs bit rows right)
      (emitState (some 3) bit []
        (temporaryRow extraPairs bit marked ++ (leftRows extraPairs rows).reverse ++ right)),
      path.posts.length ≤ rows.length + 1 := by
  induction rows generalizing right with
  | nil =>
    refine ⟨ActualPath.single ?_, Nat.le_refl _⟩
    simpa [rowScan, leftRows] using emit_write_row extraPairs marked bit right
  | cons row rows ih =>
    obtain ⟨oldBit, oldMark⟩ := row
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (temporaryRow extraPairs oldBit oldMark ++ right)
    have lengthBound : posts.length ≤ rows.length + 1 := bound
    let later : EmitPath extraPairs marked
        (rowScan extraPairs bit rows (temporaryRow extraPairs oldBit oldMark ++ right))
        (emitState (some 3) bit []
          (temporaryRow extraPairs bit marked ++ (leftRows extraPairs ((oldBit, oldMark) :: rows)).reverse ++ right)) :=
      ⟨posts, chain, by simpa [leftRows, List.reverse_append, List.append_assoc] using last⟩
    refine ⟨(ActualPath.single (rowScan_skip extraPairs marked bit oldBit oldMark rows right)).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

theorem return_rows_path (extraPairs : Nat) (marked saved : Bool)
    (rows : List (Bool × Bool)) (left right : List Bool) :
    ∃ path : EmitPath extraPairs marked
      (emitState (some 3) saved left (physicalRows extraPairs rows ++ true :: right))
      (emitState (some 4) saved (true :: ((physicalRows extraPairs rows).reverse ++ left)) right),
      path.posts.length ≤ rows.length + 1 := by
  induction rows generalizing left with
  | nil => exact ⟨ActualPath.single (emit_return_anchor extraPairs marked saved left right), Nat.le_refl _⟩
  | cons row rows ih =>
    obtain ⟨bit, oldMark⟩ := row
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih ((temporaryRow extraPairs bit oldMark).reverse ++ left)
    have lengthBound : posts.length ≤ rows.length + 1 := bound
    let later : EmitPath extraPairs marked
        (emitState (some 3) saved ((temporaryRow extraPairs bit oldMark).reverse ++ left)
          (physicalRows extraPairs rows ++ true :: right))
        (emitState (some 4) saved
          (true :: ((physicalRows extraPairs ((bit, oldMark) :: rows)).reverse ++ left)) right) :=
      ⟨posts, chain, by simpa [physicalRows, List.reverse_append, List.append_assoc] using last⟩
    have edge : TM1.step (emitProgram extraPairs marked)
        (emitState (some 3) saved left (physicalRows extraPairs ((bit, oldMark) :: rows) ++ true :: right)) =
        some (emitState (some 3) saved ((temporaryRow extraPairs bit oldMark).reverse ++ left)
          (physicalRows extraPairs rows ++ true :: right)) := by
      simpa only [physicalRows_cons, List.append_assoc] using
        emit_return_row extraPairs marked saved bit oldMark left (physicalRows extraPairs rows ++ true :: right)
    refine ⟨(ActualPath.single edge).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

def anchorSearch (extraPairs : Nat) (saved : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (right : List Bool) : EmitState :=
  let frame := List.replicate gap false ++ true :: leftRows extraPairs rows
  emitState (some 1) saved frame.tail (frame.headI :: right)

theorem anchor_cross (extraPairs : Nat) (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram extraPairs marked) (emitState (some 1) saved left (true :: right)) =
      some (emitState (some 2) saved left.tail (left.headI :: true :: right)) := by
  cases left with
  | nil => simp [TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]
  | cons previous archive => exact emit_anchor_true extraPairs marked saved previous archive right

theorem anchorSearch_step (extraPairs : Nat) (marked saved : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.step (emitProgram extraPairs marked) (anchorSearch extraPairs saved (gap + 1) rows right) =
      some (anchorSearch extraPairs saved gap rows (false :: right)) := by
  cases gap <;> simp [anchorSearch, List.replicate_succ, TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]

theorem anchorSearch_path (extraPairs : Nat) (marked saved : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : EmitPath extraPairs marked (anchorSearch extraPairs saved gap rows right)
      (rowScan extraPairs saved rows (true :: (List.replicate gap false ++ right))),
      path.posts.length ≤ gap + 1 := by
  induction gap generalizing right with
  | zero =>
    refine ⟨ActualPath.single ?_, Nat.le_refl _⟩
    simpa [anchorSearch, rowScan] using anchor_cross extraPairs marked saved (leftRows extraPairs rows) right
  | succ gap ih =>
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (false :: right)
    have lengthBound : posts.length ≤ gap + 1 := bound
    let later : EmitPath extraPairs marked (anchorSearch extraPairs saved gap rows (false :: right))
        (rowScan extraPairs saved rows (true :: (List.replicate (gap + 1) false ++ right))) :=
      ⟨posts, chain, by simpa [List.replicate_add, List.append_assoc] using last⟩
    refine ⟨(ActualPath.single (anchorSearch_step extraPairs marked saved gap rows right)).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

theorem read_to_anchor (extraPairs : Nat) (marked saved bit : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (suffix : List Bool) :
    ∃ path : EmitPath extraPairs marked
      (emitState (some 0) saved (List.replicate gap false ++ true :: leftRows extraPairs rows) (true :: bit :: suffix))
      (rowScan extraPairs bit rows (true :: (List.replicate (gap + 1) false ++ true :: suffix))),
      path.posts.length ≤ gap + 2 := by
  have edge : TM1.step (emitProgram extraPairs marked)
      (emitState (some 0) saved (List.replicate gap false ++ true :: leftRows extraPairs rows) (true :: bit :: suffix)) =
      some (anchorSearch extraPairs bit gap rows (false :: true :: suffix)) := by
    cases gap with
    | zero => simpa [anchorSearch] using emit_read extraPairs marked saved bit true (leftRows extraPairs rows) suffix
    | succ gap =>
      simpa [anchorSearch, List.replicate_succ] using
        emit_read extraPairs marked saved bit false (List.replicate gap false ++ true :: leftRows extraPairs rows) suffix
  obtain ⟨⟨posts, chain, last⟩, bound⟩ := anchorSearch_path extraPairs marked bit gap rows (false :: true :: suffix)
  have lengthBound : posts.length ≤ gap + 1 := bound
  let later : EmitPath extraPairs marked (anchorSearch extraPairs bit gap rows (false :: true :: suffix))
      (rowScan extraPairs bit rows (true :: (List.replicate (gap + 1) false ++ true :: suffix))) :=
    ⟨posts, chain, by simpa [List.replicate_add, List.append_assoc] using last⟩
  refine ⟨(ActualPath.single edge).trans later, ?_⟩
  simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
  omega

theorem cursorSearch_path (extraPairs : Nat) (marked saved : Bool) (gap : Nat) (left suffix : List Bool) :
    ∃ path : EmitPath extraPairs marked
      (emitState (some 4) saved left (List.replicate gap false ++ true :: suffix))
      (emitState (some 5) saved (List.replicate gap false ++ left) (true :: suffix)),
      path.posts.length ≤ gap + 1 := by
  induction gap generalizing left with
  | zero => exact ⟨ActualPath.single (emit_cursor_found extraPairs marked saved left suffix), Nat.le_refl _⟩
  | succ gap ih =>
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (false :: left)
    have lengthBound : posts.length ≤ gap + 1 := bound
    let later : EmitPath extraPairs marked
        (emitState (some 4) saved (false :: left) (List.replicate gap false ++ true :: suffix))
        (emitState (some 5) saved (List.replicate (gap + 1) false ++ left) (true :: suffix)) :=
      ⟨posts, chain, by simpa [List.replicate_add, List.append_assoc] using last⟩
    have edge := emit_cursor_false extraPairs marked saved left (List.replicate gap false ++ true :: suffix)
    refine ⟨(ActualPath.single edge).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

theorem leftRows_reverse (extraPairs : Nat) (rows : List (Bool × Bool)) :
    (leftRows extraPairs rows).reverse = physicalRows extraPairs rows.reverse := by
  unfold leftRows physicalRows
  rw [List.reverse_flatMap]
  simp only [Function.comp_def, List.reverse_reverse]

theorem physicalRows_reverse (extraPairs : Nat) (rows : List (Bool × Bool)) :
    (physicalRows extraPairs rows).reverse = leftRows extraPairs rows.reverse := by
  simpa only [List.reverse_reverse] using (congrArg List.reverse (leftRows_reverse extraPairs rows.reverse)).symm

/-- One selected real chain performs every scan/write and returns at
the new cursor. Final VM specializes extraPairs=29 before all inputs.
TM1's internal fixed stride moves are later charged by SupportClock. -/
theorem emit_one_bit_path (extraPairs : Nat) (marked saved bit : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (suffix : List Bool) :
    ∃ path : EmitPath extraPairs marked
      (emitState (some 0) saved (List.replicate gap false ++ true :: leftRows extraPairs rows) (true :: bit :: suffix))
      (emitState (some 5) bit
        (List.replicate (gap + 1) false ++ true :: leftRows extraPairs (rows ++ [(bit, marked)])) (true :: suffix)),
      path.posts.length ≤ 2 * gap + 2 * rows.length + 7 := by
  obtain ⟨first, firstBound⟩ := read_to_anchor extraPairs marked saved bit gap rows suffix
  obtain ⟨second, secondBound⟩ := scan_write_path extraPairs marked bit rows
    (true :: (List.replicate (gap + 1) false ++ true :: suffix))
  obtain ⟨⟨thirdPosts, thirdChain, thirdLast⟩, thirdBound⟩ :=
    return_rows_path extraPairs marked bit ((bit, marked) :: rows.reverse) []
      (List.replicate (gap + 1) false ++ true :: suffix)
  have thirdCount : thirdPosts.length ≤ rows.length + 2 := by
    simpa only [List.length_cons, List.length_reverse] using thirdBound
  let third : EmitPath extraPairs marked
      (emitState (some 3) bit []
        (temporaryRow extraPairs bit marked ++ (leftRows extraPairs rows).reverse ++
          true :: (List.replicate (gap + 1) false ++ true :: suffix)))
      (emitState (some 4) bit (true :: leftRows extraPairs (rows ++ [(bit, marked)]))
        (List.replicate (gap + 1) false ++ true :: suffix)) :=
    ⟨thirdPosts,
      by simpa only [physicalRows_cons, leftRows_reverse, List.append_assoc] using thirdChain,
      by simpa only [physicalRows_cons, leftRows_reverse, List.reverse_append, List.append_nil,
        physicalRows_reverse, List.reverse_reverse, leftRows_append, leftRows_singleton,
        List.append_assoc] using thirdLast⟩
  obtain ⟨fourth, fourthBound⟩ := cursorSearch_path extraPairs marked bit (gap + 1)
    (true :: leftRows extraPairs (rows ++ [(bit, marked)])) suffix
  refine ⟨((first.trans second).trans third).trans fourth, ?_⟩
  simp only [ActualPath.trans_length]
  have thirdLength : third.posts.length = thirdPosts.length := rfl
  omega

end PDROC.BitVM.Common.IO.Wide
