module

public import Paid.PDROC_BitVM_Common_IO_Wide_Runtime_006

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 5000
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

def state (label : Label) (saved : Store) (left right : List Bool) : TM1.Cfg Bool Label Store :=
  ⟨some label, saved, Tape.mk₂ left right⟩

def counterFoundCode : Statement :=
  .load (fun _ saved => { saved with next := 3 }) (.goto (fun _ _ => 12))

def counterInspectCode : Statement :=
  .branch (fun symbol _ => symbol)
    (.write (fun _ _ => false) (moveCode .left 3 counterFoundCode))
    (moveCode .left 4 (.goto (fun _ _ => 7)))

/-- The real LEFT61 traversal reaches physical col3. It retains the
entire unread suffix and all other caller fields, including the bit. -/
theorem counter_inspection (saved : Store) (bit marked : Bool) (left right : List Bool) :
    TM1.step program
      (state 7 saved ((rowPrefix 29 bit marked).reverse ++ left) (true :: right)) =
      some (TM1.stepAux counterInspectCode saved
        (Tape.mk₂ (bit :: true :: false :: left)
          (marked :: (List.replicate 59 false ++ true :: true :: right)))) := by
  let front := true :: (List.replicate 59 false ++ [marked])
  have length : front.length = 61 := by simp [front]
  have moved := moveCode_left front (bit :: true :: false :: left) (true :: right) saved counterInspectCode
  rw [length] at moved
  change some (TM1.stepAux (moveCode .left 61 counterInspectCode) saved
    (Tape.mk₂ ((rowPrefix 29 bit marked).reverse ++ left) (true :: right))) = _
  simpa [front, rowPrefix, padding, List.reverse_append, List.append_assoc] using congrArg some moved

/-- The width counter really loses ONE TRUE mark at col3; only its
observed mark branch requests a new raw payload bit. -/
theorem counter_clear_mark (saved : Store) (bit : Bool) (left right : List Bool) :
    TM1.step program (state 7 saved ((rowPrefix 29 bit true).reverse ++ left) (true :: right)) =
      some (state 12 { saved with next := 3 } left (temporaryRow 29 bit false ++ right)) := by
  rw [counter_inspection]
  change some (TM1.stepAux (moveCode .left 3 counterFoundCode) saved
    (Tape.mk₂ (bit :: true :: false :: left)
      (false :: (List.replicate 59 false ++ true :: true :: right)))) = _
  have moved := moveCode_left [bit, true, false] left
    (false :: (List.replicate 59 false ++ true :: true :: right)) saved counterFoundCode
  simpa [counterFoundCode, TM1.stepAux, state, temporaryRow, rowPrefix, padding, List.append_assoc] using
    congrArg some moved

theorem counter_skip_unmarked (saved : Store) (bit previous : Bool) (left right : List Bool) :
    TM1.step program
      (state 7 saved ((rowPrefix 29 bit false).reverse ++ previous :: left) (true :: right)) =
      some (state 7 saved left (previous :: (temporaryRow 29 bit false ++ right))) := by
  rw [counter_inspection]
  change some (TM1.stepAux (moveCode .left 4 (.goto (fun _ _ => 7))) saved
    (Tape.mk₂ (bit :: true :: false :: previous :: left)
      (false :: (List.replicate 59 false ++ true :: true :: right)))) = _
  have moved := moveCode_left [bit, true, false, previous] left
    (false :: (List.replicate 59 false ++ true :: true :: right)) saved
      (TM1.Stmt.goto (fun _ _ => (7 : Label)))
  simpa [TM1.stepAux, state, temporaryRow, rowPrefix, padding, List.append_assoc] using congrArg some moved

theorem counter_skip_last_unmarked (saved : Store) (bit : Bool) (right : List Bool) :
    TM1.step program (state 7 saved (rowPrefix 29 bit false).reverse (true :: right)) =
      some (state 7 saved [] (false :: (temporaryRow 29 bit false ++ right))) := by
  simpa [state, tape_left_blank] using counter_skip_unmarked saved bit false [] right

/-- The actual blank immediately before the first output row terminates
the search. This branch reads NO further original source bit. -/
theorem counter_no_mark (saved : Store) (right : List Bool) :
    TM1.step program (state 7 saved [] (false :: right)) =
      some (state 12 { saved with next := 4 } [] right) := by
  have moved : (Tape.mk₂ [] (false :: right)).move .right = Tape.mk₂ [] right := by
    calc
      (Tape.mk₂ [] (false :: right)).move .right = Tape.mk₂ [false] right := by simp [Tape.mk₂]
      _ = Tape.mk₂ [] right := tape_left_blank [] right
  change some (TM1.stepAux (.move .right (.load (fun _ old => { old with next := 4 })
    (.goto (fun _ _ => 12)))) saved (Tape.mk₂ [] (false :: right))) = _
  simp only [TM1.stepAux, moved, state]

def markCount (rows : List (Bool × Bool)) : Nat := (rows.filter (fun row => row.2)).length

/-- Pure endpoint specification. The machine never evaluates this list
function; the actual code above scans cells and writes one mark FALSE. -/
def clearFirstMark : List (Bool × Bool) → Option (List (Bool × Bool))
  | [] => none
  | (bit, true) :: rows => some ((bit, false) :: rows)
  | (bit, false) :: rows => (clearFirstMark rows).map ((bit, false) :: ·)

theorem clearFirstMark_bits (rows changed : List (Bool × Bool))
    (found : clearFirstMark rows = some changed) : changed.map Prod.fst = rows.map Prod.fst := by
  induction rows generalizing changed with
  | nil => cases found
  | cons row rows ih =>
    obtain ⟨bit, marked⟩ := row
    cases marked with
    | true =>
      have same : (bit, false) :: rows = changed := Option.some.inj found
      subst changed
      rfl
    | false =>
      cases result : clearFirstMark rows with
      | none => simp [clearFirstMark, result] at found
      | some rest =>
        have same : (bit, false) :: rest = changed :=
          Option.some.inj (by simpa only [clearFirstMark, result, Option.map_some] using found)
        subst changed
        simpa using congrArg (bit :: ·) (ih rest result)

theorem clearFirstMark_none (rows : List (Bool × Bool)) :
    clearFirstMark rows = none ↔ markCount rows = 0 := by
  induction rows with
  | nil => simp [clearFirstMark, markCount]
  | cons row rows ih =>
    obtain ⟨bit, marked⟩ := row
    cases marked with
    | false => simpa [clearFirstMark, markCount] using ih
    | true => simp [clearFirstMark, markCount]

theorem clearFirstMark_count (rows changed : List (Bool × Bool))
    (found : clearFirstMark rows = some changed) : markCount rows = markCount changed + 1 := by
  induction rows generalizing changed with
  | nil => cases found
  | cons row rows ih =>
    obtain ⟨bit, marked⟩ := row
    cases marked with
    | true =>
      have same : (bit, false) :: rows = changed := Option.some.inj found
      subst changed
      simp [markCount]
    | false =>
      cases result : clearFirstMark rows with
      | none => simp [clearFirstMark, result] at found
      | some rest =>
        have same : (bit, false) :: rest = changed :=
          Option.some.inj (by simpa only [clearFirstMark, result, Option.map_some] using found)
        subst changed
        simpa [markCount] using ih rest result

def counterResultRows (rows : List (Bool × Bool)) : List (Bool × Bool) := (clearFirstMark rows).getD rows

def counterResultNext (rows : List (Bool × Bool)) : Fin 6 :=
  if (clearFirstMark rows).isSome then 3 else 4

def counterScan (saved : Store) (todo past : List (Bool × Bool)) (gap : Nat)
    (suffix : List Bool) : TM1.Cfg Bool Label Store :=
  state 7 saved (leftRows 29 todo).tail
    ((leftRows 29 todo).headI :: (physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix)))

def counterEnd (saved : Store) (todo past : List (Bool × Bool)) (gap : Nat)
    (suffix : List Bool) : TM1.Cfg Bool Label Store :=
  state (PDROC.BitVM.Common.IO.Bootstrap.dispatch (counterResultNext todo))
    { saved with next := counterResultNext todo }
    (List.replicate gap false ++ true :: leftRows 29 (past.reverse ++ counterResultRows todo)) (true :: suffix)

theorem counterResultRows_false (bit : Bool) (rows : List (Bool × Bool)) :
    counterResultRows ((bit, false) :: rows) = (bit, false) :: counterResultRows rows := by
  cases result : clearFirstMark rows <;> simp [counterResultRows, clearFirstMark, result]

theorem counterResultNext_false (bit : Bool) (rows : List (Bool × Bool)) :
    counterResultNext ((bit, false) :: rows) = counterResultNext rows := by
  cases result : clearFirstMark rows <;> simp [counterResultNext, clearFirstMark, result]

theorem counterScan_skip (saved : Store) (bit : Bool) (todo past : List (Bool × Bool))
    (gap : Nat) (suffix : List Bool) :
    TM1.step program (counterScan saved ((bit, false) :: todo) past gap suffix) =
      some (counterScan saved todo ((bit, false) :: past) gap suffix) := by
  cases todo with
  | nil =>
    simpa [counterScan, leftRows, physicalRows, temporaryRow, List.reverse_append, List.append_assoc] using
      counter_skip_last_unmarked saved bit (physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix))
  | cons row todo =>
    obtain ⟨nextBit, nextMark⟩ := row
    simpa [counterScan, leftRows, physicalRows, temporaryRow, List.reverse_append, List.append_assoc] using
      counter_skip_unmarked saved bit true
        ((rowPrefix 29 nextBit nextMark).reverse ++ leftRows 29 todo)
        (physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix))

/-- One real q7 search/decrement and row/gap return, retaining the same
selected path and all original bit data. This is the field loop's actual
guard: resultNext=3 requests payload; resultNext=4 advances a fixed field. -/
theorem counter_scan_path (saved : Store) (todo past : List (Bool × Bool)) (gap : Nat)
    (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program) (counterScan saved todo past gap suffix)
      (counterEnd saved todo past gap suffix),
      path.posts.length ≤ 2 * todo.length + past.length + gap + 4 := by
  induction todo generalizing past with
  | nil =>
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := program_return_cursor { saved with next := 4 } gap past [] suffix
    have lengthBound : posts.length ≤ past.length + gap + 2 := bound
    let later : ActualPath (TM1.step program)
        (state 12 { saved with next := 4 } [] (physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix)))
        (counterEnd saved [] past gap suffix) :=
      ⟨posts, chain, by
        simpa [state, counterEnd, counterResultRows, counterResultNext, clearFirstMark,
          physicalRows_reverse, leftRows, List.flatMap_append] using last⟩
    have edge := counter_no_mark saved (physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix))
    refine ⟨(ActualPath.single edge).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega
  | cons row todo ih =>
    obtain ⟨bit, marked⟩ := row
    cases marked with
    | false =>
      obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih ((bit, false) :: past)
      have lengthBound : posts.length ≤ 2 * todo.length + (((bit, false) :: past).length) + gap + 4 := bound
      let later : ActualPath (TM1.step program) (counterScan saved todo ((bit, false) :: past) gap suffix)
          (counterEnd saved ((bit, false) :: todo) past gap suffix) :=
        ⟨posts, chain, by
          simpa [counterEnd, counterResultRows_false, counterResultNext_false,
            List.reverse_cons, List.append_assoc] using last⟩
      refine ⟨(ActualPath.single (counterScan_skip saved bit todo past gap suffix)).trans later, ?_⟩
      simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
      simp only [List.length_cons] at lengthBound
      omega
    | true =>
      obtain ⟨⟨posts, chain, last⟩, bound⟩ :=
        program_return_cursor { saved with next := 3 } gap ((bit, false) :: past) (leftRows 29 todo) suffix
      have lengthBound : posts.length ≤ (((bit, false) :: past).length) + gap + 2 := bound
      let later : ActualPath (TM1.step program)
          (state 12 { saved with next := 3 } (leftRows 29 todo)
            (temporaryRow 29 bit false ++ physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix)))
          (counterEnd saved ((bit, true) :: todo) past gap suffix) :=
        ⟨posts,
          by simpa [state, physicalRows_cons, List.append_assoc] using chain,
          by simpa [state, counterEnd, counterResultRows, counterResultNext, clearFirstMark, physicalRows_cons,
            physicalRows_reverse, leftRows, List.flatMap_append, List.append_assoc] using last⟩
      have edge : TM1.step program (counterScan saved ((bit, true) :: todo) past gap suffix) =
          some (state 12 { saved with next := 3 } (leftRows 29 todo)
            (temporaryRow 29 bit false ++ physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix))) := by
        simpa [counterScan, leftRows, temporaryRow, List.reverse_append, List.append_assoc] using
          counter_clear_mark saved bit (leftRows 29 todo)
            (physicalRows 29 past ++ true :: (List.replicate gap false ++ true :: suffix))
      let joined := (ActualPath.single edge).trans later
      have joinedBound : joined.posts.length ≤ 2 * (todo.length + 1) + past.length + gap + 4 := by
        simp only [joined, ActualPath.trans, ActualPath.single, later,
          List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at lengthBound
        omega
      exact ⟨joined, joinedBound⟩

def counterAnchor (saved : Store) (gap : Nat) (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.Cfg Bool Label Store :=
  let frame := List.replicate gap false ++ true :: leftRows 29 rows
  state 6 saved frame.tail (frame.headI :: right)

theorem counterAnchor_cross (saved : Store) (left right : List Bool) :
    TM1.step program (state 6 saved left (true :: right)) =
      some (state 7 saved left.tail (left.headI :: true :: right)) := by
  cases left <;> simp [TM1.step, TM1.stepAux, program,
    PDROC.BitVM.Common.IO.Bootstrap.program, state, Tape.mk₂]

theorem counterAnchor_step (saved : Store) (gap : Nat) (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.step program (counterAnchor saved (gap + 1) rows right) =
      some (counterAnchor saved gap rows (false :: right)) := by
  cases gap <;> simp [counterAnchor, List.replicate_succ, TM1.step, TM1.stepAux, program,
    PDROC.BitVM.Common.IO.Bootstrap.program, state, Tape.mk₂]

theorem counterAnchor_path (saved : Store) (gap : Nat) (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : ActualPath (TM1.step program) (counterAnchor saved gap rows right)
      (state 7 saved (leftRows 29 rows).tail
        ((leftRows 29 rows).headI :: true :: (List.replicate gap false ++ right))),
      path.posts.length ≤ gap + 1 := by
  induction gap generalizing right with
  | zero =>
    refine ⟨ActualPath.single ?_, Nat.le_refl _⟩
    simpa [counterAnchor] using counterAnchor_cross saved (leftRows 29 rows) right
  | succ gap ih =>
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (false :: right)
    have lengthBound : posts.length ≤ gap + 1 := bound
    let later : ActualPath (TM1.step program) (counterAnchor saved gap rows (false :: right))
        (state 7 saved (leftRows 29 rows).tail
          ((leftRows 29 rows).headI :: true :: (List.replicate (gap + 1) false ++ right))) :=
      ⟨posts, chain, by simpa [List.replicate_add, List.append_assoc] using last⟩
    refine ⟨(ActualPath.single (counterAnchor_step saved gap rows right)).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

/-- The complete true mark-search loop from the actual source cursor.
No mark count, width or successful run is supplied to the program. The
returned finite continuation is determined by those actually observed cells. -/
theorem counter_full_path (saved : Store) (gap : Nat) (rows : List (Bool × Bool)) (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 5 saved (List.replicate gap false ++ true :: leftRows 29 rows) (true :: suffix))
      (state (PDROC.BitVM.Common.IO.Bootstrap.dispatch (counterResultNext rows))
        { saved with next := counterResultNext rows }
        (List.replicate gap false ++ true :: leftRows 29 (counterResultRows rows)) (true :: suffix)),
      path.posts.length ≤ 2 * gap + 2 * rows.length + 6 := by
  have edge : TM1.step program
      (state 5 saved (List.replicate gap false ++ true :: leftRows 29 rows) (true :: suffix)) =
      some (counterAnchor saved gap rows (true :: suffix)) := by
    cases gap <;> simp [counterAnchor, List.replicate_succ, TM1.step, TM1.stepAux, program,
      PDROC.BitVM.Common.IO.Bootstrap.program, state, Tape.mk₂]
  obtain ⟨middle, middleBound⟩ := counterAnchor_path saved gap rows (true :: suffix)
  let center : ActualPath (TM1.step program) (counterAnchor saved gap rows (true :: suffix))
      (counterScan saved rows [] gap suffix) :=
    ⟨middle.posts, middle.chain, by simpa [counterScan, physicalRows] using middle.last⟩
  obtain ⟨last, lastBound⟩ := counter_scan_path saved rows [] gap suffix
  let joined := ((ActualPath.single edge).trans center).trans last
  refine ⟨⟨joined.posts, joined.chain, ?_⟩, ?_⟩
  · simpa [counterEnd] using joined.last
  · have centerLength : center.posts.length = middle.posts.length := rfl
    simp only [joined, ActualPath.trans_length, ActualPath.single, List.length_cons, List.length_nil]
    simp only [List.length_nil] at lastBound
    omega

end PDROC.BitVM.Common.IO.Wide
