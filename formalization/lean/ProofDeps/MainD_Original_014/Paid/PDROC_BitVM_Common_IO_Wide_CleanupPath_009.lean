module

public import Paid.PDROC_BitVM_Common_IO_Wide_Cleanup_008

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 5000
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

theorem tape_right_blanks (left right : List Bool) (count : Nat) :
    Tape.mk₂ left (right ++ List.replicate count false) = Tape.mk₂ left right := by
  have blank : ListBlank.mk (right ++ List.replicate count false) = ListBlank.mk right :=
    Quotient.sound' (Or.inr ⟨count, rfl⟩)
  unfold Tape.mk₂
  rw [blank]

/-- Return across every already cleaned row, including the TRUE-bottom
first row. The positive path really moves; it cannot be a reset of head. -/
theorem back_rows_path (saved : Store) (firstBit : Bool) (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 19 saved ((cleanRows rows).reverse ++ (cleanRow 29 true firstBit).reverse) (false :: right))
      (state 19 saved [] (cleanRow 29 true firstBit ++ cleanRows rows ++ false :: right)),
      0 < path.posts.length ∧ path.posts.length ≤ rows.length + 1 := by
  induction rows using List.reverseRecOn generalizing right with
  | nil =>
    have edge : TM1.step program
        (state 19 saved ((cleanRows []).reverse ++ (cleanRow 29 true firstBit).reverse) (false :: right)) =
        some (state 19 saved [] (cleanRow 29 true firstBit ++ cleanRows [] ++ false :: right)) := by
      simpa [cleanRows] using cleanup_back_row saved true firstBit [] right
    refine ⟨ActualPath.single edge, ?_, ?_⟩ <;> simp [ActualPath.single]
  | append_singleton rows row ih =>
    obtain ⟨bit, marked⟩ := row
    obtain ⟨⟨posts, chain, last⟩, positive, bound⟩ :=
      ih ((cleanRow 29 false bit).tail ++ false :: right)
    have lengthBound : posts.length ≤ rows.length + 1 := bound
    let later : ActualPath (TM1.step program)
        (state 19 saved ((cleanRows rows).reverse ++ (cleanRow 29 true firstBit).reverse)
          (cleanRow 29 false bit ++ false :: right))
        (state 19 saved [] (cleanRow 29 true firstBit ++ cleanRows (rows ++ [(bit, marked)]) ++ false :: right)) :=
      ⟨posts, chain, by
        simpa [cleanRows, cleanRow, padding, List.flatMap_append, List.append_assoc] using last⟩
    have edge : TM1.step program
        (state 19 saved ((cleanRows (rows ++ [(bit, marked)])).reverse ++ (cleanRow 29 true firstBit).reverse)
          (false :: right)) =
        some (state 19 saved ((cleanRows rows).reverse ++ (cleanRow 29 true firstBit).reverse)
          (cleanRow 29 false bit ++ false :: right)) := by
      simpa [cleanRows, List.flatMap_append, List.reverse_append, List.append_assoc] using
        cleanup_back_row saved false bit ((cleanRows rows).reverse ++ (cleanRow 29 true firstBit).reverse) right
    refine ⟨(ActualPath.single edge).trans later, ?_, ?_⟩
    · simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
      omega
    · simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil,
        List.length_append]
      omega

/-- q18 really erases the anchor before performing the same backward
stride as q19. Only the already proved actual step is substituted. -/
theorem cleanup_anchor_back (saved : Store) (left right : List Bool) :
    TM1.step program (state 18 saved left (true :: right)) =
      TM1.step program (state 19 saved left (false :: right)) := by
  rfl

theorem anchor_return_path (saved : Store) (firstBit : Bool) (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 18 saved ((cleanRows rows).reverse ++ (cleanRow 29 true firstBit).reverse) (true :: right))
      (⟨none, saved, Tape.mk₂ [] (cleanRow 29 true firstBit ++ cleanRows rows ++ false :: right)⟩ :
        TM1.Cfg Bool Label Store),
      path.posts.length ≤ rows.length + 2 := by
  obtain ⟨⟨posts, chain, last⟩, positive, bound⟩ := back_rows_path saved firstBit rows right
  have lengthBound : posts.length ≤ rows.length + 1 := bound
  cases posts with
  | nil => simp at positive
  | cons next rest =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    have newEdge : TM1.step program
        (state 18 saved ((cleanRows rows).reverse ++ (cleanRow 29 true firstBit).reverse) (true :: right)) = some next := by
      rw [cleanup_anchor_back]
      exact edge
    let replaced : ActualPath (TM1.step program)
        (state 18 saved ((cleanRows rows).reverse ++ (cleanRow 29 true firstBit).reverse) (true :: right))
        (state 19 saved [] (cleanRow 29 true firstBit ++ cleanRows rows ++ false :: right)) :=
      ⟨next :: rest, List.isChain_cons_cons.mpr ⟨newEdge, tailChain⟩,
        by simpa only [List.getLast?_cons_cons] using last⟩
    have stop : TM1.step program (state 19 saved [] (cleanRow 29 true firstBit ++ cleanRows rows ++ false :: right)) =
        some (⟨none, saved, Tape.mk₂ [] (cleanRow 29 true firstBit ++ cleanRows rows ++ false :: right)⟩ :
          TM1.Cfg Bool Label Store) := by
      exact cleanup_at_bottom saved [] ((cleanRow 29 true firstBit).tail ++ cleanRows rows ++ false :: right)
    refine ⟨replaced.trans (ActualPath.single stop), ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, replaced, List.length_cons, List.length_nil]
    simp only [List.length_cons] at lengthBound
    omega

/-- Nonempty physical output is cleaned and halted with its full tape
preserved exactly. Nonemptiness will come from the genuine RAW6 footer;
the construction never pretends cleanup works on zero emitted rows. -/
theorem clean_nonempty_path (saved : Store) (firstBit firstMark : Bool)
    (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 17 saved [] (temporaryRow 29 firstBit firstMark ++ physicalRows 29 rows ++ true :: right))
      (⟨none, saved, Tape.mk₂ [] (cleanRow 29 true firstBit ++ cleanRows rows ++ false :: right)⟩ :
        TM1.Cfg Bool Label Store),
      path.posts.length ≤ 2 * rows.length + 3 := by
  have edge := cleanup_first_row saved firstBit firstMark [] (physicalRows 29 rows ++ true :: right)
  obtain ⟨middle, middleBound⟩ := cleanup_rows_path saved rows (cleanRow 29 true firstBit).reverse (true :: right)
  obtain ⟨last, lastBound⟩ := anchor_return_path saved firstBit rows right
  let joined := ((ActualPath.single edge).trans middle).trans last
  refine ⟨⟨joined.posts, ?_, joined.last⟩, ?_⟩
  · simpa only [List.append_assoc] using joined.chain
  · simp only [joined, ActualPath.trans, ActualPath.single, List.length_append, List.length_cons, List.length_nil]
    omega

def cleanupAnchor (saved : Store) (gap : Nat) (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.Cfg Bool Label Store :=
  let frame := List.replicate gap false ++ true :: leftRows 29 rows
  state 15 saved frame.tail (frame.headI :: right)

def cleanupScan (saved : Store) (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.Cfg Bool Label Store :=
  state 16 saved (leftRows 29 rows).tail ((leftRows 29 rows).headI :: right)

theorem cleanupAnchor_cross (saved : Store) (left right : List Bool) :
    TM1.step program (state 15 saved left (true :: right)) =
      some (state 16 saved left.tail (left.headI :: true :: right)) := by
  cases left <;> simp [TM1.step, TM1.stepAux, program,
    PDROC.BitVM.Common.IO.Bootstrap.program, state, Tape.mk₂]

theorem cleanupAnchor_step (saved : Store) (gap : Nat) (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.step program (cleanupAnchor saved (gap + 1) rows right) =
      some (cleanupAnchor saved gap rows (false :: right)) := by
  cases gap <;> simp [cleanupAnchor, List.replicate_succ, TM1.step, TM1.stepAux, program,
    PDROC.BitVM.Common.IO.Bootstrap.program, state, Tape.mk₂]

theorem cleanupAnchor_path (saved : Store) (gap : Nat) (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : ActualPath (TM1.step program) (cleanupAnchor saved gap rows right)
      (cleanupScan saved rows (true :: (List.replicate gap false ++ right))),
      path.posts.length ≤ gap + 1 := by
  induction gap generalizing right with
  | zero =>
    refine ⟨ActualPath.single ?_, Nat.le_refl _⟩
    simpa [cleanupAnchor, cleanupScan] using cleanupAnchor_cross saved (leftRows 29 rows) right
  | succ gap ih =>
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (false :: right)
    have lengthBound : posts.length ≤ gap + 1 := bound
    let later : ActualPath (TM1.step program) (cleanupAnchor saved gap rows (false :: right))
        (cleanupScan saved rows (true :: (List.replicate (gap + 1) false ++ right))) :=
      ⟨posts, chain, by simpa [List.replicate_add, List.append_assoc] using last⟩
    refine ⟨(ActualPath.single (cleanupAnchor_step saved gap rows right)).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

theorem cleanup_skip_row (saved : Store) (bit marked previous : Bool) (left right : List Bool) :
    TM1.step program
      (state 16 saved ((rowPrefix 29 bit marked).reverse ++ previous :: left) (true :: right)) =
      some (state 16 saved left (previous :: (temporaryRow 29 bit marked ++ right))) := by
  have moved := moveCode_left ((rowPrefix 29 bit marked).reverse ++ [previous]) left (true :: right) saved
    (TM1.Stmt.goto (fun _ _ => (16 : Label)))
  have count : ((rowPrefix 29 bit marked).reverse ++ [previous]).length = 65 := by
    simpa only [List.length_append, List.length_reverse, List.length_cons, List.length_nil, stride] using
      rowPrefix_length 29 bit marked
  rw [count] at moved
  change some (TM1.stepAux (moveCode .left 65 (.goto (fun _ _ => 16))) saved
    (Tape.mk₂ ((rowPrefix 29 bit marked).reverse ++ previous :: left) (true :: right))) = _
  simpa [TM1.stepAux, state, temporaryRow, List.reverse_append, List.append_assoc] using congrArg some moved

theorem cleanup_skip_last_row (saved : Store) (bit marked : Bool) (right : List Bool) :
    TM1.step program (state 16 saved (rowPrefix 29 bit marked).reverse (true :: right)) =
      some (state 16 saved [] (false :: (temporaryRow 29 bit marked ++ right))) := by
  simpa [state, tape_left_blank] using cleanup_skip_row saved bit marked false [] right

theorem cleanup_left_end (saved : Store) (right : List Bool) :
    TM1.step program (state 16 saved [] (false :: right)) = some (state 17 saved [] right) := by
  have moved : (Tape.mk₂ [] (false :: right)).move .right = Tape.mk₂ [] right := by
    calc
      (Tape.mk₂ [] (false :: right)).move .right = Tape.mk₂ [false] right := by simp [Tape.mk₂]
      _ = Tape.mk₂ [] right := tape_left_blank [] right
  change some (TM1.stepAux (.move .right (.goto (fun _ _ => 17))) saved (Tape.mk₂ [] (false :: right))) = _
  simp only [TM1.stepAux, moved, state]

theorem cleanupScan_skip (saved : Store) (bit marked : Bool) (rows : List (Bool × Bool)) (right : List Bool) :
    TM1.step program (cleanupScan saved ((bit, marked) :: rows) right) =
      some (cleanupScan saved rows (temporaryRow 29 bit marked ++ right)) := by
  cases rows with
  | nil =>
    simpa [cleanupScan, leftRows, temporaryRow, List.reverse_append] using cleanup_skip_last_row saved bit marked right
  | cons row rows =>
    obtain ⟨nextBit, nextMark⟩ := row
    simpa [cleanupScan, leftRows, temporaryRow, List.reverse_append, List.append_assoc] using
      cleanup_skip_row saved bit marked true ((rowPrefix 29 nextBit nextMark).reverse ++ leftRows 29 rows) right

/-- The actual left search restores the newest (footer) row as first,
without an independent bottom column or uncharged reversal. -/
theorem cleanupScan_path (saved : Store) (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : ActualPath (TM1.step program) (cleanupScan saved rows right)
      (state 17 saved [] ((leftRows 29 rows).reverse ++ right)),
      path.posts.length ≤ rows.length + 1 := by
  induction rows generalizing right with
  | nil =>
    refine ⟨ActualPath.single ?_, Nat.le_refl _⟩
    simpa [cleanupScan, leftRows] using cleanup_left_end saved right
  | cons row rows ih =>
    obtain ⟨bit, marked⟩ := row
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (temporaryRow 29 bit marked ++ right)
    have lengthBound : posts.length ≤ rows.length + 1 := bound
    let later : ActualPath (TM1.step program) (cleanupScan saved rows (temporaryRow 29 bit marked ++ right))
        (state 17 saved [] ((leftRows 29 ((bit, marked) :: rows)).reverse ++ right)) :=
      ⟨posts, chain, by simpa [leftRows, List.reverse_append, List.append_assoc] using last⟩
    refine ⟨(ActualPath.single (cleanupScan_skip saved bit marked rows right)).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

theorem cleanRows_word (rows : List (Bool × Bool)) :
    cleanRows rows.reverse = (rows.map Prod.fst).reverse.flatMap (cleanRow 29 false) := by
  simp only [cleanRows, ← List.map_reverse, List.flatMap_map]

/-- Actual last-cursor erasure, both anchor/row searches, all-cell
cleanup and actual return/HALT. The ENTIRE final Tape is the original
Mathlib Fin32 trInit encoding. All old input/anchor/cursor cells are blank. -/
theorem complete_cleanup_path (saved : Store) (gap : Nat) (rows : List (Bool × Bool))
    (lastBit lastMark : Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 14 saved (List.replicate gap false ++ true :: leftRows 29 (rows ++ [(lastBit, lastMark)])) [true])
      (⟨none, saved, Tape.mk₁ (encodedInit32 (rows.map Prod.fst ++ [lastBit]))⟩ : TM1.Cfg Bool Label Store),
      path.posts.length ≤ gap + 3 * rows.length + 7 := by
  let allRows := rows ++ [(lastBit, lastMark)]
  have edge : TM1.step program
      (state 14 saved (List.replicate gap false ++ true :: leftRows 29 allRows) [true]) =
      some (cleanupAnchor saved gap allRows [false]) := by
    cases gap <;> simp [cleanupAnchor, List.replicate_succ, TM1.step, TM1.stepAux, program,
      PDROC.BitVM.Common.IO.Bootstrap.program, state, Tape.mk₂]
  obtain ⟨⟨middlePosts, middleChain, middleLast⟩, middleBound⟩ := cleanupAnchor_path saved gap allRows [false]
  have middleCount : middlePosts.length ≤ gap + 1 := middleBound
  let middle : ActualPath (TM1.step program) (cleanupAnchor saved gap allRows [false])
      (cleanupScan saved allRows (true :: List.replicate (gap + 1) false)) :=
    ⟨middlePosts, middleChain, by simpa [List.replicate_add, List.append_assoc] using middleLast⟩
  obtain ⟨⟨scanPosts, scanChain, scanLast⟩, scanBound⟩ :=
    cleanupScan_path saved allRows (true :: List.replicate (gap + 1) false)
  have scanCount : scanPosts.length ≤ rows.length + 2 := by
    simpa [allRows] using scanBound
  have order : (leftRows 29 allRows).reverse = temporaryRow 29 lastBit lastMark ++ physicalRows 29 rows.reverse := by
    rw [leftRows_reverse]
    simp only [allRows, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, physicalRows_cons]
  let scan : ActualPath (TM1.step program) (cleanupScan saved allRows (true :: List.replicate (gap + 1) false))
      (state 17 saved [] (temporaryRow 29 lastBit lastMark ++ physicalRows 29 rows.reverse ++
        true :: List.replicate (gap + 1) false)) :=
    ⟨scanPosts, scanChain, by simpa only [order, List.append_assoc] using scanLast⟩
  obtain ⟨⟨cleanPosts, cleanChain, cleanLast⟩, cleanBound⟩ :=
    clean_nonempty_path saved lastBit lastMark rows.reverse (List.replicate (gap + 1) false)
  have cleanCount : cleanPosts.length ≤ 2 * rows.length + 3 := by
    simpa only [List.length_reverse] using cleanBound
  have sameTape : Tape.mk₂ []
        (cleanRow 29 true lastBit ++ cleanRows rows.reverse ++ false :: List.replicate (gap + 1) false) =
      Tape.mk₁ (encodedInit32 (rows.map Prod.fst ++ [lastBit])) := by
    have word : cleanRow 29 true lastBit ++ cleanRows rows.reverse =
        encodedInit32 (rows.map Prod.fst ++ [lastBit]) := by
      rw [encodedInit32_snoc, cleanRows_word]
    have zeros : false :: List.replicate (gap + 1) false = List.replicate (gap + 2) false := by
      exact (List.replicate_succ (n := gap + 1) (a := false)).symm
    calc
      Tape.mk₂ [] (cleanRow 29 true lastBit ++ cleanRows rows.reverse ++ false :: List.replicate (gap + 1) false) =
          Tape.mk₂ [] ((cleanRow 29 true lastBit ++ cleanRows rows.reverse) ++ List.replicate (gap + 2) false) := by
            rw [zeros, List.append_assoc]
      _ = Tape.mk₂ [] (encodedInit32 (rows.map Prod.fst ++ [lastBit]) ++ List.replicate (gap + 2) false) := by rw [word]
      _ = Tape.mk₁ (encodedInit32 (rows.map Prod.fst ++ [lastBit])) := by
        simpa only [Tape.mk₁] using tape_right_blanks [] (encodedInit32 (rows.map Prod.fst ++ [lastBit])) (gap + 2)
  let cleaned : ActualPath (TM1.step program)
      (state 17 saved [] (temporaryRow 29 lastBit lastMark ++ physicalRows 29 rows.reverse ++
        true :: List.replicate (gap + 1) false))
      (⟨none, saved, Tape.mk₁ (encodedInit32 (rows.map Prod.fst ++ [lastBit]))⟩ : TM1.Cfg Bool Label Store) :=
    ⟨cleanPosts, cleanChain, by simpa only [sameTape] using cleanLast⟩
  let joined := (((ActualPath.single edge).trans middle).trans scan).trans cleaned
  refine ⟨⟨joined.posts, ?_, joined.last⟩, ?_⟩
  · simpa only [allRows] using joined.chain
  · simp only [joined, ActualPath.trans_length, ActualPath.single, middle, scan, cleaned,
      List.length_cons, List.length_nil]
    omega

end PDROC.BitVM.Common.IO.Wide
