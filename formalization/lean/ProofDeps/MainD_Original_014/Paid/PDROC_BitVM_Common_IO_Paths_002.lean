module

public import Paid.PDROC_BitVM_Common_IO_Emit_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.BitVM.Common.IO

open Turing PaperProofs.Common.Native.PSTRWordBool

/-- A genuine selected path with no duplicated boundary state. Its list
is proof data, never a machine store, input, transition oracle or fuel. -/
structure ActualPath {State : Type*} (step : State → Option State) (before after : State) where
  posts : List State
  chain : (before :: posts).IsChain (fun x y => step x = some y)
  last : (before :: posts).getLast? = some after

namespace ActualPath

variable {State : Type*} {step : State → Option State} {before middle after : State}

def refl (state : State) : ActualPath step state state :=
  ⟨[], List.isChain_singleton _, rfl⟩

def single (edge : step before = some after) : ActualPath step before after :=
  ⟨[after], List.isChain_cons_cons.mpr ⟨edge, List.isChain_singleton _⟩, rfl⟩

def trans (first : ActualPath step before middle) (second : ActualPath step middle after) :
    ActualPath step before after :=
  ⟨first.posts ++ second.posts,
    NativeTrace.join_chain _ _ _ first.last first.chain second.chain,
    (NativeTrace.join_last _ _ _ first.last).trans second.last⟩

theorem trans_length (first : ActualPath step before middle) (second : ActualPath step middle after) :
    (first.trans second).posts.length = first.posts.length + second.posts.length := by
  exact List.length_append

end ActualPath

abbrev EmitPath (marked : Bool) := ActualPath (TM1.step (emitProgram marked))

/-- Nearest output cells first: chronological consumed bits give this
left-facing list, and therefore the physical output is in reverse order. -/
def leftRows (rows : List (Bool × Bool)) : List Bool :=
  rows.flatMap (fun row => (temporaryRow row.1 row.2).reverse)

def physicalRows (rows : List (Bool × Bool)) : List Bool :=
  rows.flatMap (fun row => temporaryRow row.1 row.2)

def rowScan (saved : Bool) (rows : List (Bool × Bool)) (right : List Bool) : EmitState :=
  emitState (some 2) saved (leftRows rows).tail ((leftRows rows).headI :: right)

theorem rowScan_skip (marked saved bit oldMark : Bool) (rows : List (Bool × Bool))
    (right : List Bool) :
    TM1.step (emitProgram marked) (rowScan saved ((bit, oldMark) :: rows) right) =
      some (rowScan saved rows (temporaryRow bit oldMark ++ right)) := by
  cases rows with
  | nil => simpa [rowScan, leftRows, temporaryRow] using emit_skip_last_row marked saved bit oldMark right
  | cons row rows =>
    obtain ⟨nextBit, nextMark⟩ := row
    simpa [rowScan, leftRows, temporaryRow] using
      emit_skip_row marked saved bit oldMark true
        ([true, false, nextMark, nextBit, true, false] ++ leftRows rows) right

/-- Every old row is scanned by seven real moves; the new row is then
written in real blank cells. The whole right suffix is unchanged. -/
theorem scan_write_path (marked bit : Bool) (rows : List (Bool × Bool)) (right : List Bool) :
    ∃ path : EmitPath marked (rowScan bit rows right)
      (emitState (some 3) bit []
        (temporaryRow bit marked ++ (leftRows rows).reverse ++ right)),
      path.posts.length ≤ rows.length + 1 := by
  induction rows generalizing right with
  | nil =>
    refine ⟨ActualPath.single (emit_write_row marked bit right), ?_⟩
    exact Nat.le_refl _
  | cons row rows ih =>
    obtain ⟨oldBit, oldMark⟩ := row
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih (temporaryRow oldBit oldMark ++ right)
    have lengthBound : posts.length ≤ rows.length + 1 := bound
    let later' : EmitPath marked
        (rowScan bit rows (temporaryRow oldBit oldMark ++ right))
        (emitState (some 3) bit []
          (temporaryRow bit marked ++ (leftRows ((oldBit, oldMark) :: rows)).reverse ++ right)) :=
      ⟨posts, chain, by simpa [leftRows, List.reverse_append, List.append_assoc] using last⟩
    refine ⟨(ActualPath.single (rowScan_skip marked bit oldBit oldMark rows right)).trans later', ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later', List.length_cons, List.length_nil]
    omega

/-- Forward seven-cell scans really return to the TRUE anchor. -/
theorem return_rows_path (marked saved : Bool) (rows : List (Bool × Bool)) (left right : List Bool) :
    ∃ path : EmitPath marked
      (emitState (some 3) saved left (physicalRows rows ++ true :: right))
      (emitState (some 4) saved (true :: ((physicalRows rows).reverse ++ left)) right),
      path.posts.length ≤ rows.length + 1 := by
  induction rows generalizing left with
  | nil =>
    refine ⟨ActualPath.single (emit_return_anchor marked saved left right), ?_⟩
    exact Nat.le_refl _
  | cons row rows ih =>
    obtain ⟨bit, oldMark⟩ := row
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih ((temporaryRow bit oldMark).reverse ++ left)
    have lengthBound : posts.length ≤ rows.length + 1 := bound
    let later' : EmitPath marked
        (emitState (some 3) saved ((temporaryRow bit oldMark).reverse ++ left)
          (physicalRows rows ++ true :: right))
        (emitState (some 4) saved
          (true :: ((physicalRows ((bit, oldMark) :: rows)).reverse ++ left)) right) :=
      ⟨posts, chain, by simpa [physicalRows, List.reverse_append, List.append_assoc] using last⟩
    have edge := emit_return_row marked saved bit oldMark left (physicalRows rows ++ true :: right)
    refine ⟨(ActualPath.single edge).trans later', ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later', List.length_cons, List.length_nil]
    omega

end PDROC.BitVM.Common.IO
