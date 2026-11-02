module
public import Common.PSTR_TM_Seq_005

/-! A finite physical window around an unchanged Bool TM0. The credits below
are proof indices, never machine parameters. An actual allocator/copy producer
must establish this tape before this lemma can be used by a Rat caller. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrame005

open Turing

def windowPrefix : Nat → ListBlank Bool → List Bool
  | 0, _ => []
  | n+1, tape => tape.head :: windowPrefix n tape.tail

@[simp] theorem prefix_length (n : Nat) (tape : ListBlank Bool) :
    (windowPrefix n tape).length = n := by
  induction n generalizing tape with
  | zero => rfl
  | succ n ih => simp [windowPrefix, ih]

@[simp] theorem prefix_cons (n : Nat) (symbol : Bool) (tape : ListBlank Bool) :
    windowPrefix (n+1) (tape.cons symbol) = symbol :: windowPrefix n tape := by
  simp [windowPrefix]

/-- The two outside lists start at fixed physical boundaries. All cells in
between come from the original tape, including real zero cells. -/
def frameTape (tape : Tape Bool) (left right : Nat) (archive suffix : List Bool) : Tape Bool :=
  ⟨tape.head, ListBlank.mk (windowPrefix left tape.left ++ archive),
    ListBlank.mk (windowPrefix right tape.right ++ suffix)⟩

@[simp] theorem frameTape_head (tape : Tape Bool) (left right : Nat)
    (archive suffix : List Bool) :
    (frameTape tape left right archive suffix).head = tape.head := rfl

theorem frameTape_write (tape : Tape Bool) (left right : Nat)
    (archive suffix : List Bool) (symbol : Bool) :
    (frameTape tape left right archive suffix).write symbol =
      frameTape (tape.write symbol) left right archive suffix := rfl

theorem frameTape_move_right (tape : Tape Bool) (left right : Nat)
    (archive suffix : List Bool) :
    (frameTape tape left (right+1) archive suffix).move .right =
      frameTape (tape.move .right) (left+1) right archive suffix := by
  simp [frameTape, Tape.move, windowPrefix, ListBlank.cons_mk]

theorem frameTape_move_left (tape : Tape Bool) (left right : Nat)
    (archive suffix : List Bool) :
    (frameTape tape (left+1) right archive suffix).move .left =
      frameTape (tape.move .left) left (right+1) archive suffix := by
  simp [frameTape, Tape.move, windowPrefix, ListBlank.cons_mk]

variable {states : Nat}

def frameCfg (left right : Nat) (archive suffix : List Bool)
    (state : MachineState states) : MachineState states :=
  ⟨state.q, frameTape state.Tape left right archive suffix⟩

def nextLeft (machine : Machine states) (state : MachineState states) (left : Nat) : Nat :=
  match machine state.q state.Tape.head with
  | some (_, .move .left) => left-1
  | some (_, .move .right) => left+1
  | _ => left

def nextRight (machine : Machine states) (state : MachineState states) (right : Nat) : Nat :=
  match machine state.q state.Tape.head with
  | some (_, .move .left) => right+1
  | some (_, .move .right) => right-1
  | _ => right

theorem nextLeft_lower (machine : Machine states) (state : MachineState states) (left : Nat) :
    left ≤ nextLeft machine state left + 1 := by
  unfold nextLeft
  split <;> omega

theorem nextRight_lower (machine : Machine states) (state : MachineState states) (right : Nat) :
    right ≤ nextRight machine state right + 1 := by
  unfold nextRight
  split <;> omega

theorem next_sum (machine : Machine states) (state : MachineState states) (left right : Nat)
    (hl : 0 < left) (hr : 0 < right) :
    nextLeft machine state left + nextRight machine state right = left+right := by
  unfold nextLeft nextRight
  split <;> omega

/-- Same code, same branch and actual single step; no frame oracle is added. -/
theorem step_frame (machine : Machine states) (state : MachineState states)
    (left right : Nat) (archive suffix : List Bool) (hl : 0 < left) (hr : 0 < right) :
    TM0.step machine (frameCfg left right archive suffix state) =
      (TM0.step machine state).map
        (frameCfg (nextLeft machine state left) (nextRight machine state right) archive suffix) := by
  cases state with
  | mk q tape =>
    cases hm : machine q tape.head with
    | none => simp [TM0.step, frameCfg, hm]
    | some result =>
      obtain ⟨next, statement⟩ := result
      cases statement with
      | write symbol =>
        simp [TM0.step, frameCfg, nextLeft, nextRight, hm, frameTape_write]
      | move direction =>
        cases direction with
        | left =>
          obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : left ≠ 0)
          simp [TM0.step, frameCfg, nextLeft, nextRight, hm, frameTape_move_left]
        | right =>
          obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : right ≠ 0)
          simp [TM0.step, frameCfg, nextLeft, nextRight, hm, frameTape_move_right]

@[simp] theorem displacement_frame (machine : Machine states) (state : MachineState states)
    (left right : Nat) (archive suffix : List Bool) :
    displacement machine (frameCfg left right archive suffix state) = displacement machine state := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrame005
