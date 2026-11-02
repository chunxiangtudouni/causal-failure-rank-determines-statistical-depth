module

public import Common.PSTR_WordVM_WordBank_021
public import Common.PSTR_WordBool_NativeTrace_006
public import Common.PSTR_WordBool_AuxWorkspace_020
public import Common.PSTR_WordBool_ScannerClock_024

/-! Actual AND/OR backend for the packed Word ISA. The operation is a fixed
code choice before inputs. Runtime width is the real TRUE tally11, operands
are the real equal-width lists3/4. The program consumes those operands,
reverses its actual output7 into3, restores11 and empties7/12. No Word value,
width or heap bound occurs in labels or control store. Caller3 is unexecuted. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.Bitwise

open Turing

abbrev Stack := Fin 16
abbrev Label := Fin 4
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Bool × Bool
abbrev Statement := TM2.Stmt Alphabet Label Store
abbrev State := TM2.Cfg Alphabet Label Store

def combine (isOr a b : Bool) : Bool := if isOr then a || b else a && b

def capture (_memory : Store) (value : Option Bool) : Store := (value.isSome, value.getD false)

def program (isOr : Bool) (caller : Statement) (point : Label) : Statement :=
  if point = 0 then
    .pop 11 capture (.branch Prod.fst
      (.pop 3 (fun memory value => (value.getD false, memory.2))
        (.pop 4 (fun memory value => (memory.1, value.getD false))
          (.push 7 (fun memory => combine isOr memory.1 memory.2)
            (.push 12 (fun _ => true) (.goto (fun _ => 0))))))
      (.load (fun _ => (false, false)) (.goto (fun _ => 1))))
  else if point = 1 then
    .pop 7 capture (.branch Prod.fst
      (.push 3 Prod.snd (.goto (fun _ => 1))) (.goto (fun _ => 2)))
  else if point = 2 then
    .pop 12 capture (.branch Prod.fst
      (.push 11 (fun _ => true) (.goto (fun _ => 2))) (.goto (fun _ => 3)))
  else caller

def cells (background : Stack → List Bool) (left right reversed room used : List Bool)
    (point : Stack) : List Bool :=
  if point = 3 then left else if point = 4 then right else if point = 7 then reversed else
    if point = 11 then room else if point = 12 then used else background point

def state (background : Stack → List Bool) (point : Label) (memory : Store)
    (left right reversed room used : List Bool) : State :=
  ⟨some point, memory, cells background left right reversed room used⟩

theorem step_forward (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (a b : Bool) (left right reversed room used : List Bool) :
    TM2.step (program isOr caller)
        (state background 0 memory (a :: left) (b :: right) reversed (true :: room) used) =
      some (state background 0 (a, b) left right (combine isOr a b :: reversed) room (true :: used)) := by
  change some (⟨some 0, (a, b), _⟩ : State) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_forward_end (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (reversed used : List Bool) :
    TM2.step (program isOr caller) (state background 0 memory [] [] reversed [] used) =
      some (state background 1 (false, false) [] [] reversed [] used) := by
  change some (⟨some 1, (false, false), _⟩ : State) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_reverse (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (bit : Bool) (left reversed used : List Bool) :
    TM2.step (program isOr caller) (state background 1 memory left [] (bit :: reversed) [] used) =
      some (state background 1 (true, bit) (bit :: left) [] reversed [] used) := by
  change some (⟨some 1, (true, bit), _⟩ : State) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_reverse_end (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (left used : List Bool) :
    TM2.step (program isOr caller) (state background 1 memory left [] [] [] used) =
      some (state background 2 (false, false) left [] [] [] used) := by
  change some (⟨some 2, (false, false), _⟩ : State) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_restore (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (left room used : List Bool) :
    TM2.step (program isOr caller) (state background 2 memory left [] [] room (true :: used)) =
      some (state background 2 (true, true) left [] [] (true :: room) used) := by
  change some (⟨some 2, (true, true), _⟩ : State) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_restore_end (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (left room : List Bool) :
    TM2.step (program isOr caller) (state background 2 memory left [] [] room []) =
      some (state background 3 (false, false) left [] [] room []) := by
  change some (⟨some 3, (false, false), _⟩ : State) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem program_actions (isOr : Bool) (caller : Statement) (point : Label) (proper : point ≠ 3) :
    ScannerClock.actions (program isOr caller point) ≤ 5 := by
  fin_cases point <;> first | exact False.elim (proper rfl) |
    norm_num [program, ScannerClock.actions]

theorem program_pushes (isOr : Bool) (caller : Statement) (point : Label) (proper : point ≠ 3) :
    AuxWorkspace.pushes (program isOr caller point) ≤ 2 := by
  fin_cases point <;> first | exact False.elim (proper rfl) |
    norm_num [program, AuxWorkspace.pushes]

theorem cells_frame (background : Stack → List Bool) (left right reversed room used : List Bool)
    (point : Stack) (notLeft : point ≠ 3) (notRight : point ≠ 4) (notReversed : point ≠ 7)
    (notRoom : point ≠ 11) (notUsed : point ≠ 12) :
    cells background left right reversed room used point = background point := by
  simp only [cells, notLeft, notRight, notReversed, notRoom, notUsed, ite_false]

end PaperProofs.Common.Native.PSTRWordBool.Bitwise
