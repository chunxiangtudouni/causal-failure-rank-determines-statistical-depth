module

public import Common.PSTR_WordBool_RawInit_CopyCode004

/-! Actual flag-aligned shuttle traces used by the ONE header copier.
Only its two left scans and three right scans occur here. The recursive
lists specify witnesses of real fixed-table steps, never machine inputs. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010 PSTRTMIncrement009

def leftFlag (bank saved : Bool) : Fin 42 := roundLabel saved (if bank then 6 else 3)
def leftData (bank saved : Bool) : Fin 42 := roundLabel saved (if bank then 7 else 4)

def leftStart (bank saved : Bool) (leftEnd remaining right : List Bool) : MachineState 41 :=
  match remaining with
  | [] => coreState (leftFlag bank saved) leftEnd (false :: right)
  | bit :: later => coreState (leftFlag bank saved)
      (bit :: (leftBlocks later ++ false :: leftEnd)) (true :: right)

def leftTrace (bank saved : Bool) (leftEnd : List Bool) :
    List Bool → List Bool → List (MachineState 41)
  | [], right => [coreState (leftFlag bank saved) leftEnd (false :: right)]
  | bit :: later, right =>
    [coreState (leftFlag bank saved) (bit :: (leftBlocks later ++ false :: leftEnd)) (true :: right),
     coreState (leftData bank saved) (leftBlocks later ++ false :: leftEnd) (bit :: true :: right)] ++
      leftTrace bank saved leftEnd later (bit :: true :: right)

theorem left_head (bank saved : Bool) (leftEnd remaining right : List Bool) :
    (leftTrace bank saved leftEnd remaining right).head? =
      some (leftStart bank saved leftEnd remaining right) := by
  cases remaining <;> rfl

theorem left_last (bank saved : Bool) (leftEnd remaining right : List Bool) :
    (leftTrace bank saved leftEnd remaining right).getLast? =
      some (coreState (leftFlag bank saved) leftEnd (false :: (blocks remaining.reverse ++ right))) := by
  induction remaining generalizing right with
  | nil => rfl
  | cons bit later ih =>
    have nonempty : leftTrace bank saved leftEnd later (bit :: true :: right) ≠ [] := by
      intro empty
      have first := left_head bank saved leftEnd later (bit :: true :: right)
      simp [empty] at first
    simp only [leftTrace, List.cons_append, List.nil_append, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil nonempty, ih]
    simp [blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem left_length (bank saved : Bool) (leftEnd remaining right : List Bool) :
    (leftTrace bank saved leftEnd remaining right).length = 2 * remaining.length + 1 := by
  induction remaining generalizing right with
  | nil => rfl
  | cons bit later ih =>
    simp only [leftTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem left_chain (bank saved : Bool) (leftEnd remaining right : List Bool) :
    (leftTrace bank saved leftEnd remaining right).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  induction remaining generalizing right with
  | nil => exact .singleton _
  | cons bit later ih =>
    rw [leftTrace]
    apply List.IsChain.append
    · apply List.isChain_cons_cons.mpr
      refine ⟨?_, .singleton _⟩
      cases bank <;> cases saved <;>
        simp [TM0.step, coreMachine, coreState, leftFlag, leftData, roundLabel, roundCode, Tape.mk₂]
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      simp only [left_head, Option.mem_some_iff] at afterHead
      subst before
      subst after
      cases later <;> cases bank <;> cases saved <;>
        simp [leftStart, TM0.step, coreMachine, coreState, leftFlag, leftData,
          roundLabel, roundCode, Tape.mk₂, leftBlocks]

def rightData (mode : Fin 3) (saved : Bool) : Fin 42 :=
  if mode = 0 then roundLabel saved 12 else if mode = 1 then roundLabel saved 14 else 4

def rightFlag (mode : Fin 3) (saved : Bool) : Fin 42 :=
  if mode = 0 then roundLabel saved 11 else if mode = 1 then roundLabel saved 15 else 5

def rightTrace (mode : Fin 3) (saved : Bool) (left : List Bool) :
    List Bool → Bool → List Bool → List (MachineState 41)
  | [], endBit, tail =>
    [coreState (rightData mode saved) left (endBit :: false :: tail),
     coreState (rightFlag mode saved) (endBit :: left) (false :: tail)]
  | bit :: later, endBit, tail =>
    [coreState (rightData mode saved) left (bit :: true :: (blocks later ++ endBit :: false :: tail)),
     coreState (rightFlag mode saved) (bit :: left) (true :: (blocks later ++ endBit :: false :: tail))] ++
      rightTrace mode saved (true :: bit :: left) later endBit tail

theorem right_head (mode : Fin 3) (saved endBit : Bool) (left digits tail : List Bool) :
    (rightTrace mode saved left digits endBit tail).head? =
      some (coreState (rightData mode saved) left (blocks digits ++ endBit :: false :: tail)) := by
  cases digits <;> rfl

theorem right_last (mode : Fin 3) (saved endBit : Bool) (left digits tail : List Bool) :
    (rightTrace mode saved left digits endBit tail).getLast? =
      some (coreState (rightFlag mode saved) (endBit :: (leftBlocks digits.reverse ++ left)) (false :: tail)) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have nonempty : rightTrace mode saved (true :: bit :: left) later endBit tail ≠ [] := by
      intro empty
      have first := right_head mode saved endBit (true :: bit :: left) later tail
      simp [empty] at first
    simp only [rightTrace, List.cons_append, List.nil_append, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil nonempty, ih]
    simp [leftBlocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem right_length (mode : Fin 3) (saved endBit : Bool) (left digits tail : List Bool) :
    (rightTrace mode saved left digits endBit tail).length = 2 * digits.length + 2 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [rightTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem right_chain (mode : Fin 3) (saved endBit : Bool) (left digits tail : List Bool) :
    (rightTrace mode saved left digits endBit tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  induction digits generalizing left with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, .singleton _⟩
    fin_cases mode <;> cases saved <;>
      simp [TM0.step, coreMachine, coreState, rightData, rightFlag, roundLabel, roundCode, Tape.mk₂]
  | cons bit later ih =>
    rw [rightTrace]
    apply List.IsChain.append
    · apply List.isChain_cons_cons.mpr
      refine ⟨?_, .singleton _⟩
      fin_cases mode <;> cases saved <;>
        simp [TM0.step, coreMachine, coreState, rightData, rightFlag, roundLabel, roundCode, Tape.mk₂]
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      simp only [right_head, Option.mem_some_iff] at afterHead
      subst before
      subst after
      fin_cases mode <;> cases saved <;>
        simp [TM0.step, coreMachine, coreState, rightData, rightFlag, roundLabel, roundCode, Tape.mk₂, blocks]

end PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy
