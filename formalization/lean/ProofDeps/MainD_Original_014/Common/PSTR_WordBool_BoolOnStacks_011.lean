module

public import Common.PSTR_WordBool_PushPopSource_001

/-! Fixed finite source code for reusing an old Bool TM0 on two work stacks.
This file supplies the actual code, finite support and initial tape map.
Whole source execution, quantitative compiler use and reusable workspace
are separate obligations; no old-machine execution is assumed for free. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.BoolOnStacks

open Turing

abbrev Store (states : Nat) := Fin (states + 1) × Bool
abbrev State (states : Nat) := TM2.Cfg PushPop.Alphabet Unit (Store states)

variable {states : Nat}

def capture (store : Store states) (value : Option Bool) : Store states :=
  (store.1, value.getD false)

def updateControl (machine : TM0.Machine Bool (Fin (states + 1)))
    (store : Store states) : Store states :=
  (((machine store.1 store.2).map Prod.fst).getD store.1, store.2)

def isWrite (machine : TM0.Machine Bool (Fin (states + 1))) (store : Store states) : Bool :=
  match machine store.1 store.2 with
  | some (_, .write _) => true
  | _ => false

def isRight (machine : TM0.Machine Bool (Fin (states + 1))) (store : Store states) : Bool :=
  match machine store.1 store.2 with
  | some (_, .move .right) => true
  | _ => false

def written (machine : TM0.Machine Bool (Fin (states + 1))) (store : Store states) : Bool :=
  match machine store.1 store.2 with
  | some (_, .write bit) => bit
  | _ => false

def program (machine : TM0.Machine Bool (Fin (states + 1))) (_ : Unit) :
    TM2.Stmt PushPop.Alphabet Unit (Store states) :=
  let again : TM2.Stmt PushPop.Alphabet Unit (Store states) := .goto (fun _ => ())
  .pop 0 capture
    (.branch (fun store => (machine store.1 store.2).isNone)
      (.push 0 Prod.snd .halt)
      (.branch (isWrite machine)
        (.push 0 (written machine) (.load (updateControl machine) again))
        (.branch (isRight machine)
          (.push 1 Prod.snd (.load (updateControl machine) again))
          (.load (updateControl machine)
            (.push 0 Prod.snd (.pop 1 capture (.push 0 Prod.snd again)))))))

def representedTape (state : State states) : Tape Bool :=
  Tape.mk' (ListBlank.mk (state.stk 1)) (ListBlank.mk (state.stk 0))

def representedState (state : State states) : TM0.Cfg Bool (Fin (states + 1)) :=
  ⟨state.var.1, representedTape state⟩

theorem initial_map (input : List Bool) :
    representedState (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := Store states) 0 input) =
      TM0.init input := rfl

theorem update_control_of_some (machine : TM0.Machine Bool (Fin (states + 1)))
    (store : Store states) (next : Fin (states + 1)) (instruction : TM0.Stmt Bool)
    (actual : machine store.1 store.2 = some (next, instruction)) :
    updateControl machine store = (next, store.2) := by
  simp [updateControl, actual]

theorem supports (machine : TM0.Machine Bool (Fin (states + 1))) :
    TM2.Supports (program machine) (Finset.univ : Finset Unit) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    simp [program, TM2.SupportsStmt]

end PaperProofs.Common.Native.PSTRWordBool.BoolOnStacks
