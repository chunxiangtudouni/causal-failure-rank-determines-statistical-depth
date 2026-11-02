module

public import Common.PSTR_WordBool_PushPopSource_001

/-! A concrete trace of the ACTUAL Mathlib TM2-to-TM1 compiler. The input
track is retained while the second stack is pushed and popped. TM1 macro
configurations are counted here; original Bool TM0 time and codecs are not
inferred from this intermediate trace. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.PushPopTM1

open Turing

abbrev Track := TM2to1.Γ' PushPop.Stack PushPop.Alphabet
abbrev Label := TM2to1.Λ' PushPop.Stack PushPop.Alphabet PushPop.Label Unit
abbrev State := TM1.Cfg Track Label Unit

def compiled : Label → TM1.Stmt Track Label Unit := TM2to1.tr PushPop.program

def pushTail : TM2.Stmt PushPop.Alphabet PushPop.Label Unit := .goto (fun _ => 1)
def popTail : TM2.Stmt PushPop.Alphabet PushPop.Label Unit := .goto (fun _ => 2)
def goPush : Label := .go 1 (.push (fun _ => true)) pushTail
def goPop : Label := .go 1 (.pop (fun _ _ => ())) popTail
def retPush : Label := .ret pushTail
def retPop : Label := .ret popTail

def cfg (label : Option Label) (tape : Tape Track) : State := ⟨label, (), tape⟩

def initialTape (input : List Bool) : Tape Track :=
  Tape.mk₁ (TM2to1.trInit (0 : PushPop.Stack) input)

def putScratch (tape : Tape Track) : Tape Track :=
  tape.write (tape.head.1, Function.update tape.head.2 1 (some true))

def clearScratch (tape : Tape Track) : Tape Track :=
  tape.write (tape.head.1, Function.update tape.head.2 1 none)

theorem initial_window (input : List Bool) :
    (initialTape input).head.1 = true ∧ (initialTape input).head.2 1 = none ∧
      ((initialTape input).move .right).head.1 = false ∧
      ((initialTape input).move .right).head.2 1 = none := by
  unfold initialTape TM2to1.trInit
  generalize input.reverse = reversed
  cases reversed with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil => exact ⟨rfl, rfl, rfl, rfl⟩
    | cons second tail => exact ⟨rfl, rfl, rfl, rfl⟩

theorem put_head (tape : Tape Track) :
    (putScratch tape).head.1 = tape.head.1 ∧ (putScratch tape).head.2 1 = some true :=
  ⟨rfl, rfl⟩

theorem put_next (tape : Tape Track) :
    ((putScratch tape).move .right).head = (tape.move .right).head := by
  cases tape
  rfl

theorem clear_put (tape : Tape Track) (empty : tape.head.2 1 = none) :
    clearScratch (putScratch tape) = tape := by
  cases tape with
  | mk row left right =>
    obtain ⟨bottom, cells⟩ := row
    change cells (1 : PushPop.Stack) = none at empty
    have sameCells : Function.update (Function.update cells 1 (some true)) 1 none = cells := by
      funext stack
      by_cases same : stack = 1
      · subst stack
        simp [empty]
      · simp [same]
    exact congrArg (fun slots => (⟨(bottom, slots), left, right⟩ : Tape Track)) sameCells

theorem normal_push (tape : Tape Track) :
    TM1.step compiled (cfg (some (.normal 0)) tape) = some (cfg (some goPush) tape) := rfl

theorem normal_pop (tape : Tape Track) :
    TM1.step compiled (cfg (some (.normal 1)) tape) = some (cfg (some goPop) tape) := rfl

theorem normal_halt (tape : Tape Track) :
    TM1.step compiled (cfg (some (.normal 2)) tape) = some (cfg none tape) := rfl

theorem go_push (tape : Tape Track) (empty : tape.head.2 1 = none) :
    TM1.step compiled (cfg (some goPush) tape) =
      some (cfg (some retPush) ((putScratch tape).move .right)) := by
  simp only [cfg, compiled, goPush, retPush, TM1.step, TM2to1.tr, TM1.stepAux,
    TM2to1.trStAct, empty, Option.isNone_none, Bool.cond_true, putScratch]

theorem ret_push (tape : Tape Track) (bottom : tape.head.1 = true) :
    TM1.step compiled (cfg (some retPush) tape) = some (cfg (some (.normal 1)) tape) := by
  simp only [cfg, compiled, retPush, pushTail, TM1.step, TM2to1.tr, TM1.stepAux,
    TM2to1.trNormal, bottom, Bool.cond_true]

theorem ret_left (tail : TM2.Stmt PushPop.Alphabet PushPop.Label Unit)
    (tape : Tape Track) (bottom : tape.head.1 = false) :
    TM1.step compiled (cfg (some (.ret tail)) tape) =
      some (cfg (some (.ret tail)) (tape.move .left)) := by
  simp only [cfg, compiled, TM1.step, TM2to1.tr, TM1.stepAux, bottom, Bool.cond_false]

theorem go_pop_scan (tape : Tape Track) (present : tape.head.2 1 = some true) :
    TM1.step compiled (cfg (some goPop) tape) =
      some (cfg (some goPop) (tape.move .right)) := by
  simp only [cfg, compiled, goPop, TM1.step, TM2to1.tr, TM1.stepAux, present,
    Option.isNone_some, Bool.cond_false]

theorem go_pop_finish (tape : Tape Track) (empty : tape.head.2 1 = none) (bottom : tape.head.1 = false) :
    TM1.step compiled (cfg (some goPop) tape) =
      some (cfg (some retPop) (clearScratch (tape.move .left))) := by
  simp only [cfg, compiled, goPop, retPop, TM1.step, TM2to1.tr, TM1.stepAux,
    TM2to1.trStAct, empty, bottom, Option.isNone_none, Bool.cond_true, Bool.cond_false, clearScratch]

theorem ret_pop (tape : Tape Track) (bottom : tape.head.1 = true) :
    TM1.step compiled (cfg (some retPop) tape) = some (cfg (some (.normal 2)) tape) := by
  simp only [cfg, compiled, retPop, popTail, TM1.step, TM2to1.tr, TM1.stepAux,
    TM2to1.trNormal, bottom, Bool.cond_true]

def trace (input : List Bool) : List State :=
  let tape := initialTape input
  let changed := putScratch tape
  [cfg (some (.normal 0)) tape, cfg (some goPush) tape,
    cfg (some retPush) (changed.move .right), cfg (some retPush) changed,
    cfg (some (.normal 1)) changed, cfg (some goPop) changed,
    cfg (some goPop) (changed.move .right), cfg (some retPop) tape,
    cfg (some (.normal 2)) tape, cfg none tape]

theorem trace_head (input : List Bool) :
    (trace input).head? = some (TM1.init (Γ := Track) (Λ := Label) (σ := Unit)
      (TM2to1.trInit (0 : PushPop.Stack) input)) := rfl

theorem trace_chain (input : List Bool) :
    (trace input).IsChain (fun before after => TM1.step compiled before = some after) := by
  have window := initial_window input
  have movedBottom : ((putScratch (initialTape input)).move .right).head.1 = false :=
    (congrArg Prod.fst (put_next (initialTape input))).trans window.2.2.1
  have movedEmpty : ((putScratch (initialTape input)).move .right).head.2 1 = none :=
    (congrArg (fun row : Track => row.2 1) (put_next (initialTape input))).trans window.2.2.2
  have putBottom : (putScratch (initialTape input)).head.1 = true := (put_head _).1.trans window.1
  have putPresent : (putScratch (initialTape input)).head.2 1 = some true := (put_head _).2
  have returning := ret_left pushTail ((putScratch (initialTape input)).move .right) movedBottom
  rw [Tape.move_right_left] at returning
  have finishing := go_pop_finish ((putScratch (initialTape input)).move .right) movedEmpty movedBottom
  rw [Tape.move_right_left, clear_put _ window.2.1] at finishing
  unfold trace
  dsimp only
  apply List.isChain_cons_cons.mpr
  refine ⟨normal_push _, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨go_push _ window.2.1, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨returning, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨ret_push _ putBottom, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨normal_pop _, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨go_pop_scan _ putPresent, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨finishing, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨ret_pop _ window.1, ?_⟩
  apply List.isChain_cons_cons.mpr
  exact ⟨normal_halt _, List.isChain_singleton _⟩

theorem trace_last (input : List Bool) : (trace input).getLast? = some (cfg none (initialTape input)) := rfl

theorem trace_length (input : List Bool) : (trace input).length = 10 := rfl

theorem final_halted (input : List Bool) : TM1.step compiled (cfg none (initialTape input)) = none := rfl

theorem supports : TM1.Supports compiled (TM2to1.trSupp PushPop.program Finset.univ) :=
  TM2to1.tr_supports PushPop.program PushPop.supports

end PaperProofs.Common.Native.PSTRWordBool.PushPopTM1
