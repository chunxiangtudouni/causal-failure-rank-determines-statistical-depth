module

public import PSTR_WordBool_RatPair_API_001
public import PSTR_WordBool_RatCmp_API_001
public import PSTR_WordBool_RatDrop_API_007

/-! Concrete packet comparisons. Each phase builds the original two-Rat
input, executes the frozen signed comparator, records the physical result,
and really discards the two consumed packets before the next phase. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp

open Turing
open PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordBool
open PSTRWordVM

abbrev Registers (C : Type*) := C × Bool × Bool
abbrev Store (C : Type*) := RatCmp.Store (RatPair.Store (Registers C))
abbrev DropContext (C : Type*) := (RatPair.Store (Registers C) × RatCmp.Reader.Store) ×
  BoolOnStacks.Store RatCmp.states

inductive Label where
  | pair : Bool → RatPair.Label → Label
  | cmp : Bool → RatCmp.Label → Label
  | capture : Bool → Label
  | discard : Bool → RatDrop.Label → Label
  | emit | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.pair false default⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def pairIso (C : Type*) : RatPair.Store (RatCmp.Store (Registers C)) ≃ Store C where
  toFun := fun ⟨⟨⟨⟨⟨⟨r, flags⟩, native⟩, reader⟩, sx, sy⟩, rat⟩, fmt⟩ =>
    ((((((r, sx, sy), rat), fmt), flags), native), reader)
  invFun := fun ⟨⟨⟨⟨⟨⟨r, sx, sy⟩, rat⟩, fmt⟩, flags⟩, native⟩, reader⟩ =>
    (((((((r, flags), native), reader), sx, sy), rat), fmt))
  left_inv := by rintro ⟨⟨⟨⟨⟨⟨r, flags⟩, native⟩, reader⟩, sx, sy⟩, rat⟩, fmt⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨⟨⟨r, sx, sy⟩, rat⟩, fmt⟩, flags⟩, native⟩, reader⟩; rfl

def registers (memory : Store C) : Registers C := memory.1.1.1.1.1.1

def writeResult (second bit : Bool) (r : Registers C) : Registers C :=
  if second then (r.1, r.2.1, bit) else (r.1, bit, r.2.2)

def record (second : Bool) (memory : Store C) (cell : Option Bool) : Store C :=
  ((((((writeResult second (cell.getD false) (registers memory), memory.1.1.1.1.1.2),
    memory.1.1.1.1.2), memory.1.1.1.2), memory.1.1.2), memory.1.2), memory.2)

def pairLabel (second : Bool) (point : RatPair.Label) : Label :=
  if point = RatPair.done then .cmp second (.sub 1) else .pair second point

def cmpLabel (second : Bool) (point : RatCmp.Label) : Label :=
  if point = RatCmp.done then .capture second else .cmp second point

def nextLabel (second : Bool) : Label :=
  if second then .emit else .pair true (.collect 0)

def discardLabel (second : Bool) (point : RatDrop.Label) : Label :=
  if point = 9 then nextLabel second else .discard second point

def program (caller : Statement C) : Label → Statement C
  | .pair second point => LabelMap.statement (pairLabel second)
      (StoreIso.statement (pairIso C) (RatPair.program .halt point))
  | .cmp second point => LabelMap.statement (cmpLabel second) (RatCmp.program .halt point)
  | .capture second => .pop 3 (record second) (.goto (fun _ => .discard second 3))
  | .discard second point => LabelMap.statement (discardLabel second) (RatDrop.program .halt point)
  | .emit => .push 3 (fun memory => (registers memory).2.2)
      (.push 3 (fun memory => (registers memory).2.1) (.goto (fun _ => .done)))
  | .done => caller

def pairCfg (second : Bool) (before : RatPair.State (RatCmp.Store (Registers C))) : State C :=
  LabelMap.configuration (pairLabel second) (StoreIso.configuration (pairIso C) before)

def cmpCfg (second : Bool) (before : RatCmp.State (RatPair.Store (Registers C))) : State C :=
  LabelMap.configuration (cmpLabel second) before

def discardCfg (second : Bool) (before : RatDrop.State (DropContext C)) : State C :=
  LabelMap.configuration (discardLabel second) before

def entry (second : Bool) (background : RatInput.Stack → List Bool) (memory : Store C)
    (x y : Rat) (tail scratch : List Bool) : State C :=
  ⟨some (.pair second (.collect 0)), memory,
    RatPair.Link.initial background (RatPair.input x y tail) scratch⟩

theorem program_pair (caller : Statement C) (second : Bool) (point : RatPair.Label)
    (proper : point ≠ RatPair.done) :
    program caller (pairLabel second point) = LabelMap.statement (pairLabel second)
      (StoreIso.statement (pairIso C) (RatPair.program .halt point)) := by
  simp only [pairLabel, proper, ite_false, program]

theorem program_cmp (caller : Statement C) (second : Bool) (point : RatCmp.Label)
    (proper : point ≠ RatCmp.done) :
    program caller (cmpLabel second point) = LabelMap.statement (cmpLabel second)
      (RatCmp.program .halt point) := by
  simp only [cmpLabel, proper, ite_false, program]

theorem program_discard (caller : Statement C) (second : Bool) (point : RatDrop.Label)
    (proper : point ≠ 9) :
    program caller (discardLabel second point) = LabelMap.statement (discardLabel second)
      (RatDrop.program .halt point) := by
  simp only [discardLabel, proper, ite_false, program]

theorem entry_pair (second : Bool) (background : RatInput.Stack → List Bool) (memory : Store C)
    (x y : Rat) (tail scratch : List Bool) :
    let old := (pairIso C).symm memory
    pairCfg second (RatPair.entry background old.1.1.1 old.1.1.2.1 old.1.1.2.2
      old.1.2 old.2 x y tail scratch) = entry second background memory x y tail scratch := by
  dsimp only [pairCfg, RatPair.entry, RatPair.Link.entry, RatPair.Link.collectConfiguration,
    RatPair.Collector.state, LabelMap.configuration, StoreIso.configuration]
  rw [Equiv.apply_symm_apply]
  change (⟨some (pairLabel second (.collect 0)), memory, _⟩ : State C) = _
  have proper : (RatPair.Link.Label.collect 0) ≠ RatPair.done := by intro h; cases h
  simp only [pairLabel, proper, ite_false, entry, RatPair.Link.initial, RatPair.two_packet_format]

theorem pair_cmp_shared (second : Bool) (before : RatPair.State (RatCmp.Store (Registers C)))
    (x y : Rat) (active : before.l = some RatPair.done)
    (right : before.stk 13 = encode [.rational x, .rational y]) (left : before.stk 14 = []) :
    let memory := pairIso C before.var
    cmpCfg second (RatCmp.entry memory.1.1.1 memory.1.1.2 memory.2 memory.1.2 before.stk x y) =
      pairCfg second before := by
  cases before with
  | mk position memory contents =>
    change position = some RatPair.done at active
    subst position
    dsimp [cmpCfg, RatCmp.entry, RatCmp.Link.entry, RatCmp.Link.subConfiguration,
      RatOutput.Link.nativeConfiguration, IsolatedRat.entry, pairCfg,
      LabelMap.configuration, StoreIso.configuration, pairLabel, cmpLabel]
    congr 1
    funext slot
    fin_cases slot <;> first | rfl | exact right.symm | exact left.symm

theorem capture_step (caller : Statement C) (second bit : Bool) (memory : Store C)
    (contents : RatInput.Stack → List Bool) :
    TM2.step (program caller) ⟨some (.capture second), memory, Function.update contents 3 [bit]⟩ =
      some ⟨some (.discard second 3), record second memory (some bit), Function.update contents 3 []⟩ := by
  simp [program, TM2.step, TM2.stepAux]

end B23_4_RatWordPrep.SeqCmp
