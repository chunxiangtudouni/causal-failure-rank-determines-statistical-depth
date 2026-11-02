module

public import PSTR_WordBool_RatCmp_Run_001

/-! The frozen actual subtraction return and comparison reader share the
entire physical configuration. Only static label/store maps are used. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link

open Turing PSTRWordVM RationalControllerComputation

abbrev states : Nat := RatAddSub.addSubStates
abbrev Base (C : Type*) := RatOutput.Link.Store C states
abbrev Store (C : Type*) := RatOutput.Link.Store (C × Reader.Store) states

inductive Label where
  | sub : RatOutput.Link.Label → Label
  | read : Reader.Label → Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.sub 1⟩

abbrev Stack := RatOutput.Stack
abbrev Statement (C : Type*) := TM2.Stmt RatOutput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatOutput.Alphabet Label (Store C)

variable {C : Type*}

def exchange (C : Type*) : (Base C × Reader.Store) ≃ Store C where
  toFun := fun memory=>(((memory.1.1.1,memory.2),memory.1.1.2),memory.1.2)
  invFun := fun memory=>(((memory.1.1.1,memory.1.2),memory.2),memory.1.1.2)
  left_inv := by rintro ⟨⟨⟨context,native⟩,reader⟩,flags⟩;rfl
  right_inv := by rintro ⟨⟨⟨context,flags⟩,native⟩,reader⟩;rfl

def subLabel (point : RatOutput.Link.Label) : Label := if point=10 then .read 0 else .sub point
def readLabel (point : Reader.Label) : Label := .read point
def done : Label := .read 4

def program (caller : Statement C) : Label → Statement C
  | .sub point => LabelMap.statement subLabel
      (RatOutput.Link.program RatAddSub.subSource (C:=C × Reader.Store) .halt point)
  | .read point => if point=4 then caller else LabelMap.statement readLabel
      (StoreIso.statement (exchange C) (Reader.program (C:=Base C) .halt point))

def subConfiguration (before : RatOutput.Link.State (C × Reader.Store) states) : State C :=
  LabelMap.configuration subLabel before
def readConfiguration (before : Reader.State (Base C)) : State C :=
  LabelMap.configuration readLabel (StoreIso.configuration (exchange C) before)

theorem program_sub (caller : Statement C) (point : RatOutput.Link.Label) (proper : point≠10) :
    program caller (subLabel point)=LabelMap.statement subLabel
      (RatOutput.Link.program RatAddSub.subSource (C:=C × Reader.Store) .halt point) := by
  simp only [subLabel,proper,ite_false,program]

theorem program_read (caller : Statement C) (point : Reader.Label) (proper : point≠4) :
    program caller (readLabel point)=LabelMap.statement readLabel
      (StoreIso.statement (exchange C) (Reader.program (C:=Base C) .halt point)) := by
  simp only [readLabel,program,proper,ite_false]

theorem sub_path (caller : Statement C) (trace : List (RatOutput.Link.State (C × Reader.Store) states))
    (before final : RatOutput.Link.State (C × Reader.Store) states) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatOutput.Link.program RatAddSub.subSource .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 10) :
    (trace.map subConfiguration).head?=some (subConfiguration before) ∧
    (trace.map subConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map subConfiguration).getLast?=some (subConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (RatOutput.Link.program RatAddSub.subSource .halt) 10 rfl
    trace final chain last active
  have mapped:=LabelMap.actual_path_on subLabel (RatOutput.Link.program RatAddSub.subSource .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_sub caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem read_path (caller : Statement C) (trace : List (Reader.State (Base C)))
    (before final : Reader.State (Base C)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (Reader.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 4) :
    (trace.map readConfiguration).head?=some (readConfiguration before) ∧
    (trace.map readConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map readConfiguration).getLast?=some (readConfiguration final) := by
  let isoProgram:=StoreIso.machine (exchange C) (Reader.program .halt)
  have iso:=StoreIso.actual_path_on (exchange C) (Reader.program .halt) isoProgram trace before final
    first chain last (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 4 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on readLabel isoProgram (program caller) _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
    intro current member point selected
    exact program_read caller point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (exchange C))).map (LabelMap.configuration readLabel)=
      trace.map readConfiguration := by rw [List.map_map];rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem cells_self (contents : Stack → List Bool) : Reader.cells contents (contents 15) (contents 3)=contents := by
  funext slot
  dsimp only [Reader.cells]
  split_ifs with source target
  · rw [source]
  · rw [target]
  · rfl

theorem shared_configuration (before : RatOutput.Link.State (C × Reader.Store) states) (active : before.l=some 10) :
    readConfiguration (Reader.state before.stk 0 ((exchange C).symm before.var).1
      ((exchange C).symm before.var).2 (before.stk 15) (before.stk 3))=subConfiguration before := by
  cases before with
  | mk position memory contents =>
    change position=some 10 at active
    subst position
    change (⟨some (.read 0),(exchange C) ((exchange C).symm memory),Reader.cells contents (contents 15) (contents 3)⟩:State C)=_
    rw [Equiv.apply_symm_apply,cells_self]
    rfl

def entry (context : C) (flags : Reader.Store) (readerMemory : RatOutput.Store)
    (nativeMemory : BoolOnStacks.Store states) (background : Stack → List Bool) (x y : Rat) : State C :=
  subConfiguration (RatOutput.Link.nativeConfiguration
    (IsolatedRat.entry ((context,flags),readerMemory) nativeMemory background (encode [.rational x,.rational y])))

def rawBound (x y : Rat) : Nat := RatAddSub.addSubCoefficient*((encode [.rational x,.rational y]).length+1)^4
def baseBudget (background : Stack → List Bool) (x y : Rat) : Nat := IsolatedRat.outside background+rawBound x y

end PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link
