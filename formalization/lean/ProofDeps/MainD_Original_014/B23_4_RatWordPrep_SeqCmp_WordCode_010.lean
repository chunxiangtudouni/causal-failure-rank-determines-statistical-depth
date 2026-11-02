module

public import B23_4_RatWordPrep_SeqCmp_Return_009
public import PSTR_WordBool_WordOutput_API_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp.Word

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

abbrev OutputContext (C : Type*) := (((C × Bool × Bool) × RatCmp.Reader.Store) ×
  BoolOnStacks.Store RatCmp.states) × RatOutput.Store

inductive Label where
  | front : SeqCmp.Label → Label
  | orFirst | orSecond
  | mapRound : SeqCmp.Label → Label
  | serialize : WordOutput.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.front default⟩

abbrev Store (C : Type*) := SeqCmp.Store C
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def outputIso (C : Type*) : WordOutput.Store (OutputContext C) ≃ Store C where
  toFun := fun ⟨⟨⟨⟨⟨⟨⟨c,sx,sy⟩,flags⟩,native⟩,reader⟩,hit,map⟩,rat⟩,fmt⟩ =>
    (((((((c,hit,map),sx,sy),rat),fmt),flags),native),reader)
  invFun := fun ⟨⟨⟨⟨⟨⟨⟨c,hit,map⟩,sx,sy⟩,rat⟩,fmt⟩,flags⟩,native⟩,reader⟩ =>
    ((((((((c,sx,sy),flags),native),reader),hit,map),rat),fmt))
  left_inv := by rintro ⟨⟨⟨⟨⟨⟨⟨c,sx,sy⟩,flags⟩,native⟩,reader⟩,hit,map⟩,rat⟩,fmt⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨⟨⟨⟨c,hit,map⟩,sx,sy⟩,rat⟩,fmt⟩,flags⟩,native⟩,reader⟩; rfl

def frontLabel (point : SeqCmp.Label) : Label := if point=.done then .orFirst else .front point
def mapLabel (point : SeqCmp.Label) : Label :=
  if point=.emit then .serialize (.collect (.collect 0)) else .mapRound point
def outputLabel (point : WordOutput.Label) : Label := if point=.done then .done else .serialize point

def recordOr (memory : Store C) (cell : Option Bool) : Store C :=
  record false memory (some ((registers memory).2.1 || cell.getD false))

def program (caller : Statement C) : Label → Statement C
  | .front point => LabelMap.statement frontLabel (SeqCmp.program .halt point)
  | .orFirst => .pop 3 (record false) (.goto (fun _ => .orSecond))
  | .orSecond => .pop 3 recordOr (.goto (fun _ => .mapRound (.pair true (.collect 0))))
  | .mapRound point => LabelMap.statement mapLabel (SeqCmp.program .halt point)
  | .serialize point => LabelMap.statement outputLabel (StoreIso.statement (outputIso C) (WordOutput.program .halt point))
  | .done => caller

def frontCfg (before : SeqCmp.State C) : State C := LabelMap.configuration frontLabel before
def mapCfg (before : SeqCmp.State C) : State C := LabelMap.configuration mapLabel before
def outputCfg (before : WordOutput.State (OutputContext C)) : State C :=
  LabelMap.configuration outputLabel (StoreIso.configuration (outputIso C) before)

/-- These are operand packets, not precomputed comparison answers. The
last packet is the odds value retained for original output serialization. -/
def input (r low high : Rat) (tail : List Bool) : List Bool :=
  RatPair.input r low (RatPair.input high r (RatPair.input 1 r (RatInput.Encoder.packet r tail)))

def entry (background : RatInput.Stack → List Bool) (memory : Store C)
    (r low high : Rat) (tail scratch : List Bool) : State C :=
  frontCfg (SeqCmp.entry false background memory r low
    (RatPair.input high r (RatPair.input 1 r (RatInput.Encoder.packet r tail))) scratch)

theorem program_front (caller : Statement C) (point : SeqCmp.Label) (proper : point≠.done) :
    program caller (frontLabel point)=LabelMap.statement frontLabel (SeqCmp.program .halt point) := by
  simp only [frontLabel,proper,ite_false,program]

theorem program_map (caller : Statement C) (point : SeqCmp.Label) (proper : point≠.emit) :
    program caller (mapLabel point)=LabelMap.statement mapLabel (SeqCmp.program .halt point) := by
  simp only [mapLabel,proper,ite_false,program]

theorem program_output (caller : Statement C) (point : WordOutput.Label) (proper : point≠.done) :
    program caller (outputLabel point)=LabelMap.statement outputLabel
      (StoreIso.statement (outputIso C) (WordOutput.program .halt point)) := by
  simp only [outputLabel,proper,ite_false,program]

theorem first_or (caller : Statement C) (memory : Store C) (contents : RatInput.Stack → List Bool)
    (lower upper : Bool) :
    TM2.step (program caller) ⟨some .orFirst,memory,Function.update contents 3 [lower,upper]⟩=
      some ⟨some .orSecond,record false memory (some lower),Function.update contents 3 [upper]⟩ := by
  simp [program,TM2.step,TM2.stepAux]

theorem second_or (caller : Statement C) (memory : Store C) (contents : RatInput.Stack → List Bool)
    (upper : Bool) :
    TM2.step (program caller) ⟨some .orSecond,memory,Function.update contents 3 [upper]⟩=
      some ⟨some (.mapRound (.pair true (.collect 0))),recordOr memory (some upper),Function.update contents 3 []⟩ := by
  simp [program,TM2.step,TM2.stepAux]

theorem or_registers (memory : Store C) (lower upper : Bool) :
    registers (recordOr (record false memory (some lower)) (some upper))=
      ((registers memory).1,lower || upper,(registers memory).2.2) := rfl

theorem output_registers (before : Store C) (after : WordOutput.Store (OutputContext C))
    (preserved : after.1.1=((outputIso C).symm before).1.1) :
    registers (outputIso C after)=registers before := by
  have h := congrArg (fun x : OutputContext C × Bool × Bool => (x.1.1.1.1.1,x.2.1,x.2.2)) preserved
  change registers (outputIso C after)=registers (outputIso C ((outputIso C).symm before)) at h
  simpa only [Equiv.apply_symm_apply] using h

theorem output_entry_stacks (background : RatInput.Stack → List Bool) (memory : WordOutput.Store (OutputContext C))
    (r : Rat) (tail scratch : List Bool) :
    (WordOutput.entry (RatPair.Link.clean background) memory.1.1.1 memory.1.1.2.1 memory.1.1.2.2
      memory.1.2 memory.2 r tail scratch).stk=
      RatPair.Link.initial background (RatInput.Encoder.packet r tail) scratch := by
  funext slot
  fin_cases slot <;> rfl

end B23_4_RatWordPrep.SeqCmp.Word
