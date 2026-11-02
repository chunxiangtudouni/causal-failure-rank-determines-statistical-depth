module

public import PSTR_WordBool_RatPair_API_001
public import PSTR_WordBool_RatMulDiv_Callees_001
public import PSTR_WordBool_RatAddSub_Callees_001
public import PSTR_WordBool_RatDrop_API_007

/-! Fixed binary instruction: actual pair producer, actual original Raw
callee and paid output reader, then real old-operand disposal. The Raw
machine is a source parameter, fixed before every operand quantifier. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatBinary

open Turing PSTRWordVM RationalControllerComputation

inductive Label where
  | pair : RatPair.Label→Label
  | arith : RatOutput.Link.Label→Label
  | drop : RatDrop.Label→Label
  | done : Label
  deriving DecidableEq,Fintype

instance : Inhabited Label:=⟨.pair default⟩

abbrev Store (C : Type*) (states : Nat):=RatOutput.Link.Store (RatPair.Store C) states
abbrev Statement (C : Type*) (states : Nat):=TM2.Stmt RatInput.Alphabet Label (Store C states)
abbrev State (C : Type*) (states : Nat):=TM2.Cfg RatInput.Alphabet Label (Store C states)

variable {C : Type*} {states : Nat}

def pairStoreMap (C : Type*) (states : Nat) :
    RatPair.Store ((C×BoolOnStacks.Store states)×RatOutput.Store)≃Store C states where
  toFun v:=(((((v.1.1.1.1.1,v.1.1.2),v.1.2),v.2),v.1.1.1.1.2),v.1.1.1.2)
  invFun v:=(((((v.1.1.1.1.1,v.1.2),v.2),v.1.1.1.1.2),v.1.1.1.2),v.1.1.2)
  left_inv _:=rfl
  right_inv _:=rfl

def pairLabel (point : RatPair.Label) : Label:=if point=RatPair.done then .arith 1 else .pair point
def arithLabel (point : RatOutput.Link.Label) : Label:=if point=10 then .drop 0 else .arith point
def dropLabel (point : RatDrop.Label) : Label:=if point=10 then .done else .drop point

def program (machine : Machine states) (caller : Statement C states) : Label→Statement C states
  | .pair point=>LabelMap.statement pairLabel (StoreIso.statement (pairStoreMap C states)
      (RatPair.program (C:=(C×BoolOnStacks.Store states)×RatOutput.Store) .halt point))
  | .arith point=>LabelMap.statement arithLabel (RatOutput.Link.program machine .halt point)
  | .drop point=>LabelMap.statement dropLabel (RatDrop.program .halt point)
  | .done=>caller

def pairConfiguration (before : RatPair.State ((C×BoolOnStacks.Store states)×RatOutput.Store)) : State C states:=
  LabelMap.configuration pairLabel (StoreIso.configuration (pairStoreMap C states) before)

def arithConfiguration (before : RatOutput.Link.State (RatPair.Store C) states) : State C states:=
  LabelMap.configuration arithLabel before

def dropConfiguration (before : RatDrop.State (RatPair.Store C×BoolOnStacks.Store states)) : State C states:=
  LabelMap.configuration dropLabel before

def entry (background : RatInput.Stack→List Bool) (context : C) (oldX oldY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (nativeMemory : BoolOnStacks.Store states)
    (readerMemory : RatOutput.Store) (x y : Rat) (tail scratch : List Bool) : State C states:=
  pairConfiguration (RatPair.entry background ((context,nativeMemory),readerMemory) oldX oldY memory formatter x y tail scratch)

theorem program_pair (machine : Machine states) (caller : Statement C states) (point : RatPair.Label)
    (proper : point≠RatPair.done) :
    program machine caller (pairLabel point)=LabelMap.statement pairLabel (StoreIso.statement (pairStoreMap C states)
      (RatPair.program (C:=(C×BoolOnStacks.Store states)×RatOutput.Store) .halt point)) := by
  simp only [pairLabel,proper,ite_false,program]

theorem program_arith (machine : Machine states) (caller : Statement C states) (point : RatOutput.Link.Label)
    (proper : point≠10) :
    program machine caller (arithLabel point)=LabelMap.statement arithLabel (RatOutput.Link.program machine .halt point) := by
  simp only [arithLabel,proper,ite_false,program]

theorem program_drop (machine : Machine states) (caller : Statement C states) (point : RatDrop.Label)
    (proper : point≠10) :
    program machine caller (dropLabel point)=LabelMap.statement dropLabel (RatDrop.program .halt point) := by
  simp only [dropLabel,proper,ite_false,program]

end PaperProofs.Common.Native.PSTRWordBool.RatBinary
