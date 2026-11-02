module

public import Common.PSTR_WordBool_RatInputCollect_085

/-! One fixed real encoder: actual packet copy/restore, two paid buffer
reversals reused from076, and two actual046 arbitrary-bit-list formatters.
No BitVec width or structuralWord truncation occurs. All roles are static. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation

inductive Label where
  | collect : RatInput.Label → Label
  | reverseNum : Label
  | reverseDen : Label
  | den : WordNatIO.Label → Label
  | num : WordNatIO.Label → Label
  | finish : Label
  | done : Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.collect 0⟩

abbrev Store (C : Type*) := (C × RatInput.Store) × WordNatIO.Store
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def exchange (C : Type*) : ((C × WordNatIO.Store) × RatInput.Store) ≃ Store C :=
  StoreIso.exchange C WordNatIO.Store RatInput.Store

def collectLabel (point : RatInput.Label) : Label := if point=4 then .reverseNum else .collect point
def reverseNumLabel (point : RatOutput.Label) : Label := if point=7 then .reverseNum else .reverseDen
def reverseDenLabel (point : RatOutput.Label) : Label := if point=7 then .reverseDen else .den 0
def denLabel (point : WordNatIO.Label) : Label := if point=6 then .num 0 else .den point
def numLabel (point : WordNatIO.Label) : Label := if point=6 then .finish else .num point

def reverseRoles (second : Bool) : RatInput.Stack ≃ RatInput.Stack :=
  (Equiv.swap 14 (if second then 4 else 3)).trans (Equiv.swap 15 (if second then 6 else 5))

def formatRoles (second : Bool) : RatInput.Stack ≃ RatInput.Stack :=
  ((Equiv.swap 0 13).trans (Equiv.swap 1 14)).trans (Equiv.swap 3 (if second then 6 else 5))

/-- Fixed ORIGINAL count2 and rational1 bytes, chosen before any data. -/
def prefixBits : List Bool := encodeNat 2 ++ encodeDatum (.rational 1)

def putPrefix : List Bool → Statement C → Statement C
  | [],next => next
  | bit::later,next => putPrefix later (.push 13 (fun _=>bit) next)

def finishBody : Statement C :=
  .push 13 (fun memory=>PSTRSymbolicNaturalExport.positive memory.1)
    (.push 13 (fun _=>true) (putPrefix prefixBits (.goto (fun _=>.done))))

def program (caller : Statement C) : Label → Statement C
  | .collect point => LabelMap.statement collectLabel (StoreIso.statement (exchange C)
      (RatInput.program (C:=C × WordNatIO.Store) .halt point))
  | .reverseNum => LabelMap.statement reverseNumLabel (StackIso.statement (reverseRoles false)
      (RatOutput.program (C:=C × RatInput.Store) .halt 7))
  | .reverseDen => LabelMap.statement reverseDenLabel (StackIso.statement (reverseRoles true)
      (RatOutput.program (C:=C × RatInput.Store) .halt 7))
  | .den point => LabelMap.statement denLabel (StackIso.statement (formatRoles true)
      (WordNatIO.callerProgram (C:=C × RatInput.Store) .halt point))
  | .num point => LabelMap.statement numLabel (StackIso.statement (formatRoles false)
      (WordNatIO.callerProgram (C:=C × RatInput.Store) .halt point))
  | .finish => finishBody
  | .done => caller

def collectConfiguration (before : RatInput.State (C × WordNatIO.Store)) : State C :=
  LabelMap.configuration collectLabel (StoreIso.configuration (exchange C) before)

def reverseConfiguration (second : Bool) (before : RatOutput.State (C × RatInput.Store)) : State C :=
  LabelMap.configuration (if second then reverseDenLabel else reverseNumLabel)
    (StackIso.configuration (reverseRoles second) before)

def formatConfiguration (second : Bool) (before : WordNatIO.CallerState (C × RatInput.Store)) : State C :=
  LabelMap.configuration (if second then denLabel else numLabel) (StackIso.configuration (formatRoles second) before)

theorem prefixBits_length : prefixBits.length=13 := by decide

theorem putPrefix_stepAux (bits : List Bool) (next : Statement C) (memory : Store C)
    (contents : RatInput.Stack → List Bool) :
    TM2.stepAux (putPrefix bits next) memory contents =
      TM2.stepAux next memory (Function.update contents 13 (bits++contents 13)) := by
  induction bits generalizing next with
  | nil => simp only [putPrefix,List.nil_append,Function.update_eq_self]
  | cons bit later ih =>
    rw [putPrefix,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder
