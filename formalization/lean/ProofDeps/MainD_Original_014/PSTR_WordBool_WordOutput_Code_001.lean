module

public import PSTR_WordBool_RatPair_Serialize_Suffix_001

/-! Fixed final word serializer. The two Bool datums are physically
pushed from readonly finite registers before the real formatter suffix.
The frozen count2/rat1 prefix is physically popped and count3 is pushed. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordOutput

open Turing PSTRWordVM RationalControllerComputation

inductive Label where
  | collect : RatInput.Encoder.Label → Label
  | prepare : Label
  | suffix : RatInput.Encoder.Label → Label
  | trim : Label
  | done : Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.collect (.collect 0)⟩

abbrev Stack := RatInput.Stack
abbrev Store (C : Type*) := RatInput.Encoder.Store (C × Bool × Bool)
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def collectLabel (point : RatInput.Encoder.Label) : Label := if point=.reverseNum then .prepare else .collect point
def suffixLabel (point : RatInput.Encoder.Label) : Label := if point=.done then .trim else .suffix point

def hitFlag (memory : Store C) : Bool := memory.1.1.2.1
def mapFlag (memory : Store C) : Bool := memory.1.1.2.2
def keep (memory : Store C) (_ : Option Bool) : Store C := memory

def putBits : List Bool → Statement C → Statement C
  | [],next=>next
  | bit::later,next=>putBits later (.push 13 (fun _=>bit) next)

def dropBits : List Bool → Statement C → Statement C
  | [],next=>next
  | _::later,next=>.pop 13 keep (dropBits later next)

def trueBits : List Bool := encodeDatum (.natural 1)
def falseBits : List Bool := encodeDatum (.natural 0)

def hitBody : Statement C := .branch hitFlag
  (putBits trueBits (.goto (fun _=>.suffix .reverseNum)))
  (putBits falseBits (.goto (fun _=>.suffix .reverseNum)))

def prepareBody : Statement C := .pop 13 keep (.push 13 (fun _=>true)
  (.branch mapFlag (putBits trueBits hitBody) (putBits falseBits hitBody)))

def trimBody : Statement C := dropBits RatInput.Encoder.prefixBits
  (putBits (encodeNat 3) (.goto (fun _=>.done)))

def program (caller : Statement C) : Label → Statement C
  | .collect point=>LabelMap.statement collectLabel (RatInput.Encoder.program (C:=C × Bool × Bool) .halt point)
  | .prepare=>prepareBody
  | .suffix point=>LabelMap.statement suffixLabel (RatInput.Encoder.program (C:=C × Bool × Bool) .halt point)
  | .trim=>trimBody
  | .done=>caller

def collectConfiguration (before : RatInput.Encoder.State (C × Bool × Bool)) : State C :=
  LabelMap.configuration collectLabel before
def suffixConfiguration (before : RatInput.Encoder.State (C × Bool × Bool)) : State C :=
  LabelMap.configuration suffixLabel before

def boolTail (hit map : Bool) : List Bool := encodeDatum (boolDatum hit)++encodeDatum (boolDatum map)++[true]

def output (negative : Bool) (num den : List Bool) (hit map : Bool) : List Bool :=
  encodeNat 3++true::negative::(encodeNat (PSTRTMIncrement009.valueDigits num)++
    encodeNat (PSTRTMIncrement009.valueDigits den)++boolTail hit map)

theorem putBits_stepAux (bits : List Bool) (next : Statement C) (memory : Store C) (contents : Stack → List Bool) :
    TM2.stepAux (putBits bits next) memory contents=
      TM2.stepAux next memory (Function.update contents 13 (bits++contents 13)) := by
  induction bits generalizing next with
  | nil=>simp only [putBits,List.nil_append,Function.update_eq_self]
  | cons bit later ih=>
    rw [putBits,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

theorem dropBits_stepAux (bits : List Bool) (next : Statement C) (memory : Store C)
    (contents : Stack → List Bool) (tail : List Bool) :
    TM2.stepAux (dropBits bits next) memory (Function.update contents 13 (bits++tail))=
      TM2.stepAux next memory (Function.update contents 13 tail) := by
  induction bits with
  | nil=>rfl
  | cons bit later ih=>
    simp only [dropBits,List.cons_append,TM2.stepAux,keep,Function.update_self,Function.update_idem]
    exact ih

theorem bank_raw (background : Stack → List Bool)
    (source scratch numRev denRev numerator denominator raw left counter : List Bool) :
    RatInput.Encoder.bank background source scratch numRev denRev numerator denominator raw left counter 13=raw := rfl

theorem prepare_step (caller : Statement C) (background : Stack → List Bool) (context : C) (hit map : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch numRev denRev : List Bool) :
    TM2.step (program caller) ⟨some .prepare,(((context,hit,map),memory),formatter),
      RatInput.Encoder.bank background source scratch numRev denRev [] [] [true] [] []⟩=
      some ⟨some (.suffix .reverseNum),(((context,hit,map),memory),formatter),
        RatInput.Encoder.bank background source scratch numRev denRev [] [] (boolTail hit map) [] []⟩ := by
  cases hit <;> cases map <;>
    simp [program,prepareBody,hitBody,TM2.step,TM2.stepAux,keep,putBits_stepAux,hitFlag,mapFlag,
      bank_raw,RatInput.Encoder.bank_update_raw,boolTail,trueBits,falseBits,boolDatum,List.append_assoc]

theorem trim_step (caller : Statement C) (memory : Store C) (contents : Stack → List Bool) (tail : List Bool) :
    TM2.step (program caller) ⟨some .trim,memory,Function.update contents 13 (RatInput.Encoder.prefixBits++tail)⟩=
      some ⟨some .done,memory,Function.update contents 13 (encodeNat 3++tail)⟩ := by
  change some (TM2.stepAux trimBody memory _)=_
  rw [trimBody,dropBits_stepAux,putBits_stepAux]
  simp only [TM2.stepAux,Function.update_self,Function.update_idem]

end PaperProofs.Common.Native.PSTRWordBool.WordOutput
