module

public import PSTR_WordBool_RatPair_Serialize_Suffix_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def phaseBank (isX : Bool) (contents : RatInput.Stack → List Bool)
    (numRev denRev numerator denominator raw left counter : List Bool) : RatInput.Stack → List Bool :=
  StackIso.slots (roles isX)
    (RatInput.Encoder.bank (StackIso.slots (roles isX).symm contents)
      (contents 15) (contents 7) numRev denRev numerator denominator raw left counter)

theorem phase_configuration (isX : Bool) (contents : RatInput.Stack → List Bool)
    (point : RatInput.Encoder.Label) (memory : Store C)
    (numRev denRev numerator denominator raw left counter : List Bool) :
    phaseConfiguration isX
        ⟨some point,memory,RatInput.Encoder.bank (StackIso.slots (roles isX).symm contents)
          (contents 15) (contents 7) numRev denRev numerator denominator raw left counter⟩ =
      (⟨some (phaseLabel isX point),memory,
        phaseBank isX contents numRev denRev numerator denominator raw left counter⟩ : State C) := rfl

theorem phaseBank_bank (isX : Bool) (background : RatInput.Stack → List Bool)
    (xNum xDen yNum yDen oldNum oldDen oldRaw oldLeft oldCounter : List Bool)
    (numRev denRev numerator denominator raw left counter : List Bool) :
    phaseBank isX (bank background xNum xDen yNum yDen oldNum oldDen oldRaw oldLeft oldCounter)
        numRev denRev numerator denominator raw left counter =
      bank background (if isX then numRev else xNum) (if isX then denRev else xDen)
        (if isX then yNum else numRev) (if isX then yDen else denRev)
        numerator denominator raw left counter := by
  cases isX <;> funext slot <;> fin_cases slot <;> rfl

theorem actual_phase (caller : Statement C) (isX : Bool) (contents : RatInput.Stack → List Bool)
    (context : C × Bool × Bool) (bit flag negative : Bool) (formatter : WordNatIO.Store)
    (num den raw : List Bool) :
    ∃ trace : List (State C),
      trace.head? = some ⟨some (.phase isX .reverseNum),((context,(bit,flag,negative)),formatter),
        phaseBank isX contents num.reverse den.reverse [] [] raw [] []⟩ ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some ⟨some (.trim isX),((context,(bit,flag,negative)),(false,false)),
        phaseBank isX contents [] [] [] []
          (RatInput.Encoder.prefixBits ++ true :: negative ::
            (encodeNat (PSTRTMIncrement009.valueDigits num) ++
              encodeNat (PSTRTMIncrement009.valueDigits den) ++ raw)) [] []⟩ ∧
      trace.length ≤ 5*(num.length+den.length)+24 := by
  obtain ⟨trace,first,chain,last,count⟩ := old_suffix
    (StackIso.slots (roles isX).symm contents) context bit flag negative formatter
    num den (contents 15) (contents 7) raw
  have path := phase_path caller isX trace _ _ first chain last rfl
  refine ⟨trace.map (phaseConfiguration isX),?_,path.2.1,?_,?_⟩
  · rw [path.1,phase_configuration]
    rfl
  · rw [path.2.2,phase_configuration]
    rfl
  · simpa only [List.length_map] using count

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer
