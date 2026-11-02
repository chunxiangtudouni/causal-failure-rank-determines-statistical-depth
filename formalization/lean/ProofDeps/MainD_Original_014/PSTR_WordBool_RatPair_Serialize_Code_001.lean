module

public import Common.PSTR_WordBool_RatInputAPI_093

/-! Fixed two-Rat serializer. It reuses the frozen encoder suffix twice,
including its real finish, then pays a constant13-cell prefix removal.
The two signs are Boolean memory fields, never program arguments. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer

open Turing PSTRWordVM RationalControllerComputation

inductive Label where
  | boot : Bool → Label
  | phase : Bool → RatInput.Encoder.Label → Label
  | trim : Bool → Label
  | done : Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.boot false⟩

abbrev Store (C : Type*) := RatInput.Encoder.Store (C × Bool × Bool)
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def roles (isX : Bool) : RatInput.Stack ≃ RatInput.Stack :=
  if isX then (Equiv.swap 3 8).trans (Equiv.swap 4 9) else Equiv.refl _

def phaseLabel (isX : Bool) (point : RatInput.Encoder.Label) : Label :=
  if point = .done then .trim isX else .phase isX point

def setMode (isX : Bool) (memory : Store C) : Store C :=
  ((memory.1.1,(memory.1.2.1,memory.1.2.2.1,
    if isX then memory.1.1.2.1 else memory.1.1.2.2)),memory.2)

def dropPrefix : List Bool → Statement C → Statement C
  | [],next => next
  | _::later,next => .pop 13 (fun memory _ => memory) (dropPrefix later next)

def putBits : List Bool → Statement C → Statement C
  | [],next => next
  | bit::later,next => putBits later (.push 13 (fun _ => bit) next)

def putCount : Statement C → Statement C := putBits (encodeNat 2)

def program (caller : Statement C) : Label → Statement C
  | .boot isX => .load (setMode isX) (.push 13 (fun _ => true) (.goto (fun _ => .phase isX .reverseNum)))
  | .phase isX point => LabelMap.statement (phaseLabel isX)
      (StackIso.statement (roles isX)
        (RatInput.Encoder.program (C := C × Bool × Bool) .halt point))
  | .trim false => dropPrefix RatInput.Encoder.prefixBits (.goto (fun _ => .boot true))
  | .trim true => dropPrefix RatInput.Encoder.prefixBits (putCount (.goto (fun _ => .done)))
  | .done => caller

def phaseConfiguration (isX : Bool) (before : RatInput.Encoder.State (C × Bool × Bool)) : State C :=
  LabelMap.configuration (phaseLabel isX) (StackIso.configuration (roles isX) before)

def bank (background : RatInput.Stack → List Bool)
    (xNum xDen yNum yDen numerator denominator raw left counter : List Bool) : RatInput.Stack → List Bool :=
  fun slot => if slot = 8 then xNum else if slot = 9 then xDen
    else if slot = 3 then yNum else if slot = 4 then yDen
    else if slot = 5 then numerator else if slot = 6 then denominator
    else if slot = 13 then raw else if slot = 14 then left else if slot = 12 then counter
    else background slot

def fields (negative : Bool) (numerator denominator : List Bool) : List Bool :=
  true :: negative :: (encodeNat (PSTRTMIncrement009.valueDigits numerator) ++
    encodeNat (PSTRTMIncrement009.valueDigits denominator) ++ [true])

def output (negativeX negativeY : Bool) (nx dx ny dy : List Bool) : List Bool :=
  encodeNat 2 ++ fields negativeX nx dx ++ fields negativeY ny dy

def entry (background : RatInput.Stack → List Bool) (context : C) (negativeX negativeY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (nx dx ny dy : List Bool) : State C :=
  ⟨some (.boot false),(((context,negativeX,negativeY),memory),formatter),
    bank background nx.reverse dx.reverse ny.reverse dy.reverse [] [] [] [] []⟩

theorem program_phase (caller : Statement C) (isX : Bool) (point : RatInput.Encoder.Label)
    (proper : point ≠ .done) :
    program caller (phaseLabel isX point) = LabelMap.statement (phaseLabel isX)
      (StackIso.statement (roles isX)
        (RatInput.Encoder.program (C := C × Bool × Bool) .halt point)) := by
  simp only [phaseLabel,proper,ite_false,program]

theorem bank_update_raw (background : RatInput.Stack → List Bool)
    (xNum xDen yNum yDen numerator denominator raw left counter next : List Bool) :
    Function.update (bank background xNum xDen yNum yDen numerator denominator raw left counter) 13 next =
      bank background xNum xDen yNum yDen numerator denominator next left counter := by
  funext slot
  fin_cases slot <;> rfl

theorem boot_step (caller : Statement C) (isX : Bool) (memory : Store C)
    (contents : RatInput.Stack → List Bool) :
    TM2.step (program caller) ⟨some (.boot isX),memory,contents⟩ =
      some ⟨some (.phase isX .reverseNum),setMode isX memory,
        Function.update contents 13 (true :: contents 13)⟩ := rfl

theorem dropPrefix_stepAux (bits : List Bool) (next : Statement C) (memory : Store C)
    (contents : RatInput.Stack → List Bool) (tail : List Bool) :
    TM2.stepAux (dropPrefix bits next) memory (Function.update contents 13 (bits ++ tail)) =
      TM2.stepAux next memory (Function.update contents 13 tail) := by
  induction bits with
  | nil => rfl
  | cons bit later ih =>
    simp only [dropPrefix,List.cons_append,TM2.stepAux,Function.update_self,Function.update_idem]
    exact ih

theorem putBits_stepAux (bits : List Bool) (next : Statement C) (memory : Store C)
    (contents : RatInput.Stack → List Bool) :
    TM2.stepAux (putBits bits next) memory contents =
      TM2.stepAux next memory (Function.update contents 13 (bits ++ contents 13)) := by
  induction bits generalizing next with
  | nil => simp only [putBits,List.nil_append,Function.update_eq_self]
  | cons bit later ih =>
    rw [putBits,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

theorem trim_y_step (caller : Statement C) (memory : Store C)
    (contents : RatInput.Stack → List Bool) (tail : List Bool) :
    TM2.step (program caller)
        ⟨some (.trim false),memory,Function.update contents 13 (RatInput.Encoder.prefixBits ++ tail)⟩ =
      some ⟨some (.boot true),memory,Function.update contents 13 tail⟩ := by
  change some (TM2.stepAux (dropPrefix _ _) _ _) = _
  rw [dropPrefix_stepAux]
  rfl

theorem trim_x_step (caller : Statement C) (memory : Store C)
    (contents : RatInput.Stack → List Bool) (tail : List Bool) :
    TM2.step (program caller)
        ⟨some (.trim true),memory,Function.update contents 13 (RatInput.Encoder.prefixBits ++ tail)⟩ =
      some ⟨some .done,memory,Function.update contents 13 (encodeNat 2 ++ tail)⟩ := by
  change some (TM2.stepAux (dropPrefix _ _) _ _) = _
  rw [dropPrefix_stepAux]
  rw [putCount,putBits_stepAux]
  simp only [TM2.stepAux,Function.update_self,Function.update_idem]

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer
