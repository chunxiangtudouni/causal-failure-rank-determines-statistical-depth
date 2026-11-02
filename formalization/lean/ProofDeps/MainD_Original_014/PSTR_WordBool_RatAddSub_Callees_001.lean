module

public import PSTR_WordBool_RatMulDiv_Call_001
public import Structure.PA17_TM_RatArithmetic_AddSubFull_079a

/-! Two concrete whole-codec callees consume the unchanged paid native/reader
join. Both Bool modes, machines, and positive quartic coefficient are fixed
before ALL rational operands; no mode flag or caller qualification is input. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatAddSub

open Turing PSTRWordVM RationalControllerComputation

abbrev addSubStates : Nat := PA17TMRatArithmeticAddSubController075.controllerCap

def addSource : Machine addSubStates := PA17TMRatArithmeticAddSubFull079.addMachine
def subSource : Machine addSubStates := PA17TMRatArithmeticAddSubFull079.subMachine
def addSubCoefficient : Nat := PA17TMRatArithmeticAddSubFull079.addSubResourceCoefficient

theorem addSubCoefficient_pos : 0 < addSubCoefficient :=
  PA17TMRatArithmeticAddSubFull079.addSubResourceCoefficient_pos

universe u

def CalleeClaims {states : Nat} (machine : Machine states) (coefficient degree : Nat)
    (operation : Rat → Rat → Rat) : Prop :=
  ∀ (C : Type u) (caller : RatOutput.Link.Statement C states) (context : C)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : RatOutput.Stack → List Bool) (x y : Rat),
    RatMulDiv.Call machine caller context readerMemory nativeMemory background
      (encode [.rational x,.rational y]) (operation x y)
      (coefficient * ((encode [.rational x,.rational y]).length + 1)^degree)

theorem actual_add {C : Type*} (caller : RatOutput.Link.Statement C addSubStates) (context : C)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store addSubStates)
    (background : RatOutput.Stack → List Bool) (x y : Rat) :
    RatMulDiv.Call addSource caller context readerMemory nativeMemory background
      (encode [.rational x,.rational y]) (x+y)
      (addSubCoefficient * ((encode [.rational x,.rational y]).length + 1)^4) := by
  obtain ⟨old,oldFinal,actual,whole,time,space⟩ :=
    PA17TMRatArithmeticAddSubFull079.original_add_sub_contract false x y
  have oldTime : old.length ≤ addSubCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := time
  have oldSpace : visitedSpace addSource (encode [.rational x,.rational y]).length old ≤
      addSubCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := by
    simpa only [List.take_length,addSource,PA17TMRatArithmeticAddSubFull079.addMachine,
      addSubCoefficient,PA17TMRatArithmeticAddSubController075.originalPower] using space old.length
  exact RatMulDiv.actual_call addSource caller context readerMemory nativeMemory background
    (encode [.rational x,.rational y]) (x+y) _ old oldFinal actual whole oldTime oldSpace

theorem actual_sub {C : Type*} (caller : RatOutput.Link.Statement C addSubStates) (context : C)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store addSubStates)
    (background : RatOutput.Stack → List Bool) (x y : Rat) :
    RatMulDiv.Call subSource caller context readerMemory nativeMemory background
      (encode [.rational x,.rational y]) (x-y)
      (addSubCoefficient * ((encode [.rational x,.rational y]).length + 1)^4) := by
  obtain ⟨old,oldFinal,actual,whole,time,space⟩ :=
    PA17TMRatArithmeticAddSubFull079.original_add_sub_contract true x y
  have oldTime : old.length ≤ addSubCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := time
  have oldSpace : visitedSpace subSource (encode [.rational x,.rational y]).length old ≤
      addSubCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := by
    simpa only [List.take_length,subSource,PA17TMRatArithmeticAddSubFull079.subMachine,
      addSubCoefficient,PA17TMRatArithmeticAddSubController075.originalPower] using space old.length
  exact RatMulDiv.actual_call subSource caller context readerMemory nativeMemory background
    (encode [.rational x,.rational y]) (x-y) _ old oldFinal actual whole oldTime oldSpace

theorem addition_callee_exists :
    ∃ states coefficient degree : Nat, ∃ machine : Machine states,
      0 < coefficient ∧ 0 < degree ∧ degree = 4 ∧ CalleeClaims.{u} machine coefficient degree (fun x y => x+y) := by
  refine ⟨addSubStates,addSubCoefficient,4,addSource,addSubCoefficient_pos,by decide,rfl,?_⟩
  intro C caller context readerMemory nativeMemory background x y
  exact actual_add caller context readerMemory nativeMemory background x y

theorem subtraction_callee_exists :
    ∃ states coefficient degree : Nat, ∃ machine : Machine states,
      0 < coefficient ∧ 0 < degree ∧ degree = 4 ∧ CalleeClaims.{u} machine coefficient degree (fun x y => x-y) := by
  refine ⟨addSubStates,addSubCoefficient,4,subSource,addSubCoefficient_pos,by decide,rfl,?_⟩
  intro C caller context readerMemory nativeMemory background x y
  exact actual_sub caller context readerMemory nativeMemory background x y

end PaperProofs.Common.Native.PSTRWordBool.RatAddSub
