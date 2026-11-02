module

public import PSTR_WordBool_RatMulDiv_Call_001
public import Structure.PA17_TM_RatArithmetic_MulSuffix_063c
public import Structure.PA17_TM_RatArithmetic_RatDivController_070c

/-! Two consumed, concrete original-codec callees. The finite Raw machines
and positive coefficients/degree4 are fixed before ALL rational operands.
In particular division has no nonzero/sign/room/width/fuel qualification. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatMulDiv

open Turing PSTRWordVM RationalControllerComputation

abbrev mulStates : Nat := PA17TMRatArithmeticMulController057.controllerCap
abbrev divStates : Nat := PA17TMRatArithmeticRatDivController070.controllerCap

def mulSource : Machine mulStates := PA17TMRatArithmeticMulController057.mulMachine
def divSource : Machine divStates := PA17TMRatArithmeticRatDivController070.divMachine

def mulCoefficient : Nat := PA17TMRatArithmeticMulSuffix063.mulResourceCoefficient
def divCoefficient : Nat := PA17TMRatArithmeticRatDivController070.divResourceCoefficient

theorem mulCoefficient_pos : 0 < mulCoefficient :=
  PA17TMRatArithmeticMulSuffix063.mulResourceCoefficient_pos

theorem divCoefficient_pos : 0 < divCoefficient :=
  PA17TMRatArithmeticRatDivController070.divResourceCoefficient_pos

universe u

def CalleeClaims {states : Nat} (machine : Machine states) (coefficient degree : Nat)
    (operation : Rat → Rat → Rat) : Prop :=
  ∀ (C : Type u) (caller : RatOutput.Link.Statement C states) (context : C)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : RatOutput.Stack → List Bool) (x y : Rat),
    Call machine caller context readerMemory nativeMemory background
      (encode [.rational x,.rational y]) (operation x y)
      (coefficient * ((encode [.rational x,.rational y]).length + 1)^degree)

theorem actual_mul {C : Type*} (caller : RatOutput.Link.Statement C mulStates) (context : C)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store mulStates)
    (background : RatOutput.Stack → List Bool) (x y : Rat) :
    Call mulSource caller context readerMemory nativeMemory background
      (encode [.rational x,.rational y]) (x*y)
      (mulCoefficient * ((encode [.rational x,.rational y]).length + 1)^4) := by
  obtain ⟨old,oldFinal,actual,whole,time,space⟩ :=
    PA17TMRatArithmeticMulSuffix063.original_mul_contract x y
  have oldTime : old.length ≤ mulCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := time
  have oldSpace : visitedSpace mulSource (encode [.rational x,.rational y]).length old ≤
      mulCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := by
    simpa only [List.take_length,mulSource,mulCoefficient,PA17TMRatArithmeticMulSuffix063.originalPower] using space old.length
  exact actual_call mulSource caller context readerMemory nativeMemory background
    (encode [.rational x,.rational y]) (x*y) _ old oldFinal actual whole oldTime oldSpace

theorem actual_div {C : Type*} (caller : RatOutput.Link.Statement C divStates) (context : C)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store divStates)
    (background : RatOutput.Stack → List Bool) (x y : Rat) :
    Call divSource caller context readerMemory nativeMemory background
      (encode [.rational x,.rational y]) (x/y)
      (divCoefficient * ((encode [.rational x,.rational y]).length + 1)^4) := by
  obtain ⟨old,oldFinal,actual,whole,time,space⟩ :=
    PA17TMRatArithmeticRatDivController070.original_div_contract x y
  have oldTime : old.length ≤ divCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := time
  have oldSpace : visitedSpace divSource (encode [.rational x,.rational y]).length old ≤
      divCoefficient * ((encode [.rational x,.rational y]).length + 1)^4 := by
    simpa only [List.take_length,divSource,divCoefficient,PA17TMRatArithmeticRatDivController070.originalPower] using space old.length
  exact actual_call divSource caller context readerMemory nativeMemory background
    (encode [.rational x,.rational y]) (x/y) _ old oldFinal actual whole oldTime oldSpace

theorem multiplication_callee_exists :
    ∃ states coefficient degree : Nat, ∃ machine : Machine states,
      0 < coefficient ∧ 0 < degree ∧ degree = 4 ∧ CalleeClaims.{u} machine coefficient degree (fun x y => x*y) := by
  refine ⟨mulStates,mulCoefficient,4,mulSource,mulCoefficient_pos,by decide,rfl,?_⟩
  intro C caller context readerMemory nativeMemory background x y
  exact actual_mul caller context readerMemory nativeMemory background x y

theorem division_callee_exists :
    ∃ states coefficient degree : Nat, ∃ machine : Machine states,
      0 < coefficient ∧ 0 < degree ∧ degree = 4 ∧ CalleeClaims.{u} machine coefficient degree (fun x y => x/y) := by
  refine ⟨divStates,divCoefficient,4,divSource,divCoefficient_pos,by decide,rfl,?_⟩
  intro C caller context readerMemory nativeMemory background x y
  exact actual_div caller context readerMemory nativeMemory background x y

theorem exact_entry_stacks {C : Type*} {states : Nat} (context : C)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : RatOutput.Stack → List Bool) (x y : Rat) :
    let before := RatOutput.Link.nativeConfiguration
      (IsolatedRat.entry (context,readerMemory) nativeMemory background (encode [.rational x,.rational y]))
    before.stk 13 = encode [.rational x,.rational y] ∧ before.stk 14 = [] ∧
      ∀ slot, slot ≠ 13 → slot ≠ 14 → before.stk slot = background slot := by
  refine ⟨rfl,rfl,?_⟩
  intro slot notR notL
  change IsolatedRat.cells background (encode [.rational x,.rational y]) [] slot = _
  simp only [IsolatedRat.cells,notR,notL,ite_false]

end PaperProofs.Common.Native.PSTRWordBool.RatMulDiv
