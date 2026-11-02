module

public import RootB234_PrepExponent_ArithmeticStore011

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Arithmetic
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
variable {C : Type*}

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet RatBinary.Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet RatBinary.Label (Store C)

def binaryProgram {D : Type*} {states : Nat} (iso : RatBinary.Store D states ≃ Store C)
    (machine : Machine states) (point : RatBinary.Label) : Statement C :=
  StoreIso.statement iso (StackIso.statement binaryRoles (RatBinary.program machine .halt point))

def binaryConfiguration {D : Type*} {states : Nat} (iso : RatBinary.Store D states ≃ Store C)
    (before : RatBinary.State D states) : State C :=
  StoreIso.configuration iso (StackIso.configuration binaryRoles before)

theorem binary_path {D : Type*} {states : Nat} (iso : RatBinary.Store D states ≃ Store C)
    (machine : Machine states) (run : List (RatBinary.State D states))
    (before final : RatBinary.State D states)
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (RatBinary.program machine .halt) a=some b))
    (last : run.getLast?=some final) :
    (run.map (binaryConfiguration iso)).head?=some (binaryConfiguration iso before) ∧
    (run.map (binaryConfiguration iso)).IsChain (fun a b => TM2.step (binaryProgram iso machine) a=some b) ∧
    (run.map (binaryConfiguration iso)).getLast?=some (binaryConfiguration iso final) := by
  let changed : RatBinary.Label → RatBinary.Statement D states :=
    fun point => StackIso.statement binaryRoles (RatBinary.program (C:=D) machine .halt point)
  have stackChain := StackIso.chain_configuration_on binaryRoles (RatBinary.program machine .halt)
    changed run chain (by intro current member point selected;rfl)
  have stackFirst : (run.map (StackIso.configuration binaryRoles)).head?=
      some (StackIso.configuration binaryRoles before) := by rw [List.head?_map,first,Option.map_some]
  have stackLast : (run.map (StackIso.configuration binaryRoles)).getLast?=
      some (StackIso.configuration binaryRoles final) := by rw [List.getLast?_map,last,Option.map_some]
  have linked := StoreIso.actual_path_on iso changed (binaryProgram iso machine)
    _ _ _ stackFirst stackChain stackLast (by intro current member point selected;rfl)
  simp only [List.map_map,Function.comp_def] at linked
  exact ⟨linked.1,linked.2.1,linked.2.2.1⟩

def mulProgram : RatBinary.Label → Statement C := binaryProgram (mulIso C) RatMulDiv.mulSource
def subProgram : RatBinary.Label → Statement C := binaryProgram (subIso C) RatAddSub.subSource

theorem actual_mul (background : RatInput.Stack → List Bool) (context : MulContext C)
    (oldX oldY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (nativeMemory : BoolOnStacks.Store RatMulDiv.mulStates) (readerMemory : RatOutput.Store)
    (x y : Rat) (tail scratch : List Bool) :
    ∃ run final,
      RatBinary.Facts RatMulDiv.mulSource RatMulDiv.mulCoefficient (fun a b => a*b)
        background context oldX oldY memory formatter nativeMemory readerMemory x y tail scratch run final ∧
      (run.map (binaryConfiguration (mulIso C))).head?=some
        (binaryConfiguration (mulIso C) (RatBinary.entry background context oldX oldY memory formatter
          nativeMemory readerMemory x y tail scratch)) ∧
      (run.map (binaryConfiguration (mulIso C))).IsChain (fun a b => TM2.step mulProgram a=some b) ∧
      (run.map (binaryConfiguration (mulIso C))).getLast?=some (binaryConfiguration (mulIso C) final) ∧
      (binaryConfiguration (mulIso C) final).l=some .done ∧
      (binaryConfiguration (mulIso C) final).var.2.1=context.2.1 ∧
      (binaryConfiguration (mulIso C) final).stk=
        StackIso.slots binaryRoles (RatPair.Link.finalContents background (RatPair.packet (x*y) tail) scratch []) := by
  obtain ⟨run,final,facts⟩ := RatBinary.actual_binary RatMulDiv.mulSource RatMulDiv.mulCoefficient
    (fun a b => a*b) (by
      intro D caller ctx rm nm bg a b
      exact RatMulDiv.actual_mul caller ctx rm nm bg a b)
    background context oldX oldY memory formatter nativeMemory readerMemory x y tail scratch
  have path := binary_path (mulIso C) RatMulDiv.mulSource run _ _ facts.first facts.chain facts.last
  refine ⟨run,final,facts,path.1,path.2.1,path.2.2,facts.active,?_,?_⟩
  · change (mulIso C final.var).2.1=context.2.1
    rw [mul_context]
    exact congrArg (fun v : MulContext C => v.2.1) facts.context_eq
  · change StackIso.slots binaryRoles final.stk=_
    rw [facts.contents]

theorem actual_sub (background : RatInput.Stack → List Bool) (context : SubContext C)
    (oldX oldY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (nativeMemory : BoolOnStacks.Store RatAddSub.addSubStates) (readerMemory : RatOutput.Store)
    (x y : Rat) (tail scratch : List Bool) :
    ∃ run final,
      RatBinary.Facts RatAddSub.subSource RatAddSub.addSubCoefficient (fun a b => a-b)
        background context oldX oldY memory formatter nativeMemory readerMemory x y tail scratch run final ∧
      (run.map (binaryConfiguration (subIso C))).head?=some
        (binaryConfiguration (subIso C) (RatBinary.entry background context oldX oldY memory formatter
          nativeMemory readerMemory x y tail scratch)) ∧
      (run.map (binaryConfiguration (subIso C))).IsChain (fun a b => TM2.step subProgram a=some b) ∧
      (run.map (binaryConfiguration (subIso C))).getLast?=some (binaryConfiguration (subIso C) final) ∧
      (binaryConfiguration (subIso C) final).l=some .done ∧
      (binaryConfiguration (subIso C) final).var.2.1=context.2.1 ∧
      (binaryConfiguration (subIso C) final).stk=
        StackIso.slots binaryRoles (RatPair.Link.finalContents background (RatPair.packet (x-y) tail) scratch []) := by
  obtain ⟨run,final,facts⟩ := RatBinary.actual_binary RatAddSub.subSource RatAddSub.addSubCoefficient
    (fun a b => a-b) (by
      intro D caller ctx rm nm bg a b
      exact RatAddSub.actual_sub caller ctx rm nm bg a b)
    background context oldX oldY memory formatter nativeMemory readerMemory x y tail scratch
  have path := binary_path (subIso C) RatAddSub.subSource run _ _ facts.first facts.chain facts.last
  refine ⟨run,final,facts,path.1,path.2.1,path.2.2,facts.active,?_,?_⟩
  · change (subIso C final.var).2.1=context.2.1
    rw [sub_context]
    exact congrArg (fun v : SubContext C => v.2.1) facts.context_eq
  · change StackIso.slots binaryRoles final.stk=_
    rw [facts.contents]

end RootB234.PrepExponent.Arithmetic
