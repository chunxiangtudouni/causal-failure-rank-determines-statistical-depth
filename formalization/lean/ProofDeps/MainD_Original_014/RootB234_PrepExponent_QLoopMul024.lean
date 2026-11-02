module

public import RootB234_PrepExponent_QLoopPackets023

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

abbrev RawStore (C : Type*) := RatBinary.Store (Arithmetic.MulContext (PacketUnary.Store C)) RatMulDiv.mulStates
abbrev RawState (C : Type*) := RatBinary.State (Arithmetic.MulContext (PacketUnary.Store C)) RatMulDiv.mulStates

def rawMemory (memory : Store C) : RawStore C :=
  (Arithmetic.mulIso (PacketUnary.Store C)).symm ((arithmeticIso C).symm memory)

def rawBackground (background : Stack → List Bool) (cache counter : List Bool) : Stack → List Bool :=
  StackIso.slots Arithmetic.binaryRoles.symm (bank background cache counter [] [])

def rawEntry (background : Stack → List Bool) (memory : Store C) (cache counter : List Bool) (x y : Rat) : RawState C :=
  let m := rawMemory memory
  RatBinary.entry (rawBackground background cache counter) m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y [] cache

def mulCfg (before : RawState C) : State C :=
  LabelMap.configuration mulLabel (StoreIso.configuration (arithmeticIso C)
    (Arithmetic.binaryConfiguration (Arithmetic.mulIso (PacketUnary.Store C)) before))

theorem raw_entry_memory (background : Stack → List Bool) (memory : Store C)
    (cache counter : List Bool) (x y : Rat) :
    (rawEntry background memory cache counter x y).var=rawMemory memory := rfl

theorem mul_entry (background : Stack → List Bool) (memory : Store C)
    (cache counter : List Bool) (x y : Rat) :
    mulCfg (rawEntry background memory cache counter x y)=
      state (.mul default) memory (bank background cache counter (RatPair.input x y []) []) := by
  have vars : arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C)
      (rawEntry background memory cache counter x y).var)=memory := by
    rw [raw_entry_memory]
    simp only [rawMemory,Equiv.apply_symm_apply]
  unfold mulCfg LabelMap.configuration StoreIso.configuration Arithmetic.binaryConfiguration StackIso.configuration
  change (⟨some (.mul default),arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C)
    (rawEntry background memory cache counter x y).var),_⟩ : State C)=_
  rw [vars]
  congr 1
  funext slot
  fin_cases slot <;> try rfl
  change (rawEntry background memory cache counter x y).stk 15=RatPair.input x y []
  let m := rawMemory memory
  exact RatPair.entry_source (rawBackground background cache counter) ((m.1.1.1.1.1,m.1.2),m.2)
    m.1.1.1.1.2.1 m.1.1.1.1.2.2 m.1.1.1.2 m.1.1.2 x y [] cache

theorem mul_final_bank (background : Stack → List Bool) (cache counter : List Bool) (value : Rat) :
    StackIso.slots Arithmetic.binaryRoles
      (RatPair.Link.finalContents (rawBackground background cache counter) (RatPair.packet value []) cache [])=
      bank background cache counter (RatInput.Encoder.packet value []) [] := by
  funext slot
  fin_cases slot <;> rfl

theorem mul_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache counter : List Bool) (x y : Rat) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.mul default) memory (bank background cache counter (RatPair.input x y []) []))
      (state (.discardOld 0) afterMemory (bank background cache counter (RatInput.Encoder.packet (x*y) []) []))),
      rootContext afterMemory=rootContext memory ∧
      part.trace.length ≤ RatBinary.time RatMulDiv.mulCoefficient (rawBackground background cache counter) x y [] cache := by
  let m := rawMemory memory
  let oldBackground := rawBackground background cache counter
  obtain ⟨run,final,facts,first,chain,last,active,contexts,contents⟩ := Arithmetic.actual_mul
    oldBackground m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y [] cache
  let arithmeticCfg := Arithmetic.binaryConfiguration (Arithmetic.mulIso (PacketUnary.Store C))
  let arithmeticFinal := arithmeticCfg final
  have path := mul_path caller (run.map arithmeticCfg) _ arithmeticFinal first chain last active
  simp only [List.map_map,Function.comp_def] at path
  have first' : (run.map mulCfg).head?=some (mulCfg (rawEntry background memory cache counter x y)) := path.1
  rw [mul_entry] at first'
  let afterMemory := arithmeticIso C arithmeticFinal.var
  have finalSlots : arithmeticFinal.stk=bank background cache counter (RatInput.Encoder.packet (x*y) []) [] :=
    contents.trans (mul_final_bank background cache counter (x*y))
  have lastState : mulCfg final=state (.discardOld 0) afterMemory
      (bank background cache counter (RatInput.Encoder.packet (x*y) []) []) := by
    change (⟨arithmeticFinal.l.map mulLabel,afterMemory,arithmeticFinal.stk⟩ : State C)=_
    rw [active,finalSlots]
    rfl
  have oldContext : m.1.1.1.1.1.2.1=((arithmeticIso C).symm memory).2.1 := by
    rw [←Arithmetic.mul_context (PacketUnary.Store C) m]
    dsimp only [m,rawMemory]
    rw [Equiv.apply_symm_apply]
  refine ⟨afterMemory,⟨run.map mulCfg,first',path.2.1,path.2.2.trans (congrArg some lastState)⟩,?_,?_⟩
  · change arithmeticFinal.var.2.1.1.1=rootContext memory
    exact congrArg (fun value : PacketUnary.Store C => value.1.1) (contexts.trans oldContext)
  · simpa only [List.length_map] using facts.count

end RootB234.PrepExponent.QLoop
