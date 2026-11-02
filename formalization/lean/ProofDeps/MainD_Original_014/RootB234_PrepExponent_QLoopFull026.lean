module

public import RootB234_PrepExponent_QLoopRun025

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

theorem bank_update7 (background : Stack → List Bool) (cache counter input trash next : List Bool) :
    Function.update (bank background cache counter input trash) 7 next=bank background next counter input trash := by
  funext slot
  fin_cases slot <;> rfl

theorem literalQ_bank_step (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache : List Bool) :
    TM2.step (program caller) (state .literalQ memory (bank background cache [] [] []))=
      some (state (.count default) memory (bank background (RatInput.Encoder.packet (12 : Rat) cache) [] [] [])) := by
  have step := literalQ_step caller memory (bank background cache [] [] [])
  rw [bank_update7] at step
  have cells : bank background cache [] [] [] 7=cache := rfl
  have packet : RatInput.Encoder.packet (12 : Rat) []++cache=RatInput.Encoder.packet (12 : Rat) cache :=
    (RatPair.packet_append 12 cache).symm
  rw [cells,packet] at step
  exact step

theorem count_bank (background : Stack → List Bool) (cache counter : List Bool) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    NCount.bank (bank background cache [] [] []) (B23_4_RatWordPrep.NatField.packet number []) [] [] counter []=
      bank background cache counter [] [] := by
  funext slot
  fin_cases slot <;> try rfl
  exact input.symm

theorem count_state (background : Stack → List Bool) (cache counter : List Bool) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) (point : NCount.Label) (memory : Store C) :
    LabelMap.configuration countLabel
      (NCount.state (bank background cache [] [] []) point memory
        (B23_4_RatWordPrep.NatField.packet number []) [] [] counter [])=
      state (countLabel point) memory (bank background cache counter [] []) := by
  unfold LabelMap.configuration NCount.state state
  rw [count_bank background cache counter number input]
  rfl

def countCost (background : Stack → List Bool) (cache : List Bool) (number : Nat) : Nat :=
  16384*(NCount.scale (bank background cache [] [] []) number)^2

theorem count_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache : List Bool) (number : Nat) (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.count default) memory (bank background cache [] [] []))
      (state .take afterMemory (bank background cache (List.replicate number true) [] []))),
      rootContext afterMemory=rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ countCost background cache number := by
  obtain ⟨converted,run,facts⟩ := NCount.actual_bounded (bank background cache [] [] [])
    memory.1.1.1 memory.1.1.2 memory.1.2 memory.2 number
  have path := count_path caller run _ _ facts.first facts.chain facts.last rfl
  let afterMemory : Store C := (converted,false,false)
  have firstState := count_state background cache [] number input default memory
  have lastState := count_state background cache (List.replicate number true) number input .done afterMemory
  refine ⟨afterMemory,⟨run.map (LabelMap.configuration countLabel),
    path.1.trans (congrArg some firstState),path.2.1,path.2.2.trans (congrArg some lastState)⟩,?_,rfl,?_⟩
  · exact congrArg Prod.snd facts.context_eq
  · simpa only [List.length_map,countCost] using facts.time

def fullCost (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) : Nat :=
  (3*RatInput.Encoder.fieldSize budget+14)+2+
    countCost background (RatInput.Encoder.packet (12 : Rat) (RatInput.Encoder.packet budget tail)) number+
    roundsCost background (RatInput.Encoder.packet budget tail) number 12

/-- Full fixed Q producer, including the actual budget archive, literal
12, physical N counter, every multiply/clear round and the final zero pop.
All untouched original fields are retained in the exact output bank. -/
theorem full_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state default memory (bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state .done afterMemory
        (bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []))),
      rootContext afterMemory=rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ fullCost background tail budget number := by
  obtain ⟨budgetPart,budgetCount⟩ := budget_actual caller background memory tail budget
  let literalPart := Segment.edge (literalQ_bank_step caller background (memory.1,false,false)
    (RatInput.Encoder.packet budget tail))
  obtain ⟨countMemory,countPart,countContext,_countFlags,countBound⟩ := count_actual caller background
    (memory.1,false,false) (RatInput.Encoder.packet (12 : Rat) (RatInput.Encoder.packet budget tail)) number input
  obtain ⟨afterMemory,roundsPart,roundsContext,roundsFlags,roundsBound⟩ := rounds_actual caller background
    countMemory (RatInput.Encoder.packet budget tail) 12 number
  let joined1 := budgetPart.append literalPart
  let joined2 := joined1.append countPart
  let whole := joined2.append roundsPart
  refine ⟨afterMemory,whole,roundsContext.trans countContext,roundsFlags,?_⟩
  have literalCount : literalPart.trace.length=2 := rfl
  have count1 : joined1.trace.length ≤ budgetPart.trace.length+literalPart.trace.length :=
    budgetPart.append_length literalPart
  have count2 : joined2.trace.length ≤ joined1.trace.length+countPart.trace.length := joined1.append_length countPart
  have count3 : whole.trace.length ≤ joined2.trace.length+roundsPart.trace.length := joined2.append_length roundsPart
  unfold fullCost
  omega

end RootB234.PrepExponent.QLoop
