module

public import B23_4_RatWordPrep_SeqCmp_WordResources_013

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp.Word

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

variable {C : Type*}

def inputScale (background : RatInput.Stack → List Bool) (r low high : Rat) (tail scratch : List Bool) : Nat :=
  RatPair.Link.outside background+tail.length+scratch.length+RatPair.fieldSize r low+
    RatPair.fieldSize high r+RatPair.fieldSize 1 r+RatInput.Encoder.fieldSize r+1

def timeCoefficient : Nat := SeqCmp.timeCoefficient*32^4+SeqCmp.comparisonCoefficient+8192
def spaceCoefficient : Nat := 64+32*timeCoefficient
def coefficient : Nat := 64*(spaceCoefficient+64)
def degree : Nat := 4

theorem coefficient_pos : 0<coefficient := by simp [coefficient]
theorem degree_eq_four : degree=4 := rfl
theorem inputScale_pos (background : RatInput.Stack → List Bool) (r low high : Rat) (tail scratch : List Bool) :
    1 ≤ inputScale background r low high tail scratch := by unfold inputScale; omega

theorem packet_length (r : Rat) (tail : List Bool) :
    (RatInput.Encoder.packet r tail).length=2*RatInput.Encoder.fieldSize r+6+tail.length := by
  simp only [RatInput.Encoder.packet,PSTRSymbolicRatExport.packet,List.length_cons,List.length_append,
    RatOutput.flagged_length,RatInput.Encoder.fieldSize]
  omega

theorem output_outside (background : RatInput.Stack → List Bool) :
    RatInput.Encoder.outside (RatPair.Link.clean background)=RatPair.Link.outside background := by
  simp [RatInput.Encoder.outside,RatPair.Link.clean,RatPair.Serializer.bank,RatPair.Link.outside,
    RatPair.Link.Work,RatInput.Encoder.Work,Fin.sum_univ_succ]

theorem stage_scales (background : RatInput.Stack → List Bool) (r low high : Rat) (tail scratch : List Bool) :
    SeqCmp.inputScale background r low high r (RatPair.input 1 r (RatInput.Encoder.packet r tail)) scratch≤
      32*inputScale background r low high tail scratch ∧
    RatPair.space background 1 r (RatInput.Encoder.packet r tail) scratch≤
      4096*inputScale background r low high tail scratch ∧
    WordOutput.scale WordOutput.coefficient WordOutput.degree (RatPair.Link.clean background) r tail scratch≤
      4096*inputScale background r low high tail scratch := by
  constructor
  · unfold SeqCmp.inputScale
    rw [SeqCmp.pair_length,packet_length]
    unfold inputScale
    omega
  constructor
  · simp only [RatPair.space,RatPair.Link.space,packet_length]
    change RatPair.Link.outside background+(2*RatInput.Encoder.fieldSize r+6+tail.length)+scratch.length+
      258*RatPair.fieldSize 1 r+2572≤_
    unfold inputScale
    omega
  · simp only [WordOutput.scale,WordOutput.coefficient,WordOutput.degree,pow_one,output_outside,WordOutput.fieldSize]
    unfold inputScale
    omega

theorem time_le (background : RatInput.Stack → List Bool) (r low high : Rat) (tail scratch : List Bool) :
    time background r low high tail scratch≤timeCoefficient*(inputScale background r low high tail scratch)^4 := by
  let n := inputScale background r low high tail scratch
  have positive : 1≤n := inputScale_pos _ _ _ _ _ _
  have scales := stage_scales background r low high tail scratch
  have first := (SeqCmp.twoTime_le background r low high r (RatPair.input 1 r (RatInput.Encoder.packet r tail)) scratch).trans
    (Nat.mul_le_mul_left SeqCmp.timeCoefficient (Nat.pow_le_pow_left scales.1 4))
  rw [Nat.mul_pow] at first
  have third := SeqCmp.comparison_cap_le background 1 r (RatInput.Encoder.packet r tail) scratch n positive scales.2.1
  have output := scales.2.2
  have fourth := SeqCmp.linear_fourth n positive
  have size : RatPair.fieldSize 1 r≤n := by dsimp only [n,inputScale]; omega
  dsimp only [time,SeqCmp.roundTime,timeCoefficient]
  change _≤(SeqCmp.timeCoefficient*32^4+SeqCmp.comparisonCoefficient+8192)*n^4
  nlinarith only [first,third,output,fourth,size,positive]

theorem initial_mass (background : RatInput.Stack → List Bool) (memory : Store C)
    (r low high : Rat) (tail scratch : List Bool) :
    RatInput.occupied (entry background memory r low high tail scratch).stk≤64*inputScale background r low high tail scratch := by
  change RatInput.occupied (RatPair.Link.initial background (input r low high tail) scratch)≤_
  rw [RatPair.Link.occupied_initial]
  simp only [input,SeqCmp.pair_length,packet_length]
  unfold inputScale
  omega

theorem space_le (background : RatInput.Stack → List Bool) (r low high : Rat) (tail scratch : List Bool) :
    space background r low high tail scratch≤spaceCoefficient*(inputScale background r low high tail scratch)^4 := by
  have mass := initial_mass background (C := Unit) default r low high tail scratch
  have time := time_le background r low high tail scratch
  have fourth := Nat.mul_le_mul_left 64 (SeqCmp.linear_fourth _ (inputScale_pos background r low high tail scratch))
  dsimp only [space,spaceCoefficient]
  nlinarith only [mass,time,fourth]

theorem unified_bounds (background : RatInput.Stack → List Bool) (r low high : Rat) (tail scratch : List Bool) :
    let n := inputScale background r low high tail scratch
    time background r low high tail scratch≤coefficient*n^degree ∧
    16*space background r low high tail scratch≤coefficient*n^degree ∧
    space background r low high tail scratch+32≤coefficient*n^degree ∧
    64*(space background r low high tail scratch+33)≤coefficient*n^degree := by
  dsimp only
  have time := time_le background r low high tail scratch
  have space := space_le background r low high tail scratch
  have fourth := SeqCmp.linear_fourth _ (inputScale_pos background r low high tail scratch)
  have one := inputScale_pos background r low high tail scratch
  dsimp only [coefficient,degree,spaceCoefficient] at *
  constructor
  · nlinarith only [time,fourth,one]
  constructor
  · nlinarith only [space,fourth,one]
  constructor <;> nlinarith only [space,fourth,one]

structure Facts (source : Label → Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (r low high : Rat) (tail scratch : List Bool)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry background memory r low high tail scratch)
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  active : final.l=some .done
  context_eq : registers final.var=((registers memory).1,decide (r≤low) || decide (high≤r),decide ((1:Rat)≤r))
  contents : final.stk=RatInput.Encoder.bank (RatPair.Link.clean background) (RatInput.Encoder.packet r tail) scratch
    [] [] [] [] (encode [.rational r,boolDatum (decide (r≤low) || decide (high≤r)),boolDatum (decide ((1:Rat)≤r))]) [] []
  time : trace.length≤coefficient*(inputScale background r low high tail scratch)^degree
  boundaries : ∀ current∈trace,(∀ slot,(current.stk slot).length≤coefficient*(inputScale background r low high tail scratch)^degree) ∧
    RatInput.occupied current.stk≤coefficient*(inputScale background r low high tail scratch)^degree ∧
    ∀ slot,¬RatPair.Link.Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        (∀ slot,(node.2 slot).length≤coefficient*(inputScale background r low high tail scratch)^degree) ∧
        ∀ slot,¬RatPair.Link.Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤coefficient*(inputScale background r low high tail scratch)^degree

theorem actual_polynomial (background : RatInput.Stack → List Bool) (memory : Store C)
    (r low high : Rat) (tail scratch : List Bool) :
    ∃ trace final, Facts (program .halt) background memory r low high tail scratch trace final := by
  obtain ⟨trace,final,first,chain,last,active,regs,contents,count,boundaries,proper⟩ :=
    actual_fields_bounded background memory r low high tail scratch
  have caps := unified_bounds background r low high tail scratch
  refine ⟨trace,final,⟨first,chain,last,active,regs,contents,count.trans caps.1,?_,?_⟩⟩
  · intro current member
    have bound := boundaries current member
    exact ⟨fun slot => (bound.1 slot).trans
      ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1),bound.2.1.trans caps.2.1,bound.2.2⟩
  · intro current member
    refine ⟨(proper current member).1,?_⟩
    intro point selected
    have bound := (proper current member).2 point selected
    exact ⟨fun node present => ⟨fun slot => ((bound.1 node present).1 slot).trans caps.2.2.1,
      (bound.1 node present).2⟩,bound.2.trans caps.2.2.2⟩

end B23_4_RatWordPrep.SeqCmp.Word
