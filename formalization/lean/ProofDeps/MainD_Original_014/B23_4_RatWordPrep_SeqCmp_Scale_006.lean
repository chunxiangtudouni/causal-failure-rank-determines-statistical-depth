module

public import B23_4_RatWordPrep_SeqCmp_Resources_005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMRatArithmeticParse002

variable {C : Type*}

/-- Canonical finite field lengths and actual old tails; independent of
the values of the finite registers and of any enclosing computation. -/
def inputScale (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) : Nat :=
  RatPair.Link.outside background + tail.length + scratch.length +
    RatPair.fieldSize a b + RatPair.fieldSize c d + 1

def comparisonCoefficient : Nat := 1024*65537 + RatCmp.coefficient*65537^4
def timeCoefficient : Nat := 2*comparisonCoefficient+256
def spaceCoefficient : Nat := 32+32*timeCoefficient
def coefficient : Nat := 64*(spaceCoefficient+64)
def degree : Nat := 4

theorem coefficient_pos : 0 < coefficient := by simp [coefficient]
theorem degree_eq_four : degree=4 := rfl

theorem inputScale_pos (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) :
    1 ≤ inputScale background a b c d tail scratch := by unfold inputScale; omega

theorem pair_length (x y : Rat) (tail : List Bool) :
    (RatPair.input x y tail).length=2*RatPair.fieldSize x y+12+tail.length := by
  rw [←RatPair.two_packet_format]
  exact RatPair.Collector.packets_length _ _ _ _ _ _ _

theorem pair_spaces (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) :
    RatPair.space background a b (RatPair.input c d tail) scratch ≤
      4096*inputScale background a b c d tail scratch ∧
    RatPair.space background c d tail scratch ≤4096*inputScale background a b c d tail scratch := by
  simp only [RatPair.space,RatPair.Link.space,pair_length]
  change RatPair.Link.outside background + (2*RatPair.fieldSize c d+12+tail.length) + scratch.length +
      258*RatPair.fieldSize a b+2572 ≤ _ ∧
    RatPair.Link.outside background+tail.length+scratch.length+258*RatPair.fieldSize c d+2572 ≤ _
  unfold inputScale
  omega

theorem linear_fourth (n : Nat) (positive : 1 ≤ n) : n ≤ n^4 := by
  have h := Nat.pow_le_pow_right positive (show 1≤4 by decide)
  simpa only [pow_one] using h

theorem comparison_cap_le (background : RatInput.Stack → List Bool) (x y : Rat) (tail scratch : List Bool)
    (n : Nat) (positive : 1≤n) (space : RatPair.space background x y tail scratch≤4096*n) :
    comparisonCap background x y tail scratch≤comparisonCoefficient*n^4 := by
  have linear : 16*RatPair.space background x y tail scratch+1≤65537*n := by omega
  have power := Nat.pow_le_pow_left linear 4
  have first := Nat.mul_le_mul_left (1024*65537) (linear_fourth n positive)
  have scaled := Nat.mul_le_mul_left 1024 linear
  have fourth := Nat.mul_le_mul_left RatCmp.coefficient power
  rw [Nat.mul_pow] at fourth
  dsimp only [comparisonCap,comparisonCoefficient]
  nlinarith only [first,scaled,fourth]

theorem twoTime_le (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) :
    twoTime background a b c d tail scratch≤timeCoefficient*(inputScale background a b c d tail scratch)^4 := by
  let n := inputScale background a b c d tail scratch
  have positive : 1≤n := inputScale_pos _ _ _ _ _ _ _
  have ps := pair_spaces background a b c d tail scratch
  have first := comparison_cap_le background a b (RatPair.input c d tail) scratch n positive ps.1
  have second := comparison_cap_le background c d tail scratch n positive ps.2
  have fourth := linear_fourth n positive
  have size : RatPair.fieldSize a b+RatPair.fieldSize c d+1≤n := by dsimp [n,inputScale]; omega
  dsimp only [twoTime,roundTime,timeCoefficient]
  change _ ≤ (2*comparisonCoefficient+256)*n^4
  nlinarith only [first,second,fourth,size,positive]

theorem twoSpace_le (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) :
    twoSpace background a b c d tail scratch≤spaceCoefficient*(inputScale background a b c d tail scratch)^4 := by
  let n := inputScale background a b c d tail scratch
  have occupied : RatInput.occupied (RatPair.Link.initial background
      (RatPair.input a b (RatPair.input c d tail)) scratch)≤32*n := by
    rw [RatPair.Link.occupied_initial,pair_length,pair_length]
    dsimp only [n,inputScale]
    omega
  have time := twoTime_le background a b c d tail scratch
  have fourth := Nat.mul_le_mul_left 32 (linear_fourth n (inputScale_pos _ _ _ _ _ _ _))
  dsimp only [twoSpace,entry,spaceCoefficient]
  change _≤(32+32*timeCoefficient)*n^4
  nlinarith only [occupied,time,fourth]

theorem unified_bounds (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) :
    let n := inputScale background a b c d tail scratch
    twoTime background a b c d tail scratch≤coefficient*n^degree ∧
    16*twoSpace background a b c d tail scratch≤coefficient*n^degree ∧
    twoSpace background a b c d tail scratch+32≤coefficient*n^degree ∧
    64*(twoSpace background a b c d tail scratch+33)≤coefficient*n^degree := by
  dsimp only
  have time := twoTime_le background a b c d tail scratch
  have space := twoSpace_le background a b c d tail scratch
  have positive := linear_fourth (inputScale background a b c d tail scratch) (inputScale_pos _ _ _ _ _ _ _)
  have one := inputScale_pos background a b c d tail scratch
  dsimp only [coefficient,degree,spaceCoefficient] at *
  constructor
  · nlinarith only [time,positive,one]
  constructor
  · nlinarith only [space,positive,one]
  constructor <;> nlinarith only [space,positive,one]

structure Facts (source : Label → Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (a b c d : Rat) (tail scratch : List Bool)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry false background memory a b (RatPair.input c d tail) scratch)
  chain : trace.IsChain (fun before after => TM2.step source before=some after)
  last : trace.getLast?=some final
  active : final.l=some .done
  context_eq : registers final.var=((registers memory).1,decide (a≤b),decide (c≤d))
  contents : final.stk=Function.update (RatPair.Link.initial background tail scratch) 3 [decide (a≤b),decide (c≤d)]
  time : trace.length≤coefficient*(inputScale background a b c d tail scratch)^degree
  boundaries : ∀ current∈trace,
    (∀ slot,(current.stk slot).length≤coefficient*(inputScale background a b c d tail scratch)^degree) ∧
    RatInput.occupied current.stk≤coefficient*(inputScale background a b c d tail scratch)^degree ∧
    ∀ slot,¬RatPair.Link.Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        (∀ slot,(node.2 slot).length≤coefficient*(inputScale background a b c d tail scratch)^degree) ∧
        ∀ slot,¬RatPair.Link.Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤coefficient*(inputScale background a b c d tail scratch)^degree

theorem actual_polynomial (background : RatInput.Stack → List Bool) (memory : Store C)
    (a b c d : Rat) (tail scratch : List Bool) :
    ∃ trace final, Facts (program .halt) background memory a b c d tail scratch trace final := by
  obtain ⟨trace,final,first,chain,last,active,regs,contents,time,boundaries,proper⟩ :=
    actual_two_bounded background memory a b c d tail scratch
  have caps := unified_bounds background a b c d tail scratch
  refine ⟨trace,final,⟨first,chain,last,active,regs,contents,time.trans caps.1,?_,?_⟩⟩
  · intro current member
    have bound := boundaries current member
    refine ⟨?_,bound.2.1.trans caps.2.1,bound.2.2⟩
    intro slot
    exact (bound.1 slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
  · intro current member
    refine ⟨(proper current member).1,?_⟩
    intro point selected
    have bound := (proper current member).2 point selected
    exact ⟨fun node present => ⟨fun slot => ((bound.1 node present).1 slot).trans caps.2.2.1,
      (bound.1 node present).2⟩,bound.2.trans caps.2.2.2⟩

end B23_4_RatWordPrep.SeqCmp
