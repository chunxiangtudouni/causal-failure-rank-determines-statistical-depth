module

public import B23_4_RatWordPrep_SeqCmp_RawNatScale_073
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawNat.Cost

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open B23_4_RatWordPrep.RawNat

variable {C : Type*}

/-- The actual TM2 source statement's scanner clock at one configuration.
An absent label has no statement to execute and is charged zero. -/
def statementClock (source : Label → Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk

/-- Sum the real source clocks on the proper trace prefix. The final boundary
configuration is not executed, so it is omitted by `dropLast`. -/
def traceClockSum (source : Label → Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock source)).sum

/-- A conservative additional charge of one per boundary configuration,
including the final boundary. This is a TM2 charge, not a TM0 cost. -/
def chargedCost (source : Label → Statement C) (trace : List (State C)) : Nat :=
  trace.length + traceClockSum source trace

def clockSumCoefficient : Nat := coefficient^2
def chargedCoefficient : Nat := coefficient^2 + coefficient
def clockSumDegree : Nat := 4

theorem clockSumCoefficient_pos : 0 < clockSumCoefficient := by
  dsimp only [clockSumCoefficient]
  exact pow_pos coefficient_pos 2

theorem chargedCoefficient_pos : 0 < chargedCoefficient := by
  have positive := coefficient_pos
  dsimp only [chargedCoefficient]
  omega

theorem clockSumDegree_eq_four : clockSumDegree = 4 := rfl

/-- Only the existing `Facts.proper` field is needed to bound each term;
there is no added clock premise. -/
theorem statementClock_le {source : Label → Statement C}
    {background : RatInput.Stack → List Bool} {memory : Store C}
    {number : Nat} {suffix : List Bool}
    {trace : List (State C)} {final parsed current : State C}
    (facts : Facts source background memory number suffix trace final parsed)
    (member : current ∈ trace.dropLast) :
    statementClock source current ≤
      coefficient * (inputScale background number)^degree := by
  cases selected : current.l with
  | none => simp only [statementClock, selected, Nat.zero_le]
  | some point =>
    simp only [statementClock, selected]
    exact ((facts.proper current member).2 point selected).2

/-- The aggregate is bounded on the very same trace carrying all original
facts. Both the number of terms and every term use the original quadratic cap. -/
theorem traceClockSum_le {source : Label → Statement C}
    {background : RatInput.Stack → List Bool} {memory : Store C}
    {number : Nat} {suffix : List Bool}
    {trace : List (State C)} {final parsed : State C}
    (facts : Facts source background memory number suffix trace final parsed) :
    traceClockSum source trace ≤
      clockSumCoefficient * (inputScale background number)^clockSumDegree := by
  let cap := coefficient * (inputScale background number)^degree
  have termwise : ∀ clock ∈ trace.dropLast.map (statementClock source), clock ≤ cap := by
    intro clock member
    obtain ⟨current, present, rfl⟩ := List.mem_map.mp member
    exact statementClock_le facts present
  have sum_bound : traceClockSum source trace ≤ trace.dropLast.length * cap := by
    simpa only [traceClockSum, List.length_map, Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock source)) cap termwise
  have length_bound : trace.dropLast.length ≤ cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum source trace ≤ trace.dropLast.length * cap := sum_bound
    _ ≤ cap * cap := Nat.mul_le_mul_right cap length_bound
    _ = clockSumCoefficient * (inputScale background number)^clockSumDegree := by
      dsimp only [cap, degree, clockSumCoefficient, clockSumDegree]
      ring

theorem chargedCost_le {source : Label → Statement C}
    {background : RatInput.Stack → List Bool} {memory : Store C}
    {number : Nat} {suffix : List Bool}
    {trace : List (State C)} {final parsed : State C}
    (facts : Facts source background memory number suffix trace final parsed) :
    chargedCost source trace ≤
      chargedCoefficient * (inputScale background number)^clockSumDegree := by
  have powers : (inputScale background number)^degree ≤
      (inputScale background number)^clockSumDegree := by
    exact Nat.pow_le_pow_right (inputScale_pos background number)
      (by decide : degree ≤ clockSumDegree)
  have length_bound := facts.time.trans (Nat.mul_le_mul_left coefficient powers)
  have sum_bound := traceClockSum_le facts
  calc
    chargedCost source trace ≤
        coefficient * (inputScale background number)^clockSumDegree +
        clockSumCoefficient * (inputScale background number)^clockSumDegree :=
      Nat.add_le_add length_bound sum_bound
    _ = chargedCoefficient * (inputScale background number)^clockSumDegree := by
      dsimp only [chargedCoefficient, clockSumCoefficient]
      ring

end B23_4_RatWordPrep.RawNat.Cost
