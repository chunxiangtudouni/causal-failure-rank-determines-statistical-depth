module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeScale_036

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalFee.Cost

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

variable {C : Type*}

def statementClock (source : Label → Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk
def traceClockSum (source : Label → Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock source)).sum
def chargedCost (source : Label → Statement C) (trace : List (State C)) : Nat :=
  trace.length+traceClockSum source trace
def chargedCoefficient : Nat := coefficient^2+coefficient

theorem chargedCoefficient_pos : 0<chargedCoefficient := by
  have positive := coefficient_pos
  dsimp only [chargedCoefficient]
  omega

variable {source : Label → Statement C} {memory : RawGetter.Store C}
  {native : RatInput.Complement.CalleeFlags} {reader : RatInput.Complement.Reader}
  {E : BinaryExperiment} {target : Rat} {word : E.StoppedWord}
  {trace : List (State C)} {final beforeRead : State C}

theorem traceClockSum_le (facts : Facts source memory native reader E target word trace final beforeRead) :
    traceClockSum source trace≤coefficient^2*((wordInput E target word).length+1)^32 := by
  let cap := coefficient*((wordInput E target word).length+1)^degree
  have termwise : ∀ value∈trace.dropLast.map (statementClock source),value≤cap := by
    intro value member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : traceClockSum source trace≤trace.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock source)) cap termwise
  have length : trace.dropLast.length≤cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum source trace ≤ cap*cap := sum.trans (Nat.mul_le_mul_right cap length)
    _ = coefficient^2*((wordInput E target word).length+1)^32 := by dsimp only [cap,degree]; ring

theorem chargedCost_le (facts : Facts source memory native reader E target word trace final beforeRead) :
    chargedCost source trace≤chargedCoefficient*((wordInput E target word).length+1)^32 := by
  have base : 1≤(wordInput E target word).length+1 := by omega
  have powers : ((wordInput E target word).length+1)^degree≤((wordInput E target word).length+1)^32 :=
    Nat.pow_le_pow_right base (by decide : degree≤32)
  have count := facts.time.trans (Nat.mul_le_mul_left coefficient powers)
  have sum := traceClockSum_le facts
  calc
    chargedCost source trace ≤ coefficient*((wordInput E target word).length+1)^32+
        coefficient^2*((wordInput E target word).length+1)^32 := Nat.add_le_add count sum
    _ = _ := by dsimp only [chargedCoefficient]; ring

end B23_4_RatWordPrep.OriginalFee.Cost
