module

public import B23_4_RatWordPrep_SeqCmp_WordResourceTransport_140

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem joined_trace {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace=front.trace.dropLast++back.trace := by
  have frontShape : front.trace.dropLast++[middle]=front.trace :=
    List.dropLast_append_getLast? middle (by rw [front.last]; rfl)
  have backShape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,shape⟩ := List.head?_eq_some_iff.mp back.first
    rw [shape]
    rfl
  change front.trace++back.trace.tail=_
  calc
    _=(front.trace.dropLast++[middle])++back.trace.tail :=
      congrArg (fun path => path++back.trace.tail) frontShape.symm
    _=front.trace.dropLast++(middle::back.trace.tail) := by rw [List.append_assoc]; rfl
    _=front.trace.dropLast++back.trace := congrArg (List.append front.trace.dropLast) backShape

theorem joined_proper {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.dropLast=front.trace.dropLast++back.trace.dropLast := by
  have nonempty : back.trace≠[] := by
    intro empty
    have first := back.first
    rw [empty] at first
    cases first
  rw [joined_trace,List.dropLast_append_of_ne_nil nonempty]

theorem joined_clockSum {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    traceClockSum (program caller) (front.append back).trace=
      traceClockSum (program caller) front.trace+traceClockSum (program caller) back.trace := by
  unfold traceClockSum
  rw [joined_proper,List.map_append,List.sum_append]

/-- Resource fields concern exactly the Segment witness, including all
internal statement nodes and the actual scanner clock on proper states. -/
structure RunBounds (caller : Statement C) {before final : State C}
    (run : Segment caller before final) (time space clock : Nat) : Prop where
  count : run.trace.length≤time
  boundary : ∀ current∈run.trace,∀ slot,(current.stk slot).length≤space
  internal : ∀ current∈run.trace.dropLast,∀ point,current.l=some point→
    ∀ node∈AuxWorkspace.nodes (program caller point) current.var current.stk,
      ∀ slot,(node.2 slot).length≤space
  clocks : ∀ current∈run.trace.dropLast,∀ point,current.l=some point→
    ScannerStatement.clock (program caller point) current.var current.stk≤clock

theorem RunBounds.append {caller : Statement C} {before middle final : State C}
    {front : Segment caller before middle} {back : Segment caller middle final}
    {time1 space1 clock1 time2 space2 clock2 : Nat}
    (a : RunBounds caller front time1 space1 clock1) (b : RunBounds caller back time2 space2 clock2) :
    RunBounds caller (front.append back) (time1+time2) (max space1 space2) (max clock1 clock2) := by
  constructor
  · exact (front.append_length_le back).trans (Nat.add_le_add a.count b.count)
  · intro current member slot
    rw [joined_trace] at member
    rcases List.mem_append.mp member with present | present
    · exact (a.boundary current (List.mem_of_mem_dropLast present) slot).trans (Nat.le_max_left _ _)
    · exact (b.boundary current present slot).trans (Nat.le_max_right _ _)
  · intro current member point selected node inside slot
    rw [joined_proper] at member
    rcases List.mem_append.mp member with present | present
    · exact (a.internal current present point selected node inside slot).trans (Nat.le_max_left _ _)
    · exact (b.internal current present point selected node inside slot).trans (Nat.le_max_right _ _)
  · intro current member point selected
    rw [joined_proper] at member
    rcases List.mem_append.mp member with present | present
    · exact (a.clocks current present point selected).trans (Nat.le_max_left _ _)
    · exact (b.clocks current present point selected).trans (Nat.le_max_right _ _)

theorem RunBounds.clockSum {caller : Statement C} {before final : State C}
    {run : Segment caller before final} {time space clock : Nat}
    (bounds : RunBounds caller run time space clock) :
    traceClockSum (program caller) run.trace≤time*clock := by
  have termwise : ∀ value∈run.trace.dropLast.map (stateClock (program caller)),value≤clock := by
    intro value member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [stateClock,selected,Nat.zero_le]
    | some point =>
      simpa only [stateClock,selected] using bounds.clocks current present point selected
  have total : traceClockSum (program caller) run.trace≤run.trace.dropLast.length*clock := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (run.trace.dropLast.map (stateClock (program caller))) clock termwise
  have count : run.trace.dropLast.length≤time := by
    rw [List.length_dropLast]
    exact (Nat.sub_le run.trace.length 1).trans bounds.count
  exact total.trans (Nat.mul_le_mul_right clock count)

theorem RunBounds.charge {caller : Statement C} {before final : State C}
    {run : Segment caller before final} {time space clock : Nat}
    (bounds : RunBounds caller run time space clock) :
    run.trace.length+traceClockSum (program caller) run.trace≤time*(clock+1) := by
  calc
    _≤time+time*clock := Nat.add_le_add bounds.count bounds.clockSum
    _=time*(clock+1) := by ring

theorem RunBounds.boundary_mass {caller : Statement C} {before final : State C}
    {run : Segment caller before final} {time space clock : Nat}
    (bounds : RunBounds caller run time space clock) (current : State C) (present : current∈run.trace) :
    RatInput.occupied current.stk≤16*space :=
  RatInput.Encoder.occupied_bound current.stk space (bounds.boundary current present)

theorem RunBounds.internal_mass {caller : Statement C} {before final : State C}
    {run : Segment caller before final} {time space clock : Nat}
    (bounds : RunBounds caller run time space clock) (current : State C) (present : current∈run.trace.dropLast)
    (point : Label) (selected : current.l=some point)
    (node : Store C × (RatInput.Stack → List Bool))
    (inside : node∈AuxWorkspace.nodes (program caller point) current.var current.stk) :
    RatInput.occupied node.2≤16*space :=
  RatInput.Encoder.occupied_bound node.2 space (bounds.internal current present point selected node inside)

end B23_4_RatWordPrep.WordFinish.Resources
