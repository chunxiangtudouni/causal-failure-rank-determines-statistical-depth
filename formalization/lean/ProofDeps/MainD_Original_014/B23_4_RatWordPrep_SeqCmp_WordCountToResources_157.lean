module

public import B23_4_RatWordPrep_SeqCmp_WordMassGrowth_156
public import B23_4_RatWordPrep_SeqCmp_WordResourceJoin_142

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

variable {C : Type*}

theorem finite_push_bound {τ Ψ : Type*} [Fintype Ψ] (source : Ψ → TM2.Stmt RatInput.Alphabet Ψ τ) :
    ∃ cap : Nat,∀ point,AuxWorkspace.pushes (source point)≤cap := by
  exact ⟨(Finset.univ : Finset Ψ).sup (fun point => AuxWorkspace.pushes (source point)),
    fun point => Finset.le_sup (f := fun label => AuxWorkspace.pushes (source label)) (Finset.mem_univ point)⟩

theorem finite_action_bound {τ Ψ : Type*} [Fintype Ψ] (source : Ψ → TM2.Stmt RatInput.Alphabet Ψ τ) :
    ∃ cap : Nat,∀ point,ScannerClock.actions (source point)≤cap := by
  exact ⟨(Finset.univ : Finset Ψ).sup (fun point => ScannerClock.actions (source point)),
    fun point => Finset.le_sup (f := fun label => ScannerClock.actions (source label)) (Finset.mem_univ point)⟩

/-- These finite syntax constants precede every original input and all
executions. No host answer or runtime cost is supplied to the source. -/
noncomputable def sourcePushCap (C : Type*) : Nat :=
  Classical.choose (finite_push_bound (program (C := C) .halt))

noncomputable def sourceActionCap (C : Type*) : Nat :=
  Classical.choose (finite_action_bound (program (C := C) .halt))

theorem source_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point)≤sourcePushCap C :=
  Classical.choose_spec (finite_push_bound (program (C := C) .halt)) point

theorem source_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point)≤sourceActionCap C :=
  Classical.choose_spec (finite_action_bound (program (C := C) .halt)) point

/-- Turns an actual whole-source count into W/A/P and scanning resources
by proved physical push growth. The original same trace is retained.
Canonical packet reentry bounds are used to obtain the count separately. -/
theorem count_to_resources {before final : State C} (run : Segment .halt before final) (bound time : Nat)
    (initial : RatInput.occupied before.stk≤bound) (count : run.trace.length≤time) :
    RunBounds .halt run time (bound+sourcePushCap C*time+sourcePushCap C)
      (2*sourceActionCap C*(bound+sourcePushCap C*time+sourcePushCap C+1)) := by
  have mass (current : State C) (member : current∈run.trace) :
      RatInput.occupied current.stk≤bound+sourcePushCap C*time :=
    (trace_mass (sourcePushCap C) source_pushes run.trace before bound run.first run.chain initial current member).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ count) _)
  have slots (current : State C) (member : current∈run.trace) (slot : RatInput.Stack) :
      (current.stk slot).length≤bound+sourcePushCap C*time :=
    (RatInput.Encoder.point_mass current.stk slot).trans (mass current member)
  constructor
  · exact count
  · intro current member slot
    exact (slots current member slot).trans (Nat.le_add_right _ _)
  · intro current member point _selected node inside slot
    have boundNode := node_mass (program .halt point) current.var current.stk node inside
    have currentMass := mass current (List.mem_of_mem_dropLast member)
    have pushes := source_pushes (C := C) point
    exact (RatInput.Encoder.point_mass node.2 slot).trans (by omega)
  · intro current member point _selected
    have boundClock := ScannerClock.clock_bound (program .halt point) current.var current.stk
      (bound+sourcePushCap C*time) (slots current (List.mem_of_mem_dropLast member))
    exact boundClock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (source_actions (C := C) point))
      (Nat.add_le_add_right (Nat.add_le_add_left (source_pushes (C := C) point) _) 1))

theorem count_clockSum {before final : State C} (run : Segment .halt before final) (bound time : Nat)
    (initial : RatInput.occupied before.stk≤bound) (count : run.trace.length≤time) :
    traceClockSum (program .halt) run.trace≤
      time*(2*sourceActionCap C*(bound+sourcePushCap C*time+sourcePushCap C+1)) :=
  (count_to_resources run bound time initial count).clockSum

theorem count_charge {before final : State C} (run : Segment .halt before final) (bound time : Nat)
    (initial : RatInput.occupied before.stk≤bound) (count : run.trace.length≤time) :
    run.trace.length+traceClockSum (program .halt) run.trace≤
      time*(2*sourceActionCap C*(bound+sourcePushCap C*time+sourcePushCap C+1)+1) :=
  (count_to_resources run bound time initial count).charge

end B23_4_RatWordPrep.WordFinish.Resources
