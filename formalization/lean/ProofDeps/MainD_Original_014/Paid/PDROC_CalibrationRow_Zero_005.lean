module

public import Paid.PDROC_CalibrationRow_Zero_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow.ZeroRuntime

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem control_carry (origin : ℕ) (control : Control) (input : List Cell) (before after : State)
    (run : (controlInstruction origin control).execute input before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.register .fresh=before.register .fresh := by
  have frame := execute_memoryFrame (∅ : Finset ℕ) (controlInstruction origin control) input before after
    (by cases control <;> trivial) run
  exact ⟨funext (fun address => frame.1 address (by simp)),Finset.ext (fun address => frame.2 address (by simp)),
    execute_preserves_fresh _ (control_noFresh origin control) input before after run⟩

theorem gate_phase (input : List Cell) (P : Parameters) (origin base level clock cursor read write : ℕ)
    (previous : Array ℚ) (before middle after state : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (body : linearExecute input (basicBlock .zeroGate).body before=some middle)
    (control : (controlInstruction origin (basicBlock .zeroGate).control).execute input middle=some after)
    (location : (∃ count≤(basicBlock .zeroGate).body.length,
      linearExecute input ((basicBlock .zeroGate).body.take count) before=some state) ∨ state=after) :
    Phase P base level clock read write previous cursor cursor before state := by
  have frames : LinearFrames (∅ : Finset ℕ) input (basicBlock .zeroGate).body before := by
    simpa only [zeroGate_body] using gate_prefix_frames (∅ : Finset ℕ) input before 7 8
  rcases location with ⟨count,_,run⟩|equal
  · have frame := frames count state run
    exact phase_sameMemory P base level clock cursor read write previous before state data
      (funext (fun address => frame.1 address (by simp)))
      (Finset.ext (fun address => frame.2 address (by simp)))
      (rowBody_prefix_fresh input .zeroGate before state count run)
  · subst state
    have frame := frames.final body
    have carry := control_carry origin (basicBlock .zeroGate).control input middle after control
    have heap := carry.1.trans (funext (fun address => frame.1 address (by simp)))
    have live := carry.2.1.trans (Finset.ext (fun address => frame.2 address (by simp)))
    have fresh := carry.2.2.trans (rowBody_prefix_fresh input .zeroGate before middle (basicBlock .zeroGate).body.length
      (by simpa only [List.take_length] using body))
    exact phase_sameMemory P base level clock cursor read write previous before after data heap live fresh

/-- Exact same-trace provenance includes the real clock/cursor/read-row,
written zero prefix, caller's unchanged unvisited heap AND live suffix,
and the concrete literal prefix. The middle cell phase records(c+1,c),
not the stronger and false boundary ZeroData(c+1). -/
inductive ZeroProvenance (P : Parameters) (origin base level clock read write : ℕ)
    (previous : Array ℚ) (input : List Cell) (caller : State) : State→Prop where
  | initial (data : ZeroData P base level clock 0 read write previous caller) :
      ZeroProvenance P origin base level clock read write previous input caller caller
  | gate (cursor : ℕ) (before middle after state : State)
      (previousStep : ZeroProvenance P origin base level clock read write previous input caller before)
      (entry : Boundary P base level clock cursor read write previous caller before) (bound : cursor≤2*level+1)
      (position : before.pc=labelAddress origin .zeroGate)
      (body : linearExecute input (basicBlock .zeroGate).body before=some middle)
      (control : (controlInstruction origin (basicBlock .zeroGate).control).execute input middle=some after)
      (location : (∃ count≤(basicBlock .zeroGate).body.length,
        linearExecute input ((basicBlock .zeroGate).body.take count) before=some state) ∨ state=after)
      (phase : Phase P base level clock read write previous cursor cursor caller state) :
      ZeroProvenance P origin base level clock read write previous input caller state
  | cell (cursor : ℕ) (before middle after state : State)
      (previousStep : ZeroProvenance P origin base level clock read write previous input caller before)
      (entry : Boundary P base level clock cursor read write previous caller before)
      (inside : cursor<2*level+1) (index : before.register .index=.natural cursor)
      (position : before.pc=labelAddress origin .zeroCell)
      (body : linearExecute input (basicBlock .zeroCell).body before=some middle)
      (control : (controlInstruction origin (basicBlock .zeroCell).control).execute input middle=some after)
      (location : (∃ count≤14,linearExecute input ((basicBlock .zeroCell).body.take count) before=some state ∧
        Phase P base level clock read write previous (prefixWritten cursor count) (prefixCursor cursor count) caller state) ∨
        (state=after ∧ Phase P base level clock read write previous (cursor+1) (cursor+1) caller state)) :
      ZeroProvenance P origin base level clock read write previous input caller state

theorem prefixWritten_ge (cursor count : ℕ) : cursor ≤ prefixWritten cursor count := by
  unfold prefixWritten
  split <;> omega

theorem provenance_closed (input : List Cell) (P : Parameters) (origin base level clock read write : ℕ)
    (previous : Array ℚ) (caller : State) (levelBound : level≤P.certificate.M+1) :
    Closed P origin base level clock read write previous input caller
      (ZeroProvenance P origin base level clock read write previous input caller) := by
  intro cursor label before middle after entry previousStep position body control state location
  rcases entry with ⟨boundary,bound,gate|⟨cell,inside,index⟩⟩
  · subst label
    have phase := gate_phase input P origin base level clock cursor read write previous before middle after state
      boundary.data body control location
    have root := Boundary.rootPhase P base level clock cursor read write previous cursor cursor caller before state
      boundary phase (Nat.le_refl _)
    exact ZeroProvenance.gate cursor before middle after state previousStep boundary bound position body control location root
  · subst label
    rcases location with ⟨count,countBound,run⟩|equal
    · have phase := zeroCell_prefix_phase input P base level clock cursor read write previous before state
        boundary.data inside levelBound index count countBound run
      have root := Boundary.rootPhase P base level clock cursor read write previous
        (prefixWritten cursor count) (prefixCursor cursor count) caller before state boundary phase (prefixWritten_ge cursor count)
      exact ZeroProvenance.cell cursor before middle after state previousStep boundary inside index position body control
        (Or.inl ⟨count,countBound,run,root⟩)
    · subst state
      have phase := zeroCell_prefix_phase input P base level clock cursor read write previous before middle
        boundary.data inside levelBound index 14 (by decide)
        (by change linearExecute input (basicBlock .zeroCell).body before=some middle; exact body)
      have full : Phase P base level clock read write previous (cursor+1) (cursor+1) before middle := by
        simpa only [prefixWritten,prefixCursor,show ¬(14 : ℕ)<6 from by decide,
          show ¬(14 : ℕ)<14 from by decide,ite_false] using phase
      have carry := control_carry origin (basicBlock .zeroCell).control input middle after control
      have phaseAfter := Phase.sameMemory P base level clock read write previous (cursor+1) (cursor+1)
        before middle after full carry.1 carry.2.1 carry.2.2
      have root := Boundary.rootPhase P base level clock cursor read write previous (cursor+1) (cursor+1)
        caller before after boundary phaseAfter (Nat.le_succ _)
      exact ZeroProvenance.cell cursor before middle after after previousStep boundary inside index position body control
        (Or.inr ⟨rfl,root⟩)

theorem ZeroProvenance.phase (P : Parameters) (origin base level clock read write : ℕ)
    (previous : Array ℚ) (input : List Cell) (caller state : State)
    (provenance : ZeroProvenance P origin base level clock read write previous input caller state) :
    ∃ written actualCursor,Phase P base level clock read write previous written actualCursor caller state := by
  cases provenance with
  | initial data => exact ⟨0,0,phase_sameMemory P base level clock 0 read write previous caller caller data rfl rfl rfl⟩
  | gate cursor before middle after state previousStep entry bound position body control location phase =>
    exact ⟨cursor,cursor,phase⟩
  | cell cursor before middle after state previousStep entry inside index position body control location =>
    rcases location with ⟨count,_,_,phase⟩|⟨_,phase⟩
    · exact ⟨prefixWritten cursor count,prefixCursor cursor count,phase⟩
    · exact ⟨cursor+1,cursor+1,phase⟩

end PDROC.CalibrationRow.ZeroRuntime
