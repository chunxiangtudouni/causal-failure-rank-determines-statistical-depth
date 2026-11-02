module

public import Paid.PDLower_CalibrationCompute_EmitCache_050
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Complete actual emit phase: the stream, the heap cache, the real
outer-level increment and the actual absolute jump are all covered. -/
theorem emit_correct (origin : ℕ) (input : List Cell) (base start : ℕ) (values : List Cell)
    (before : State) (header : Header) (weight : ℚ)
    (position : before.pc=labelAddress origin .emit)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (value : before.register .value=.rational weight)
    (cache : HeapList before start values) (cursor : header.outputCursor=start+values.length)
    (outside : base+16≤start) :
    ∃ after : State,Segment origin input before after 390 ∧
      after.pc=labelAddress origin .levelGate ∧
      ({header with level:=header.level+1,outputCursor:=header.outputCursor+2}).At after base ∧
      HeapList after start (values++[.rational header.q,.rational weight]) ∧
      after.register .fresh=.natural base ∧
      after.output=before.output++[.rational header.q,.rational weight] := by
  let completed := emitResult before base header.outputCursor header.level header.q weight
  let after : State := {completed with pc:=labelAddress origin .levelGate}
  have safeCursor : base+16≤header.outputCursor := by omega
  have actual : Segment origin input before after 390 :=
    segment_go origin .emit .levelGate input before completed position
      (emit_execute input before base header weight represented fresh value safeCursor) rfl
  refine ⟨after,actual,rfl,emit_header weight represented safeCursor,?_,?_,
    emit_output before base header.outputCursor header.level header.q weight⟩
  · change HeapList (emitResult before base header.outputCursor header.level header.q weight) start _
    rw [cursor]
    exact emit_cache cache header.level header.q weight outside
  · exact (emit_fresh before base header.outputCursor header.level header.q weight).trans fresh

end PDLower.CalibrationCompute
