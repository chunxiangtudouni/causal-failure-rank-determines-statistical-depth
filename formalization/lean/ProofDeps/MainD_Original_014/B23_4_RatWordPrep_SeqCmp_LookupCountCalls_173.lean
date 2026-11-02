module

public import B23_4_RatWordPrep_SeqCmp_LookupActual_100
public import B23_4_RatWordPrep_SeqCmp_WordPrimitiveMass_158
public import B23_4_RatWordPrep_SeqCmp_WordCountToResources_157

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

noncomputable def pushCap (truth : Bool) (caller : Statement C) : Nat :=
  Classical.choose (WordFinish.Resources.finite_push_bound (program truth caller))

theorem pushes (truth : Bool) (caller : Statement C) :
    ∀ point,AuxWorkspace.pushes (program truth caller point)≤pushCap truth caller :=
  Classical.choose_spec (WordFinish.Resources.finite_push_bound (program truth caller))

theorem append_length_le {truth : Bool} {caller : Statement C} {before middle final : State C}
    (front : Segment truth caller before middle) (back : Segment truth caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

theorem actual_round (truth : Bool) (caller : Statement C)
    (rename : RootB234.RuntimeCounter.Round.Label → Label) (before : State C) (digits : List Bool)
    (active : before.l=some (rename 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (same : ∀ point,point≠7→point≠8→program truth caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.roundIso C)
        (RootB234.RuntimeCounter.Round.program point))) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some (rename (if PSTRTMIncrement009.valueDigits digits=0 then 7 else 8)) ∧
      final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.RuntimeCounter.Round.cells before.stk
        (RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits)) [false] [] ∧
      run.trace.length≤256*(RatInput.occupied before.stk+1) ∧
      RatInput.occupied final.stk=RatInput.occupied before.stk := by
  obtain ⟨final,run,port,context,contents,time⟩ :=
    Lookup.actual_round truth caller rename before digits active right left scratch same
  rw [WordFinish.Resources.round_scale before.stk digits right left scratch] at time
  have frame (slot : RatInput.Stack) (n4 : slot≠4) (n10 : slot≠10) (n11 : slot≠11) :
      final.stk slot=before.stk slot := by
    rw [contents]
    exact RootB234.RuntimeCounter.Round.cells_frame _ _ _ _ slot
      (by simp only [RootB234.RuntimeCounter.Round.Work,n4,n10,n11,or_self,not_false_eq_true])
  have outRight : final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits) := by rw [contents]; rfl
  have outLeft : final.stk 11=[false] := by rw [contents]; rfl
  have outScratch : final.stk 4=[] := by rw [contents]; rfl
  exact ⟨final,run,port,context,contents,time,
    WordFinish.Resources.round_mass before.stk final.stk digits right outRight
      (outLeft.trans left.symm) (outScratch.trans scratch.symm) frame⟩

theorem actual_move (truth : Bool) (caller : Statement C)
    (rename : RootB234.RatPacketTransport.Label → Label) (roles : RatInput.Stack ≃ RatInput.Stack)
    (before : State C) (x : Rat) (tail : List Bool) (active : before.l=some (rename 0))
    (source : before.stk (roles 15)=RatInput.Encoder.packet x tail) (scratch : before.stk (roles 4)=[])
    (same : ∀ point,point≠4→program truth caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.packetIso C)
        (RootB234.RatPacketTransport.atProgram roles false point))) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some (rename 4) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank roles before.stk tail []
        (RatInput.Encoder.packet x (before.stk (roles 2))) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 ∧
      RatInput.occupied final.stk=RatInput.occupied before.stk := by
  obtain ⟨final,run,port,context,contents,time⟩ :=
    Lookup.actual_packet truth caller rename roles false before x tail active source scratch same
  have newSource : final.stk (roles 15)=tail := by rw [contents]; simp [RootB234.RatPacketTransport.atBank]
  have newTarget : final.stk (roles 2)=RatInput.Encoder.packet x (before.stk (roles 2)) := by
    rw [contents]; simp [RootB234.RatPacketTransport.atBank]
  have newScratch : final.stk (roles 4)=[] := by rw [contents]; simp [RootB234.RatPacketTransport.atBank]
  have frame (slot : RatInput.Stack) (n15 : slot≠roles 15) (n2 : slot≠roles 2) (n4 : slot≠roles 4) :
      final.stk slot=before.stk slot := by
    rw [contents]
    simp only [RootB234.RatPacketTransport.atBank,n15,n2,n4,ite_false]
  exact ⟨final,run,port,context,contents,time,
    WordFinish.Resources.rational_move_mass before.stk final.stk (roles 15) (roles 2) (roles 4)
      (roles.injective.ne (by decide)) x tail source newSource newTarget
      (newScratch.trans scratch.symm) frame⟩

end B23_4_RatWordPrep.Lookup.Count
