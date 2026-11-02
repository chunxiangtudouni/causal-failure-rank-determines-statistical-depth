module

public import B23_4_RatWordPrep_SeqCmp_WordPrimitiveMass_158
public import B23_4_RatWordPrep_SeqCmp_WordCountToResources_157
public import B23_4_RatWordPrep_SeqCmp_WordFieldsMoves_085

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def pushCap (caller : Statement C) : Nat :=
  Classical.choose (WordFinish.Resources.finite_push_bound (program caller))
theorem pushes (caller : Statement C) (point : Label) : AuxWorkspace.pushes (program caller point)≤pushCap caller :=
  Classical.choose_spec (WordFinish.Resources.finite_push_bound (program caller)) point

theorem append_length_le {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

theorem actual_target (caller : Statement C) (before : State C) (x : Rat) (suffix : List Bool)
    (active : before.l=some (.target .boot))
    (right : ListBlank.mk (before.stk 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true])) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.targetMove 0) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 15=RatInput.Encoder.packet x (before.stk 15) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      (∀ slot,slot≠0 → slot≠1 → slot≠15 → final.stk slot=before.stk slot) ∧
      run.trace.length≤RawGetter.time x ∧
      RatInput.occupied final.stk≤RatInput.occupied before.stk+pushCap caller*RawGetter.time x := by
  obtain ⟨final,run,port,context,packet,cursor,frame,time⟩ := WordFields.actual_target caller before x suffix active right
  have mass := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller) run.trace before
    (RatInput.occupied before.stk) run.first run.chain (Nat.le_refl _) final (List.mem_of_getLast? run.last)
  exact ⟨final,run,port,context,packet,cursor,frame,time,
    mass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ time) _)⟩

theorem actual_natural (symbolMode : Bool) (caller : Statement C) (before : State C)
    (number : Nat) (suffix : List Bool)
    (active : before.l=some (if symbolMode then .symbol .boot else .count .boot))
    (right : ListBlank.mk (before.stk 0)=ListBlank.mk (encodeDatum (.natural number)++suffix++[true])) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (if symbolMode then .symbolMove 2 else .countMove 2) ∧
      final.var.2=before.var.2 ∧ final.stk 15=NatField.packet number (before.stk 15) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      (∀ slot,slot≠0 → slot≠1 → slot≠15 → final.stk slot=before.stk slot) ∧
      run.trace.length≤RawNat.time number ∧
      RatInput.occupied final.stk≤RatInput.occupied before.stk+pushCap caller*RawNat.time number := by
  obtain ⟨final,run,port,context,packet,cursor,frame,time⟩ :=
    WordFields.actual_natural symbolMode caller before number suffix active right
  have mass := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller) run.trace before
    (RatInput.occupied before.stk) run.first run.chain (Nat.le_refl _) final (List.mem_of_getLast? run.last)
  exact ⟨final,run,port,context,packet,cursor,frame,time,
    mass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ time) _)⟩

theorem actual_round (caller : Statement C) (before : State C) (digits : List Bool)
    (active : before.l=some (.round 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (if PSTRTMIncrement009.valueDigits digits=0 then .done else .symbol .boot) ∧
      final.var.2.2=before.var.2.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,slot≠4 → slot≠10 → slot≠11 → final.stk slot=before.stk slot) ∧
      run.trace.length≤256*(RatInput.occupied before.stk+1) ∧ RatInput.occupied final.stk=RatInput.occupied before.stk := by
  obtain ⟨final,run,port,context,outRight,outLeft,outScratch,frame,time⟩ :=
    WordFields.actual_round caller before digits active right left scratch
  rw [WordFinish.Resources.round_scale before.stk digits right left scratch] at time
  exact ⟨final,run,port,context,outRight,outLeft,outScratch,frame,time,
    WordFinish.Resources.round_mass before.stk final.stk digits right outRight
      (outLeft.trans left.symm) (outScratch.trans scratch.symm) frame⟩

theorem actual_target_move (caller : Statement C) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (.targetMove 0)) (source : before.stk 15=RatInput.Encoder.packet x tail)
    (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.count .boot) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 15=tail ∧ final.stk 9=RatInput.Encoder.packet x (before.stk 9) ∧ final.stk 4=[] ∧
      (∀ slot,slot≠9 → slot≠4 → slot≠15 → final.stk slot=before.stk slot) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 ∧ RatInput.occupied final.stk=RatInput.occupied before.stk := by
  obtain ⟨final,run,port,context,outSource,outTarget,outScratch,frame,time⟩ :=
    WordFields.actual_target_move caller before x tail active source scratch
  exact ⟨final,run,port,context,outSource,outTarget,outScratch,frame,time,
    WordFinish.Resources.rational_move_mass before.stk final.stk 15 9 4 (by decide) x tail source outSource outTarget
      (outScratch.trans scratch.symm) (by intro slot n15 n9 n4; exact frame slot n9 n4 n15)⟩

theorem actual_natural_move (symbolMode : Bool) (caller : Statement C) (before : State C)
    (number : Nat) (tail : List Bool)
    (active : before.l=some (if symbolMode then .symbolMove 2 else .countMove 2))
    (source : before.stk 15=NatField.packet number tail) (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (if symbolMode then .round 0 else .build 0) ∧
      final.var.2.2=before.var.2.2 ∧ final.stk 15=tail ∧
      final.stk 3=NatField.packet number (before.stk 3) ∧ final.stk 4=[] ∧
      (∀ slot,slot≠3 → slot≠4 → slot≠15 → final.stk slot=before.stk slot) ∧
      run.trace.length≤3*(PSTRTMNatValue017.rawPayload number).length+6 ∧
      RatInput.occupied final.stk=RatInput.occupied before.stk := by
  obtain ⟨final,run,port,context,outSource,outTarget,outScratch,frame,time⟩ :=
    WordFields.actual_natural_move symbolMode caller before number tail active source scratch
  exact ⟨final,run,port,context,outSource,outTarget,outScratch,frame,time,
    WordFinish.Resources.natural_move_mass before.stk final.stk 15 3 4 (by decide) number tail source outSource outTarget
      (outScratch.trans scratch.symm) (by intro slot n15 n3 n4; exact frame slot n3 n4 n15)⟩

end B23_4_RatWordPrep.WordFields.Count
