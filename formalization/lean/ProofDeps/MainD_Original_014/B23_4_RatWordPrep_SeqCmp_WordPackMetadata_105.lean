module

public import B23_4_RatWordPrep_SeqCmp_WordPackCalls_104

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordPack

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem Segment.append_length_le {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

def MetadataFrame (slot : RatInput.Stack) : Prop := slot≠0 ∧ slot≠1 ∧ slot≠4 ∧ slot≠8 ∧ slot≠9

theorem actual_metadata (caller : Statement C) (before : State C) (number : Nat) (target : Rat)
    (active : before.l=some (.clear0 0)) (scratch : before.stk 4=[])
    (alphabet : before.stk 8=NatField.packet number [])
    (targetPacket : before.stk 9=RatInput.Encoder.packet target []) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .wordCheck ∧ final.var.2.2=before.var.2.2 ∧ final.stk 0=[] ∧
      final.stk 1=NatField.packet number (RatInput.Encoder.packet target []) ∧
      final.stk 8=[] ∧ final.stk 9=[] ∧ final.stk 4=[] ∧
      (∀ slot,MetadataFrame slot→final.stk slot=before.stk slot) ∧
      run.trace.length≤(before.stk 0).length+(before.stk 1).length+
        3*RatInput.Encoder.fieldSize target+3*(PSTRTMNatValue017.rawPayload number).length+32 := by
  obtain ⟨s1,p1,a1,v1,c1,t1,_b1⟩ := actual_cells caller .clear0 clear0Label before active
    (by intro point different; change point≠6 at different
        simp only [clear0Label,different,ite_false,program]; rfl)
  obtain ⟨s2,p2,a2,v2,c2,t2,_b2⟩ := actual_cells caller .clear1 clear1Label s1 a1
    (by intro point different; change point≠6 at different
        simp only [clear1Label,different,ite_false,program]; rfl)
  have frameClear (slot : RatInput.Stack) (n0 : slot≠0) (n1 : slot≠1) : s2.stk slot=before.stk slot := by
    rw [c2,c1]
    change Function.update (Function.update before.stk 0 []) 1 [] slot=before.stk slot
    rw [Function.update_of_ne n1,Function.update_of_ne n0]
  have sourceTarget : s2.stk (targetRoles 15)=RatInput.Encoder.packet target [] :=
    (frameClear 9 (by decide) (by decide)).trans targetPacket
  have scratchTarget : s2.stk (targetRoles 4)=[] := (frameClear 4 (by decide) (by decide)).trans scratch
  obtain ⟨s3,p3,a3,v3,c3,t3⟩ := actual_packet caller targetLabel targetRoles false s2 target []
    a2 sourceTarget scratchTarget (by intro point different; simp only [targetLabel,different,ite_false,program])
  have frameTarget (slot : RatInput.Stack) (n9 : slot≠9) (n4 : slot≠4) (n1 : slot≠1) : s3.stk slot=s2.stk slot := by
    rw [c3]
    change (if slot=9 then _ else if slot=4 then _ else if slot=1 then _ else s2.stk slot)=_
    simp only [n9,n4,n1,ite_false]
  have sourceAlphabet : s3.stk (alphabetRoles 15)=NatField.packet number [] :=
    (frameTarget 8 (by decide) (by decide) (by decide)).trans
      ((frameClear 8 (by decide) (by decide)).trans alphabet)
  have scratchAlphabet : s3.stk (alphabetRoles 4)=[] := by rw [c3]; rfl
  obtain ⟨final,p4,a4,v4,c4,t4⟩ := actual_natural caller alphabetLabel alphabetRoles s3 number []
    a3 sourceAlphabet scratchAlphabet (by intro point different; simp only [alphabetLabel,different,ite_false,program])
  have frameAlphabet (slot : RatInput.Stack) (n8 : slot≠8) (n4 : slot≠4) (n1 : slot≠1) : final.stk slot=s3.stk slot := by
    rw [c4]
    change (if slot=8 then _ else if slot=4 then _ else if slot=1 then _ else s3.stk slot)=_
    simp only [n8,n4,n1,ite_false]
  let whole := ((p1.append p2).append p3).append p4
  refine ⟨final,whole,a4,v4.trans (v3.trans (v2.trans v1)),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [frameAlphabet 0 (by decide) (by decide) (by decide),frameTarget 0 (by decide) (by decide) (by decide),c2,c1]
    rfl
  · rw [c4]
    change NatField.packet number (s3.stk 1)=_
    rw [c3]
    change NatField.packet number (RatInput.Encoder.packet target (s2.stk 1))=_
    rw [c2]
    rfl
  · rw [c4]; rfl
  · rw [frameAlphabet 9 (by decide) (by decide) (by decide),c3]; rfl
  · rw [c4]; rfl
  · intro slot safe
    exact (frameAlphabet slot safe.2.2.2.1 safe.2.2.1 safe.2.1).trans
      ((frameTarget slot safe.2.2.2.2 safe.2.2.1 safe.2.1).trans (frameClear slot safe.1 safe.2.1))
  · have count1 : p1.trace.length=(before.stk 0).length+2 := t1
    have count2 : p2.trace.length=(before.stk 1).length+2 := by
      rw [t2,c1]
      rfl
    have joined1 := p1.append_length_le p2
    have joined2 := (p1.append p2).append_length_le p3
    have joined3 := ((p1.append p2).append p3).append_length_le p4
    change (((p1.append p2).append p3).append p4).trace.length≤_
    omega

end B23_4_RatWordPrep.WordPack
