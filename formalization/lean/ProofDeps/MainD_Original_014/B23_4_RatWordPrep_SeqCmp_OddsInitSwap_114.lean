module

public import B23_4_RatWordPrep_SeqCmp_OddsInitPackets_113

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.OddsInit

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem Segment.append_length_le {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

def SwapFrame (slot : RatInput.Stack) : Prop := slot≠4 ∧ slot≠13 ∧ slot≠14 ∧ slot≠15

theorem actual_swap (caller : Statement C) (before : State C) (fee prior comp : Rat)
    (active : before.l=some (.fee 0)) (scratch : before.stk 4=[])
    (empty13 : before.stk 13=[]) (empty14 : before.stk 14=[])
    (source : before.stk 15=RatInput.Encoder.packet fee
      (RatInput.Encoder.packet comp (RatInput.Encoder.packet prior []))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.divide default) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk 15=RatPair.input prior comp [] ∧ final.stk 4=[] ∧ final.stk 13=[] ∧ final.stk 14=[] ∧
      (∀ slot,SwapFrame slot→final.stk slot=before.stk slot) ∧
      run.trace.length≤8*(RatInput.Encoder.fieldSize fee+RatInput.Encoder.fieldSize prior+RatInput.Encoder.fieldSize comp)+80 := by
  obtain ⟨s1,p1,a1,v1,c1,t1⟩ := actual_packet caller feeLabel feeRoles false before fee
    (RatInput.Encoder.packet comp (RatInput.Encoder.packet prior [])) active source scratch
      (by intro point different; simp only [feeLabel,different,ite_false,program])
  have f1 (slot : RatInput.Stack) (n15 : slot≠15) (n4 : slot≠4) (n13 : slot≠13) : s1.stk slot=before.stk slot := by
    rw [c1]
    change (if slot=15 then _ else if slot=4 then _ else if slot=13 then _ else before.stk slot)=_
    simp only [n15,n4,n13,ite_false]
  obtain ⟨s2,p2,a2,v2,c2,t2⟩ := actual_erase caller s1 a1
  have compSource : s2.stk 15=RatInput.Encoder.packet comp (RatInput.Encoder.packet prior []) := by rw [c2,c1]; rfl
  have temp2 : s2.stk 4=[] := by rw [c2,c1]; rfl
  obtain ⟨s3,p3,a3,v3,c3,t3⟩ := actual_packet caller compLabel feeRoles false s2 comp
    (RatInput.Encoder.packet prior []) a2 compSource temp2
      (by intro point different; simp only [compLabel,different,ite_false,program])
  have f3 (slot : RatInput.Stack) (n15 : slot≠15) (n4 : slot≠4) (n13 : slot≠13) : s3.stk slot=s2.stk slot := by
    rw [c3]
    change (if slot=15 then _ else if slot=4 then _ else if slot=13 then _ else s2.stk slot)=_
    simp only [n15,n4,n13,ite_false]
  have priorSource : s3.stk 15=RatInput.Encoder.packet prior [] := by rw [c3]; rfl
  have temp3 : s3.stk 4=[] := by rw [c3]; rfl
  obtain ⟨s4,p4,a4,v4,c4,t4⟩ := actual_packet caller priorLabel priorRoles false s3 prior [] a3 priorSource temp3
    (by intro point different; simp only [priorLabel,different,ite_false,program])
  have f4 (slot : RatInput.Stack) (n15 : slot≠15) (n4 : slot≠4) (n14 : slot≠14) : s4.stk slot=s3.stk slot := by
    rw [c4]
    change (if slot=15 then _ else if slot=4 then _ else if slot=14 then _ else s3.stk slot)=_
    simp only [n15,n4,n14,ite_false]
  have compPark : s4.stk 13=RatInput.Encoder.packet comp [] := by
    rw [f4 13 (by decide) (by decide) (by decide),c3,c2]
    rfl
  have temp4 : s4.stk 4=[] := by rw [c4]; rfl
  obtain ⟨s5,p5,a5,v5,c5,t5⟩ := actual_packet caller compReturnLabel compReturnRoles false s4 comp [] a4 compPark temp4
    (by intro point different; simp only [compReturnLabel,different,ite_false,program])
  have f5 (slot : RatInput.Stack) (n13 : slot≠13) (n4 : slot≠4) (n15 : slot≠15) : s5.stk slot=s4.stk slot := by
    rw [c5]
    change (if slot=13 then _ else if slot=4 then _ else if slot=15 then _ else s4.stk slot)=_
    simp only [n13,n4,n15,ite_false]
  have priorPark : s5.stk 14=RatInput.Encoder.packet prior [] := by
    rw [f5 14 (by decide) (by decide) (by decide),c4]
    change RatInput.Encoder.packet prior (s3.stk 14)=RatInput.Encoder.packet prior []
    rw [f3 14 (by decide) (by decide) (by decide),c2]
    change RatInput.Encoder.packet prior (s1.stk 14)=RatInput.Encoder.packet prior []
    rw [f1 14 (by decide) (by decide) (by decide),empty14]
  have temp5 : s5.stk 4=[] := by rw [c5]; rfl
  obtain ⟨final,p6,a6,v6,c6,t6⟩ := actual_packet caller priorReturnLabel priorReturnRoles false s5 prior [] a5 priorPark temp5
    (by intro point different; simp only [priorReturnLabel,different,ite_false,program])
  have f6 (slot : RatInput.Stack) (n14 : slot≠14) (n4 : slot≠4) (n15 : slot≠15) : final.stk slot=s5.stk slot := by
    rw [c6]
    change (if slot=14 then _ else if slot=4 then _ else if slot=15 then _ else s5.stk slot)=_
    simp only [n14,n4,n15,ite_false]
  let whole := ((((p1.append p2).append p3).append p4).append p5).append p6
  refine ⟨final,whole,a6,v6.trans (v5.trans (v4.trans (v3.trans (v2.trans v1)))),?_,?_,?_,?_,?_,?_⟩
  · rw [c6]
    change RatInput.Encoder.packet prior (s5.stk 15)=RatPair.input prior comp []
    rw [c5]
    change RatInput.Encoder.packet prior (RatInput.Encoder.packet comp (s4.stk 15))=_
    rw [c4]
    exact RatPair.two_packet_format prior comp []
  · rw [c6]; rfl
  · rw [f6 13 (by decide) (by decide) (by decide),c5]; rfl
  · rw [c6]; rfl
  · intro slot safe
    exact (f6 slot safe.2.2.1 safe.1 safe.2.2.2).trans
      ((f5 slot safe.2.1 safe.1 safe.2.2.2).trans ((f4 slot safe.2.2.2 safe.1 safe.2.2.1).trans
        ((f3 slot safe.2.2.2 safe.1 safe.2.1).trans (by
          rw [c2,Function.update_of_ne safe.2.1]
          exact f1 slot safe.2.2.2 safe.1 safe.2.1))))
  · have feePark : s1.stk 13=RatInput.Encoder.packet fee [] := by
      rw [c1]
      change RatInput.Encoder.packet fee (before.stk 13)=_
      rw [empty13]
    have erased : p2.trace.length=2*RatInput.Encoder.fieldSize fee+8 := by
      rw [t2,feePark,RatInput.Encoder.packet_length]
      simp only [List.length_nil]
    have j2 := p1.append_length_le p2
    have j3 := (p1.append p2).append_length_le p3
    have j4 := ((p1.append p2).append p3).append_length_le p4
    have j5 := (((p1.append p2).append p3).append p4).append_length_le p5
    have j6 := ((((p1.append p2).append p3).append p4).append p5).append_length_le p6
    change (((((p1.append p2).append p3).append p4).append p5).append p6).trace.length≤_
    omega

end B23_4_RatWordPrep.OddsInit
