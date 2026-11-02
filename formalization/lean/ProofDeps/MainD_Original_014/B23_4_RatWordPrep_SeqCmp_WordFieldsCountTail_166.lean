module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsCountLoop_164
public import B23_4_RatWordPrep_SeqCmp_WordFieldsCountCounter_165
public import B23_4_RatWordPrep_SeqCmp_WordFieldsTail_088

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

def headWork (before : State C) (target : Rat) (values : List Nat) : Nat :=
  RawGetter.time target+(3*RatInput.Encoder.fieldSize target+14)+RawNat.time values.length+
    (3*(PSTRTMNatValue017.rawPayload values.length).length+6)+
    ((before.stk 10).length+(before.stk 11).length+6*(PSTRTMNatValue017.rawPayload values.length).length+20)
noncomputable def tailAllowance (caller : Statement C) (before : State C) (target : Rat) (values : List Nat) : Nat :=
  RatInput.occupied before.stk+pushCap caller*(headWork before target values+readWork values)
noncomputable def tailBudget (caller : Statement C) (before : State C) (target : Rat) (values : List Nat) : Nat :=
  headWork before target values+loopBudget values (tailAllowance caller before target values)

theorem actual_tail (caller : Statement C) (before : State C) (target : Rat) (values : List Nat)
    (active : before.l=some (.target .boot)) (empty3 : before.stk 3=[]) (scratch : before.stk 4=[])
    (stream : ListBlank.mk (before.stk 0)=ListBlank.mk
      (encodeDatum (.rational target)++encodeDatum (.natural values.length)++fields values++[true])) :
    ∃ (final : State C) (run : Segment caller before final) (finalDigits : List Bool),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 15=before.stk 15 ∧ final.stk 9=RatInput.Encoder.packet target (before.stk 9) ∧
      final.stk 3=archived values [] ∧ ListBlank.mk (final.stk 0)=ListBlank.mk [true] ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(PSTRTMNatValue017.rawPayload values.length).length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,TailFrame slot → final.stk slot=before.stk slot) ∧
      RatInput.occupied final.stk≤tailAllowance caller before target values ∧
      run.trace.length≤tailBudget caller before target values := by
  have targetStream : ListBlank.mk (before.stk 0)=ListBlank.mk
      (encodeDatum (.rational target)++(encodeDatum (.natural values.length)++fields values)++[true]) := by
    simpa only [List.append_assoc] using stream
  obtain ⟨s1,p1,a1,v1,targetPacket,cursor1,f1,t1,_m1⟩ :=
    actual_target caller before target (encodeDatum (.natural values.length)++fields values) active targetStream
  have scratch1 : s1.stk 4=[] := (f1 4 (by decide) (by decide) (by decide)).trans scratch
  obtain ⟨s2,p2,a2,v2,prior2,targetStored,scratch2,f2,t2,_m2⟩ :=
    actual_target_move caller s1 target (before.stk 15) a1 targetPacket scratch1
  have countStream : ListBlank.mk (s2.stk 0)=ListBlank.mk (encodeDatum (.natural values.length)++fields values++[true]) := by
    rw [f2 0 (by decide) (by decide) (by decide)]
    exact cursor1
  obtain ⟨s3,p3,a3,v3,countPacket,cursor3,f3,t3,_m3⟩ :=
    actual_natural false caller s2 values.length (fields values) a2 countStream
  have scratch3 : s3.stk 4=[] := (f3 4 (by decide) (by decide) (by decide)).trans scratch2
  obtain ⟨s4,p4,a4,v4,prior4,countStored,scratch4,f4,t4,_m4⟩ :=
    actual_natural_move false caller s3 values.length (s2.stk 15) a3 countPacket scratch3
  have packet3 : s4.stk 3=NatField.packet values.length [] := by
    rw [countStored,f3 3 (by decide) (by decide) (by decide),f2 3 (by decide) (by decide) (by decide),
      f1 3 (by decide) (by decide) (by decide),empty3]
  obtain ⟨s5,p5,a5,v5,counter5,left5,scratch5,empty5,f5,t5,_m5⟩ :=
    actual_count_setup caller s4 values.length a4 packet3 scratch4
  have counterFrame (slot : RatInput.Stack) (n3 : slot≠3) (n4 : slot≠4) (n15 : slot≠15)
      (n0 : slot≠0) (n1 : slot≠1) (n9 : slot≠9) : s4.stk slot=before.stk slot :=
    (f4 slot n3 n4 n15).trans ((f3 slot n0 n1 n15).trans ((f2 slot n9 n4 n15).trans (f1 slot n0 n1 n15)))
  have paidSetup : p5.trace.length≤(before.stk 10).length+(before.stk 11).length+
      6*(PSTRTMNatValue017.rawPayload values.length).length+20 := by
    unfold countBuildWork at t5
    rw [counterFrame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      counterFrame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at t5
    exact t5
  let headRun := (((p1.append p2).append p3).append p4).append p5
  have headTime : headRun.trace.length≤headWork before target values := by
    have j2 := append_length_le p1 p2
    have j3 := append_length_le (p1.append p2) p3
    have j4 := append_length_le ((p1.append p2).append p3) p4
    have j5 := append_length_le (((p1.append p2).append p3).append p4) p5
    change ((((p1.append p2).append p3).append p4).append p5).trace.length≤_
    unfold headWork
    omega
  have headMass := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller) headRun.trace before
    (RatInput.occupied before.stk) headRun.first headRun.chain (Nat.le_refl _) s5 (List.mem_of_getLast? headRun.last)
  have paidMass := headMass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ headTime) _)
  have stream5 : ListBlank.mk (s5.stk 0)=ListBlank.mk (fields values++[]++[true]) := by
    rw [f5 0 (by decide) (by decide) (by decide) (by decide),f4 0 (by decide) (by decide) (by decide)]
    simpa only [List.append_nil] using cursor3
  have potential : RatInput.occupied s5.stk+pushCap caller*readWork values≤tailAllowance caller before target values := by
    unfold tailAllowance
    nlinarith
  obtain ⟨final,p6,finalDigits,a6,v6,prior6,symbols,cursor6,counter6,zero6,width6,left6,scratch6,f6,finalMass,loopTime⟩ :=
    actual_loop caller values s5 _ [] (tailAllowance caller before target values) a5 counter5 left5 scratch5
      (PSTRTMNatValue017.valueDigits_rawPayload values.length) stream5 potential
  let whole := headRun.append p6
  refine ⟨final,whole,finalDigits,a6,?_,?_,?_,?_,?_,counter6,zero6,width6,left6,scratch6,?_,finalMass,?_⟩
  · exact v6.trans (v5.trans (v4.trans ((congrArg (fun memory : Channels.Store C => memory.2) v3).trans (v2.trans v1))))
  · exact prior6.trans ((f5 15 (by decide) (by decide) (by decide) (by decide)).trans (prior4.trans prior2))
  · rw [f6 9 (by decide),f5 9 (by decide) (by decide) (by decide) (by decide),
      f4 9 (by decide) (by decide) (by decide),f3 9 (by decide) (by decide) (by decide),targetStored,
      f1 9 (by decide) (by decide) (by decide)]
  · rw [symbols,empty5]
  · simpa only [List.nil_append] using cursor6
  · intro slot safe
    have loopSafe : LoopFrame slot :=
      ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2.1,safe.2.2.2.2.2.2.1,safe.2.2.2.2.2.2.2⟩
    exact (f6 slot loopSafe).trans
      ((f5 slot safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.1 safe.2.2.2.2.2.2.1).trans
        ((f4 slot safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.2.2).trans
          ((f3 slot safe.1 safe.2.1 safe.2.2.2.2.2.2.2).trans
            ((f2 slot safe.2.2.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.2.2).trans
              (f1 slot safe.1 safe.2.1 safe.2.2.2.2.2.2.2)))))
  · have total := append_length_le headRun p6
    change (headRun.append p6).trace.length≤_
    unfold tailBudget
    omega

end B23_4_RatWordPrep.WordFields.Count
