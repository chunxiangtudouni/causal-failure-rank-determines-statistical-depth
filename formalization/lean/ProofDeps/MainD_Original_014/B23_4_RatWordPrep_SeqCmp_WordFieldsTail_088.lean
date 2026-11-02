module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsLoop_087
public import B23_4_RatWordPrep_SeqCmp_WordFieldsCounter_086

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

instance loopFrameDecidable (slot : RatInput.Stack) : Decidable (LoopFrame slot) := by
  unfold LoopFrame
  infer_instance

def TailFrame (slot : RatInput.Stack) : Prop :=
  slot≠0 ∧ slot≠1 ∧ slot≠3 ∧ slot≠4 ∧ slot≠9 ∧ slot≠10 ∧ slot≠11 ∧ slot≠15

instance tailFrameDecidable (slot : RatInput.Stack) : Decidable (TailFrame slot) := by
  unfold TailFrame
  infer_instance

theorem actual_tail (caller : Statement C) (before : State C) (target : Rat) (values : List Nat)
    (active : before.l=some (.target .boot)) (empty3 : before.stk 3=[]) (scratch : before.stk 4=[])
    (stream : ListBlank.mk (before.stk 0)=ListBlank.mk
      (encodeDatum (.rational target)++encodeDatum (.natural values.length)++fields values++[true])) :
    ∃ (final : State C) (_run : Segment caller before final) (finalDigits : List Bool),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 15=before.stk 15 ∧ final.stk 9=RatInput.Encoder.packet target (before.stk 9) ∧
      final.stk 3=archived values [] ∧ ListBlank.mk (final.stk 0)=ListBlank.mk [true] ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(PSTRTMNatValue017.rawPayload values.length).length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      ∀ slot,TailFrame slot→final.stk slot=before.stk slot := by
  have targetStream : ListBlank.mk (before.stk 0)=ListBlank.mk
      (encodeDatum (.rational target)++(encodeDatum (.natural values.length)++fields values)++[true]) := by
    simpa only [List.append_assoc] using stream
  obtain ⟨s1,p1,a1,v1,targetPacket,cursor1,f1,_t1⟩ :=
    actual_target caller before target (encodeDatum (.natural values.length)++fields values) active targetStream
  have scratch1 : s1.stk 4=[] := (f1 4 (by decide) (by decide) (by decide)).trans scratch
  obtain ⟨s2,p2,a2,v2,prior2,targetStored,scratch2,f2,_t2⟩ :=
    actual_target_move caller s1 target (before.stk 15) a1 targetPacket scratch1
  have countStream : ListBlank.mk (s2.stk 0)=
      ListBlank.mk (encodeDatum (.natural values.length)++fields values++[true]) := by
    rw [f2 0 (by decide) (by decide) (by decide)]
    exact cursor1
  obtain ⟨s3,p3,a3,v3,countPacket,cursor3,f3,_t3⟩ :=
    actual_natural false caller s2 values.length (fields values) a2 countStream
  have scratch3 : s3.stk 4=[] := (f3 4 (by decide) (by decide) (by decide)).trans scratch2
  obtain ⟨s4,p4,a4,v4,prior4,countStored,scratch4,f4,_t4⟩ :=
    actual_natural_move false caller s3 values.length (s2.stk 15) a3 countPacket scratch3
  have packet3 : s4.stk 3=NatField.packet values.length [] := by
    rw [countStored,f3 3 (by decide) (by decide) (by decide),
      f2 3 (by decide) (by decide) (by decide),f1 3 (by decide) (by decide) (by decide),empty3]
  obtain ⟨s5,p5,a5,v5,counter5,left5,scratch5,f5,_t5⟩ :=
    actual_build caller s4 values.length [] a4 packet3 scratch4
  obtain ⟨s6,p6,a6,v6,empty6,f6⟩ := actual_clear caller s5 a5
  have counter6 : s6.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (PSTRTMNatValue017.rawPayload values.length) :=
    (f6 10 (by decide)).trans counter5
  have left6 : s6.stk 11=[false] := (f6 11 (by decide)).trans left5
  have scratch6 : s6.stk 4=[] := (f6 4 (by decide)).trans scratch5
  have stream6 : ListBlank.mk (s6.stk 0)=ListBlank.mk (fields values++[]++[true]) := by
    rw [f6 0 (by decide),f5 0 (by decide) (by decide) (by decide),f4 0 (by decide) (by decide) (by decide)]
    simpa only [List.append_nil] using cursor3
  obtain ⟨final,p7,finalDigits,a7,v7,prior7,symbols,cursor7,counter7,zero7,width7,left7,scratch7,f7⟩ :=
    actual_loop caller values s6 _ [] a6 counter6 left6 scratch6
      (PSTRTMNatValue017.valueDigits_rawPayload values.length) stream6
  let whole := (((((p1.append p2).append p3).append p4).append p5).append p6).append p7
  refine ⟨final,whole,finalDigits,a7,?_,?_,?_,?_,?_,counter7,zero7,width7,left7,scratch7,?_⟩
  · exact v7.trans (v6.trans (v5.trans (v4.trans
      ((congrArg (fun memory : Channels.Store C => memory.2) v3).trans (v2.trans v1)))))
  · exact prior7.trans ((f6 15 (by decide)).trans
      ((f5 15 (by decide) (by decide) (by decide)).trans (prior4.trans prior2)))
  · rw [f7 9 (by decide),f6 9 (by decide),f5 9 (by decide) (by decide) (by decide),
      f4 9 (by decide) (by decide) (by decide),f3 9 (by decide) (by decide) (by decide),targetStored,
      f1 9 (by decide) (by decide) (by decide)]
  · rw [symbols,empty6]
  · simpa only [List.nil_append] using cursor7
  · intro slot safe
    have loopSafe : LoopFrame slot :=
      ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2.1,safe.2.2.2.2.2.2.1,safe.2.2.2.2.2.2.2⟩
    exact (f7 slot loopSafe).trans ((f6 slot safe.2.2.1).trans
      ((f5 slot safe.2.2.2.1 safe.2.2.2.2.2.1 safe.2.2.2.2.2.2.1).trans
        ((f4 slot safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.2.2).trans
          ((f3 slot safe.1 safe.2.1 safe.2.2.2.2.2.2.2).trans
            ((f2 slot safe.2.2.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.2.2).trans
              (f1 slot safe.1 safe.2.1 safe.2.2.2.2.2.2.2))))))

end B23_4_RatWordPrep.WordFields
