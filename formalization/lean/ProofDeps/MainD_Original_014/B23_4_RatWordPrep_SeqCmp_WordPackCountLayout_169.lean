module

public import B23_4_RatWordPrep_SeqCmp_WordPackMetadata_105
public import B23_4_RatWordPrep_SeqCmp_WordPackTable_107
public import B23_4_RatWordPrep_SeqCmp_WordPackCountQueues_168
public import B23_4_RatWordPrep_SeqCmp_WordPackLayout_108

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordPack.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def layoutWork (before : State C) (number : Nat) (target : Rat) (channels : List Rat) (symbols : List Nat) : Nat :=
  (before.stk 0).length+(before.stk 1).length+3*RatInput.Encoder.fieldSize target+
    3*(PSTRTMNatValue017.rawPayload number).length+32+
    naturalWork symbols.reverse+rationalWork channels.reverse+
    2*(PacketLists.rats channels []).length+4

theorem actual_layout (caller : Statement C) (before : State C) (number : Nat) (target : Rat)
    (channels : List Rat) (symbols : List Nat) (active : before.l=some (.clear0 0))
    (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (alphabet : before.stk 8=NatField.packet number []) (targetPacket : before.stk 9=RatInput.Encoder.packet target [])
    (table : before.stk 2=PacketLists.rats channels.reverse [])
    (word : before.stk 3=PacketLists.naturals symbols.reverse []) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 0=PacketLists.naturals symbols [] ∧
      final.stk 1=NatField.packet number (RatInput.Encoder.packet target []) ∧
      final.stk 2=PacketLists.rats channels [] ∧ final.stk 15=before.stk 15 ∧
      final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 8=[] ∧ final.stk 9=[] ∧ final.stk 13=[] ∧
      (∀ slot,LayoutFrame slot→final.stk slot=before.stk slot) ∧
      run.trace.length≤layoutWork before number target channels symbols := by
  obtain ⟨s1,p1,a1,v1,inputEmpty,metadata,alphabetEmpty,targetEmpty,temp1,frame1,time1⟩ :=
    actual_metadata caller before number target active scratch alphabet targetPacket
  have word1 : s1.stk 3=PacketLists.naturals symbols.reverse [] := (frame1 3 (by decide)).trans word
  obtain ⟨s2,p2,a2,v2,wordEmpty,wordOutput,temp2,frame2,time2⟩ := actual_word_queue caller symbols.reverse s1 a1 temp1 word1
  have wordReady : s2.stk 0=PacketLists.naturals symbols [] := by
    rw [wordOutput,List.reverse_reverse,inputEmpty]
  have table2 : s2.stk 2=PacketLists.rats channels.reverse [] :=
    (frame2 2 (by decide)).trans ((frame1 2 (by decide)).trans table)
  have empty13_2 : s2.stk 13=[] := (frame2 13 (by decide)).trans ((frame1 13 (by decide)).trans empty13)
  obtain ⟨s3,p3,a3,v3,tableEmpty,tableOutput,temp3,frame3,time3⟩ := actual_table_queue caller channels.reverse s2 a2 temp2 table2
  have tableReady : s3.stk 13=PacketLists.rats channels [] := by rw [tableOutput,List.reverse_reverse,empty13_2]
  have empty3_3 : s3.stk 3=[] := (frame3 3 (by decide)).trans wordEmpty
  obtain ⟨s4,p4,a4,v4,c4,t4,_b4⟩ := actual_cells caller .reverse13To3 reverse13Label s3 a3
    (by intro point different; change point≠4 at different
        simp only [reverse13Label,different,ite_false,program]; rfl)
  obtain ⟨final,p5,a5,v5,c5,t5,_b5⟩ := actual_cells caller .reverse3To2 reverse3Label s4 a4
    (by intro point different; change point≠4 at different
        simp only [reverse3Label,different,ite_false,program]; rfl)
  have frame4 (slot : RatInput.Stack) (n13 : slot≠13) (n3 : slot≠3) : s4.stk slot=s3.stk slot := by
    rw [c4]
    change Function.update (Function.update s3.stk 13 []) 3 _ slot=s3.stk slot
    rw [Function.update_of_ne n3,Function.update_of_ne n13]
  have frame5 (slot : RatInput.Stack) (n3 : slot≠3) (n2 : slot≠2) : final.stk slot=s4.stk slot := by
    rw [c5]
    change Function.update (Function.update s4.stk 3 []) 2 _ slot=s4.stk slot
    rw [Function.update_of_ne n2,Function.update_of_ne n3]
  have stable (slot : RatInput.Stack) (n0 : slot≠0) (n2 : slot≠2) (n3 : slot≠3) (n4 : slot≠4) (n13 : slot≠13) :
      final.stk slot=s1.stk slot :=
    (frame5 slot n3 n2).trans ((frame4 slot n13 n3).trans
      ((frame3 slot ⟨n13,n2,n4⟩).trans (frame2 slot ⟨n0,n3,n4⟩)))
  let whole := (((p1.append p2).append p3).append p4).append p5
  refine ⟨final,whole,a5,v5.trans (v4.trans (v3.trans (v2.trans v1))),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [frame5 0 (by decide) (by decide),frame4 0 (by decide) (by decide),frame3 0 (by decide)]
    exact wordReady
  · exact (stable 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans metadata
  · rw [c5,c4]
    change ((s3.stk 13).reverse++s3.stk 3).reverse++s3.stk 2=PacketLists.rats channels []
    rw [tableReady,empty3_3,tableEmpty]
    simp only [List.append_nil,List.reverse_reverse]
  · exact (stable 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (frame1 15 (by decide))
  · rw [c5]; rfl
  · exact (frame5 4 (by decide) (by decide)).trans ((frame4 4 (by decide) (by decide)).trans temp3)
  · exact (stable 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans alphabetEmpty
  · exact (stable 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans targetEmpty
  · rw [frame5 13 (by decide) (by decide),c4]; rfl
  · intro slot safe
    exact (stable slot safe.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.2.2).trans
      (frame1 slot ⟨safe.1,safe.2.1,safe.2.2.2.2.1,safe.2.2.2.2.2.1,safe.2.2.2.2.2.2.1⟩)
  · have time4 : p4.trace.length=(PacketLists.rats channels []).length+2 := by
      rw [t4]
      change (s3.stk 13).length+2=_
      rw [tableReady]
    have time5 : p5.trace.length=(PacketLists.rats channels []).length+2 := by
      rw [t5,c4]
      change ((s3.stk 13).reverse++s3.stk 3).length+2=_
      rw [tableReady,empty3_3]
      simp only [List.append_nil,List.length_reverse]
    have j2 := p1.append_length_le p2
    have j3 := (p1.append p2).append_length_le p3
    have j4 := ((p1.append p2).append p3).append_length_le p4
    have j5 := (((p1.append p2).append p3).append p4).append_length_le p5
    change ((((p1.append p2).append p3).append p4).append p5).trace.length≤_
    unfold layoutWork
    omega

end B23_4_RatWordPrep.WordPack.Count
