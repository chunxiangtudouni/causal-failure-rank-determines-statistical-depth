module

public import B23_4_RatWordPrep_SeqCmp_WordFoldCountLookup_182
public import B23_4_RatWordPrep_SeqCmp_WordFoldCountMass_183
public import B23_4_RatWordPrep_SeqCmp_WordBinaryScale_146
public import B23_4_RatWordPrep_SeqCmp_WordFoldBinary_120
public import B23_4_RatWordPrep_SeqCmp_WordFoldConsume_121

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def firstLookup (number bound : Nat) : Nat :=
  Lookup.Count.uniformWork false (.halt : Lookup.Statement C) number bound (massBudget bound)
noncomputable def firstMass (caller : Statement C) (number bound : Nat) : Nat :=
  massBudget bound+pushCap caller*firstLookup (C:=C) number bound
noncomputable def secondLookup (caller : Statement C) (number bound : Nat) : Nat :=
  Lookup.Count.uniformWork true (.halt : Lookup.Statement C) number bound (firstMass caller number bound)
noncomputable def secondMass (caller : Statement C) (number bound : Nat) : Nat :=
  firstMass caller number bound+pushCap caller*secondLookup caller number bound
noncomputable def ratioMass (caller : Statement C) (number bound : Nat) : Nat :=
  secondMass caller number bound+32*(bound+1)^2
noncomputable def symbolBudget (caller : Statement C) (number bound : Nat) : Nat :=
  firstLookup (C:=C) number bound+secondLookup caller number bound+
  (7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.divCoefficient+137)*(secondMass caller number bound+1)^4+
  (7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.mulCoefficient+137)*(ratioMass caller number bound+1)^4+
  6*(bound+1)+12

/-- One real word symbol: two table-restoring lookups, actual normalized
division and multiplication, then paid physical consumption of query0.
No probability/odds/branch/width/path/fuel answer is provided to source. -/
theorem actual_symbol (caller : Statement C) (E : BinaryExperiment) (symbol : Fin E.alphabetSize)
    (target : Rat) (word : E.StoppedWord) (before : State C) (odds : Rat) (queryTail metadataTail : List Bool)
    (active : before.l=some (.falseLookup .boot))
    (query : before.stk 0=NatField.packet symbol.val queryTail)
    (metadata : before.stk 1=NatField.packet E.alphabetSize metadataTail)
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) [])
    (packet : before.stk 15=RatInput.Encoder.packet odds [])
    (owned : ∀ slot,Owned slot→before.stk slot=[])
    (safe : CounterSafe (wordInput E target word).length before.stk)
    (massBound : RatInput.occupied before.stk≤massBudget (wordInput E target word).length)
    (widthBound : RatInput.Encoder.fieldSize odds≤8*((wordInput E target word).length+1)^2) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .check ∧ final.var.2.2.2=before.var.2.2.2 ∧ final.stk 0=queryTail ∧
      final.stk 1=before.stk 1 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet (stepOdds E odds symbol) [] ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      CounterSafe (wordInput E target word).length final.stk ∧
      run.trace.length≤symbolBudget caller E.alphabetSize (wordInput E target word).length := by
  obtain ⟨s1,p1,a1,_aux1,v1,table1,output1,empty13_1,temp1,frame1,_counter1,time1⟩ := actual_lookup false caller E symbol target word
    before queryTail metadataTail active (owned 4 (by decide)) (owned 13 (by decide)) query metadata table
  have owned1 := owned_lookup owned temp1 empty13_1 frame1
  have query1 : s1.stk 0=NatField.packet symbol.val queryTail := (frame1 0 (by decide)).trans query
  have metadata1 : s1.stk 1=NatField.packet E.alphabetSize metadataTail := (frame1 1 (by decide)).trans metadata
  obtain ⟨s2,p2,a2,_aux2,v2,table2,output2,empty13_2,temp2,frame2,counter2,time2⟩ := actual_lookup true caller E symbol target word
    s1 queryTail metadataTail a1 temp1 empty13_1 query1 metadata1 (table1.trans table)
  have owned2 := owned_lookup owned1 temp2 empty13_2 frame2
  have pair2 : s2.stk 15=RatPair.input (E.channel true symbol) (E.channel false symbol)
      (RatInput.Encoder.packet odds []) := by
    rw [output2,output1,packet]
    exact RatPair.two_packet_format _ _ _
  obtain ⟨s3,p3,a3,v3,ratioPacket,scratch3,owned3,frame3,time3⟩ := actual_ratio caller s2
    (E.channel true symbol) (E.channel false symbol) (RatInput.Encoder.packet odds []) a2 pair2 owned2
  have pair3 : s3.stk 15=RatPair.input (E.channel true symbol/E.channel false symbol) odds [] :=
    ratioPacket.trans (RatPair.two_packet_format _ _ _)
  obtain ⟨s4,p4,a4,v4,resultPacket,scratch4,owned4,frame4,time4⟩ := actual_multiply caller s3
    (E.channel true symbol/E.channel false symbol) odds [] a3 pair3 owned3
  have query4 : s4.stk 0=NatField.packet symbol.val queryTail :=
    (frame4 0 (by decide)).trans ((frame3 0 (by decide)).trans ((frame2 0 (by decide)).trans query1))
  obtain ⟨final,p5,a5,v5,queryFinal,empty3,empty4,frame5,time5⟩ := actual_consume caller s4 symbol.val queryTail
    a4 query4 (owned4 4 (by decide)) (owned4 3 (by decide))
  let B := (wordInput E target word).length
  have paid1 : p1.trace.length≤firstLookup (C:=C) E.alphabetSize B :=
    time1.trans (Lookup.Count.uniformWork_mono false (.halt : Lookup.Statement C) E.alphabetSize B massBound)
  have mass1 := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller)
    p1.trace before (RatInput.occupied before.stk) p1.first p1.chain (Nat.le_refl _) s1 (List.mem_of_getLast? p1.last)
  have room1 : RatInput.occupied s1.stk≤firstMass caller E.alphabetSize B :=
    mass1.trans (Nat.add_le_add massBound (Nat.mul_le_mul_left _ paid1))
  have paid2 : p2.trace.length≤secondLookup caller E.alphabetSize B :=
    time2.trans (Lookup.Count.uniformWork_mono true (.halt : Lookup.Statement C) E.alphabetSize B room1)
  have mass2 := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller)
    p2.trace s1 (RatInput.occupied s1.stk) p2.first p2.chain (Nat.le_refl _) s2 (List.mem_of_getLast? p2.last)
  have room2 : RatInput.occupied s2.stk≤secondMass caller E.alphabetSize B :=
    mass2.trans (Nat.add_le_add room1 (Nat.mul_le_mul_left _ paid2))
  let divCurrent : WordFinish.State C := ⟨none,s2.var,s2.stk⟩
  have divTime := WordFinish.Resources.binary_time_le_mass RatMulDiv.divCoefficient divCurrent
    (E.channel true symbol) (E.channel false symbol) (RatInput.Encoder.packet odds []) pair2
  have paid3 := time3.trans (divTime.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right room2 1) 4)))
  have trueWidth : RatInput.Encoder.fieldSize (E.channel true symbol)≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.channel_width_le_input E target word true symbol
  have falseWidth : RatInput.Encoder.fieldSize (E.channel false symbol)≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.channel_width_le_input E target word false symbol
  have ratioWidth : RatInput.Encoder.fieldSize (E.channel true symbol/E.channel false symbol)≤2*B :=
    (ratio_field _ _).trans (by omega)
  have ratioCells : (s3.stk 15).length≤32*(B+1)^2 := by
    rw [ratioPacket,RatInput.Encoder.packet_length,RatInput.Encoder.packet_length]
    change RatInput.Encoder.fieldSize odds≤8*(B+1)^2 at widthBound
    simp only [List.length_nil]
    nlinarith
  have ratioPhysical := binary_mass s2.stk s3.stk owned2 owned3 scratch3 frame3
  have room3 : RatInput.occupied s3.stk≤ratioMass caller E.alphabetSize B :=
    ratioPhysical.trans (Nat.add_le_add room2 ratioCells)
  let mulCurrent : WordFinish.State C := ⟨none,s3.var,s3.stk⟩
  have mulTime := WordFinish.Resources.binary_time_le_mass RatMulDiv.mulCoefficient mulCurrent
    (E.channel true symbol/E.channel false symbol) odds [] pair3
  have paid4 := time4.trans (mulTime.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right room3 1) 4)))
  have alphabet := WordFinish.Resources.alphabet_le_input E target word
  have rawWidth := (WordFinish.Resources.rawPayload_le_number symbol.val).trans
    (Nat.add_le_add_right (symbol.isLt.le.trans alphabet) 1)
  have paid5 : p5.trace.length≤6*(B+1)+12 := time5.trans (by omega)
  let whole := (((p1.append p2).append p3).append p4).append p5
  refine ⟨final,whole,a5,?_,queryFinal,?_,?_,?_,?_,?_,?_,?_⟩
  · exact v5.trans ((congrArg (fun memory : WordPack.Store C => memory.2.2) v4).trans
      ((congrArg (fun memory : WordPack.Store C => memory.2.2) v3).trans (v2.trans v1)))
  · exact (frame5 1 (by decide)).trans ((frame4 1 (by decide)).trans
      ((frame3 1 (by decide)).trans ((frame2 1 (by decide)).trans (frame1 1 (by decide)))))
  · exact (frame5 2 (by decide)).trans ((frame4 2 (by decide)).trans
      ((frame3 2 (by decide)).trans (table2.trans table1)))
  · exact (frame5 15 (by decide)).trans resultPacket
  · exact (frame5 7 (by decide)).trans (scratch4.trans
      (scratch3.trans ((frame2 7 (by decide)).trans (frame1 7 (by decide)))))
  · intro slot selected
    fin_cases slot <;> first
    | exact empty3
    | exact empty4
    | exact (frame5 _ (by decide)).trans (owned4 _ (by decide))
    | simp [Owned] at selected
  · obtain ⟨digits,right,width,left⟩ := counter2
    have p10 : final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits :=
      (frame5 10 (by decide)).trans ((frame4 10 (by decide)).trans ((frame3 10 (by decide)).trans right))
    have p11 : final.stk 11=[false] :=
      (frame5 11 (by decide)).trans ((frame4 11 (by decide)).trans ((frame3 11 (by decide)).trans left))
    refine ⟨?_,p11,?_⟩
    · exact (frame5 7 (by decide)).trans (scratch4.trans (scratch3.trans
        ((frame2 7 (by decide)).trans ((frame1 7 (by decide)).trans safe.1))))
    · rw [p10,RootB234.RuntimeCounter.Round.packet_length,width]
      omega
  · have j2 := p1.append_length_le p2
    have j3 := (p1.append p2).append_length_le p3
    have j4 := ((p1.append p2).append p3).append_length_le p4
    have j5 := (((p1.append p2).append p3).append p4).append_length_le p5
    change ((((p1.append p2).append p3).append p4).append p5).trace.length≤_
    change p3.trace.length≤(7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.divCoefficient+137)*
      (secondMass caller E.alphabetSize B+1)^4 at paid3
    change p4.trace.length≤(7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.mulCoefficient+137)*
      (ratioMass caller E.alphabetSize B+1)^4 at paid4
    change _≤symbolBudget caller E.alphabetSize B
    unfold symbolBudget
    omega

end B23_4_RatWordPrep.WordFold.Count
