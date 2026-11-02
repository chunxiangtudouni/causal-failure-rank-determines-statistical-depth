module

public import B23_4_RatWordPrep_SeqCmp_WordFoldLookup_119
public import B23_4_RatWordPrep_SeqCmp_WordFoldBinary_120
public import B23_4_RatWordPrep_SeqCmp_WordFoldConsume_121

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

instance consumeFrameDecidable (slot : RatInput.Stack) : Decidable (ConsumeFrame slot) := by unfold ConsumeFrame; infer_instance

theorem owned_lookup {before final : State C} (clean : ∀ slot,Owned slot→before.stk slot=[])
    (scratch : final.stk 4=[]) (empty13 : final.stk 13=[])
    (frame : ∀ slot,Lookup.LookupFrame slot→final.stk slot=before.stk slot) :
    ∀ slot,Owned slot→final.stk slot=[] := by
  intro slot selected
  fin_cases slot <;> first
  | exact scratch
  | exact empty13
  | exact (frame _ (by decide)).trans (clean _ (by decide))
  | simp [Owned] at selected

def stepOdds (E : BinaryExperiment) (odds : Rat) (symbol : Fin E.alphabetSize) : Rat :=
  (E.channel true symbol/E.channel false symbol)*odds

/-- One real word symbol: two table-restoring lookups, actual normalized
division and multiplication, then paid physical consumption of query0.
No probability/odds/branch/width/path/fuel answer is provided to source. -/
theorem actual_symbol (caller : Statement C) (E : BinaryExperiment) (symbol : Fin E.alphabetSize)
    (before : State C) (odds : Rat) (queryTail metadataTail : List Bool)
    (active : before.l=some (.falseLookup .boot))
    (query : before.stk 0=NatField.packet symbol.val queryTail)
    (metadata : before.stk 1=NatField.packet E.alphabetSize metadataTail)
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) [])
    (packet : before.stk 15=RatInput.Encoder.packet odds [])
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some .check ∧ final.var.2.2.2=before.var.2.2.2 ∧ final.stk 0=queryTail ∧
      final.stk 1=before.stk 1 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet (stepOdds E odds symbol) [] ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) := by
  obtain ⟨s1,p1,a1,_aux1,v1,table1,output1,empty13_1,temp1,frame1⟩ := actual_lookup false caller E symbol
    before queryTail metadataTail active (owned 4 (by decide)) (owned 13 (by decide)) query metadata table
  have owned1 := owned_lookup owned temp1 empty13_1 frame1
  have query1 : s1.stk 0=NatField.packet symbol.val queryTail := (frame1 0 (by decide)).trans query
  have metadata1 : s1.stk 1=NatField.packet E.alphabetSize metadataTail := (frame1 1 (by decide)).trans metadata
  obtain ⟨s2,p2,a2,_aux2,v2,table2,output2,empty13_2,temp2,frame2⟩ := actual_lookup true caller E symbol
    s1 queryTail metadataTail a1 temp1 empty13_1 query1 metadata1 (table1.trans table)
  have owned2 := owned_lookup owned1 temp2 empty13_2 frame2
  have pair2 : s2.stk 15=RatPair.input (E.channel true symbol) (E.channel false symbol)
      (RatInput.Encoder.packet odds []) := by
    rw [output2,output1,packet]
    exact RatPair.two_packet_format _ _ _
  obtain ⟨s3,p3,a3,v3,ratioPacket,scratch3,owned3,frame3,_time3⟩ := actual_ratio caller s2
    (E.channel true symbol) (E.channel false symbol) (RatInput.Encoder.packet odds []) a2 pair2 owned2
  have pair3 : s3.stk 15=RatPair.input (E.channel true symbol/E.channel false symbol) odds [] :=
    ratioPacket.trans (RatPair.two_packet_format _ _ _)
  obtain ⟨s4,p4,a4,v4,resultPacket,scratch4,owned4,frame4,_time4⟩ := actual_multiply caller s3
    (E.channel true symbol/E.channel false symbol) odds [] a3 pair3 owned3
  have query4 : s4.stk 0=NatField.packet symbol.val queryTail :=
    (frame4 0 (by decide)).trans ((frame3 0 (by decide)).trans ((frame2 0 (by decide)).trans query1))
  obtain ⟨final,p5,a5,v5,queryFinal,empty3,empty4,frame5,_time5⟩ := actual_consume caller s4 symbol.val queryTail
    a4 query4 (owned4 4 (by decide)) (owned4 3 (by decide))
  let whole := (((p1.append p2).append p3).append p4).append p5
  refine ⟨final,whole,a5,?_,queryFinal,?_,?_,?_,?_,?_⟩
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

end B23_4_RatWordPrep.WordFold
