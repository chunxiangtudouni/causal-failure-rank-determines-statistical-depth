module

public import B23_4_RatWordPrep_SeqCmp_LookupCountScale_180
public import B23_4_RatWordPrep_SeqCmp_LookupChannel_101

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

/-- Actual physical selection of E.channel truth symbol. The only table
and count hypotheses identify the caller's existing bank. The caller
supplies no selected value, branch, path, width, fuel or comparator bit. -/
theorem actual_channel (truth : Bool) (caller : Statement C) (E : BinaryExperiment)
    (symbol : Fin E.alphabetSize) (target : Rat) (word : E.StoppedWord) (before : State C) (queryTail metadataTail : List Bool)
    (active : before.l=some .boot) (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (query : before.stk 0=NatField.packet symbol.val queryTail)
    (metadata : before.stk 1=NatField.packet E.alphabetSize metadataTail)
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) []) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet (E.channel truth symbol) (before.stk 15) ∧
      final.stk 13=[] ∧ final.stk 4=[] ∧
      (∀ slot,LookupFrame slot→final.stk slot=before.stk slot) ∧
      (∃ digits,final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits ∧
        digits.length=(PSTRTMNatValue017.rawPayload symbol.val).length ∧ final.stk 11=[false]) ∧
      run.trace.length≤uniformWork truth caller E.alphabetSize (wordInput E target word).length (RatInput.occupied before.stk) := by
  have rowLength : (PacketLists.row E false).length=E.alphabetSize := by
    simp only [PacketLists.row,List.length_map,List.length_finRange]
  have metadataActual : before.stk 1=NatField.packet (PacketLists.row E false).length metadataTail := by
    rw [rowLength]
    exact metadata
  have rowFields (truth : Bool) : ∀ q∈PacketLists.row E truth,RatInput.Encoder.fieldSize q≤(wordInput E target word).length := by
    intro q member
    obtain ⟨position,_present,rfl⟩ := List.mem_map.mp member
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.channel_width_le_input E target word truth position
  have field (truth : Bool) : RatInput.Encoder.fieldSize (E.channel truth symbol)≤(wordInput E target word).length := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.channel_width_le_input E target word truth symbol
  cases truth with
  | false =>
    obtain ⟨front,back,split,length⟩ := PacketLists.row_split E false symbol
    have queryActual : before.stk 0=NatField.packet front.length queryTail := by rw [length]; exact query
    have tableActual : before.stk 2=PacketLists.rats
        ((if false then PacketLists.row E false else [])++front)
        (RatInput.Encoder.packet (E.channel false symbol)
          (PacketLists.rats back (PacketLists.rats (PacketLists.row E true) []))) := by
      rw [table,PacketLists.channel_rows,split]
      change PacketLists.rats ((front++E.channel false symbol::back)++PacketLists.row E true) []=_
      rw [PacketLists.rats_append,PacketLists.rats_append]
      rfl
    obtain ⟨final,run,port,context,unchanged,output,final13,finalScratch,frame,counterFinal,time⟩ :=
      actual false caller (PacketLists.row E false) front before (E.channel false symbol)
        queryTail metadataTail _ active scratch empty13 queryActual metadataActual tableActual
    have frontFields : ∀ q∈front,RatInput.Encoder.fieldSize q≤(wordInput E target word).length := by
      intro q member
      apply rowFields false q
      rw [split]
      exact List.mem_append_left _ member
    have frontCount : front.length≤E.alphabetSize := by rw [length]; exact symbol.isLt.le
    have paid := actualWork_upper false caller (PacketLists.row E false) front (E.channel false symbol)
      E.alphabetSize (wordInput E target word).length (RatInput.occupied before.stk)
      (by rw [rowLength]) frontCount (rowFields false) frontFields (field false)
    have finalCounter : ∃ digits,final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits ∧
        digits.length=(PSTRTMNatValue017.rawPayload symbol.val).length ∧ final.stk 11=[false] := by
      simpa only [length] using counterFinal
    exact ⟨final,run,port,context,unchanged,output,final13,finalScratch,frame,finalCounter,time.trans paid⟩
  | true =>
    obtain ⟨front,back,split,length⟩ := PacketLists.row_split E true symbol
    have queryActual : before.stk 0=NatField.packet front.length queryTail := by rw [length]; exact query
    have tableActual : before.stk 2=PacketLists.rats
        ((if true then PacketLists.row E false else [])++front)
        (RatInput.Encoder.packet (E.channel true symbol) (PacketLists.rats back [])) := by
      rw [table,PacketLists.channel_rows,split]
      change PacketLists.rats (PacketLists.row E false++(front++E.channel true symbol::back)) []=
        PacketLists.rats (PacketLists.row E false++front)
          (RatInput.Encoder.packet (E.channel true symbol) (PacketLists.rats back []))
      rw [PacketLists.rats_append,PacketLists.rats_append,PacketLists.rats_append]
      rfl
    obtain ⟨final,run,port,context,unchanged,output,final13,finalScratch,frame,counterFinal,time⟩ :=
      actual true caller (PacketLists.row E false) front before (E.channel true symbol)
        queryTail metadataTail _ active scratch empty13 queryActual metadataActual tableActual
    have frontFields : ∀ q∈front,RatInput.Encoder.fieldSize q≤(wordInput E target word).length := by
      intro q member
      apply rowFields true q
      rw [split]
      exact List.mem_append_left _ member
    have frontCount : front.length≤E.alphabetSize := by rw [length]; exact symbol.isLt.le
    have paid := actualWork_upper true caller (PacketLists.row E false) front (E.channel true symbol)
      E.alphabetSize (wordInput E target word).length (RatInput.occupied before.stk)
      (by rw [rowLength]) frontCount (rowFields false) frontFields (field true)
    have finalCounter : ∃ digits,final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits ∧
        digits.length=(PSTRTMNatValue017.rawPayload symbol.val).length ∧ final.stk 11=[false] := by
      simpa only [length] using counterFinal
    exact ⟨final,run,port,context,unchanged,output,final13,finalScratch,frame,finalCounter,time.trans paid⟩

end B23_4_RatWordPrep.Lookup.Count
