module

public import B23_4_RatWordPrep_SeqCmp_LookupActual_100

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

/-- Actual physical selection of E.channel truth symbol. The only table
and count hypotheses identify the caller's existing bank. The caller
supplies no selected value, branch, path, width, fuel or comparator bit. -/
theorem actual_channel (truth : Bool) (caller : Statement C) (E : BinaryExperiment)
    (symbol : Fin E.alphabetSize) (before : State C) (queryTail metadataTail : List Bool)
    (active : before.l=some .boot) (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (query : before.stk 0=NatField.packet symbol.val queryTail)
    (metadata : before.stk 1=NatField.packet E.alphabetSize metadataTail)
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) []) :
    ∃ (final : State C) (_run : Segment truth caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet (E.channel truth symbol) (before.stk 15) ∧
      final.stk 13=[] ∧ final.stk 4=[] ∧
      ∀ slot,LookupFrame slot→final.stk slot=before.stk slot := by
  have rowLength : (PacketLists.row E false).length=E.alphabetSize := by
    simp only [PacketLists.row,List.length_map,List.length_finRange]
  have metadataActual : before.stk 1=NatField.packet (PacketLists.row E false).length metadataTail := by
    rw [rowLength]
    exact metadata
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
    exact actual false caller (PacketLists.row E false) front before (E.channel false symbol)
      queryTail metadataTail _ active scratch empty13 queryActual metadataActual tableActual
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
    exact actual true caller (PacketLists.row E false) front before (E.channel true symbol)
      queryTail metadataTail _ active scratch empty13 queryActual metadataActual tableActual

end B23_4_RatWordPrep.Lookup
