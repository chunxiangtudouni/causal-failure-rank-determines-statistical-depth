module
public import Structure.B23_5_RawInit_PaddedFront027

/-! Uniform producer-facing nonempty archive ABI. Actual singleton padding
supplies two work digits; other sizes keep the original width. Original
count bits stay exact, work value is at most one, and no new original-input
qualification or host tape injection is introduced. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.PaddedArchive
open Turing RationalControllerComputation
open RationalControllerComputation.PSTRSymbolicCursorArchive
open RationalControllerComputation.PSTRSymbolicLaneArchive
open RationalControllerComputation.PSTRTMIncrement009
open RationalControllerComputation.PSTRTMThresholdCountdownCode164

theorem width_two (count : Nat) (room : 2≤count) :
    2≤(PSTRTMNatValue017.rawPayload count).length := by
  have nonzero : count≠0 := by omega
  have logRoom : 1≤Nat.log2 count := (Nat.le_log2 nonzero).mpr (by simpa using room)
  simpa only [PSTRTMNatValue017.rawPayload,List.length_ofFn,natBits] using
    Nat.add_le_add_right logRoom 1

theorem shape (data : List Datum) (nonempty : data≠[]) (tape : Tape Bool)
    (output : PaddedFront.outcome data tape) :
    ∃ digits, tape=archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) digits [] true ∧
      2≤digits.length ∧ digits.length≤(PSTRTMNatValue017.rawPayload data.length).length+1 ∧
      valueDigits digits≤1 := by
  rcases data with _ | ⟨first,data⟩
  · exact False.elim (nonempty rfl)
  rcases data with _ | ⟨second,data⟩
  · refine ⟨[true,false],?_,by decide,?_,by decide⟩
    · change tape=Tape.mk₂ _ [true] at output
      simpa only [archiveTape,allDatumPairs_cells,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.length_cons,List.length_nil,SingletonPad.header,HeaderCopy.bank,List.append_assoc] using output
    · change 2≤(PSTRTMNatValue017.rawPayload 1).length+1
      decide
  rcases data with _ | ⟨third,data⟩
  · refine ⟨predDigits (predDigits (PSTRTMNatValue017.rawPayload 2)),?_,?_,?_,by decide⟩
    · change tape=Tape.mk₂ (countedPairLeft first second []) [true] at output
      simpa only [archiveTape,allDatumPairs_cells,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.reverse_append,List.length_cons,List.length_nil,countedPairLeft,HeaderCopy.bank,
        List.append_assoc] using output
    · simpa only [pred_length] using width_two 2 (by decide)
    · simp only [pred_length,List.length_cons,List.length_nil,Nat.reduceAdd]
      omega
  rcases data with _ | ⟨fourth,later⟩
  · refine ⟨predDigits (predDigits (PSTRTMNatValue017.rawPayload 3)),?_,?_,?_,by decide⟩
    · change tape=Tape.mk₂ (_++countedPairLeft first second [third]) [true] at output
      simpa only [archiveTape,allDatumPairs_cells,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.reverse_append,List.length_cons,List.length_nil,countedPairLeft,HeaderCopy.bank,
        List.append_assoc] using output
    · simpa only [pred_length] using width_two 3 (by decide)
    · simp only [pred_length,List.length_cons,List.length_nil,Nat.reduceAdd]
      omega
  obtain ⟨digits,tapeEq,zero,width⟩:=output
  refine ⟨digits,tapeEq,?_,?_,by omega⟩
  · rw [width]
    exact width_two _ (by simp only [List.length_cons]; omega)
  · rw [width]
    omega

theorem actual (data : List Datum) (nonempty : data≠[]) : ∃ digits path final,
    Runs PaddedFront.machine (encode data) path final ∧ final.q=PaddedFront.haltPort ∧
      final.Tape=archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) digits [] true ∧
      2≤digits.length ∧ digits.length≤(PSTRTMNatValue017.rawPayload data.length).length+1 ∧
      valueDigits digits≤1 ∧ path.length≤32000*((encode data).length+1)^3 ∧ ∀ clock,
        visitedSpace PaddedFront.machine (encode data).length (path.take clock)≤
          100000*((encode data).length+1)^3 := by
  obtain ⟨path,final,run,port,output,time,space⟩:=PaddedFront.actual data
  obtain ⟨digits,tape,lower,upper,value⟩:=shape data nonempty final.Tape output
  exact ⟨digits,path,final,run,port,tape,lower,upper,value,time,space⟩

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.PaddedArchive
