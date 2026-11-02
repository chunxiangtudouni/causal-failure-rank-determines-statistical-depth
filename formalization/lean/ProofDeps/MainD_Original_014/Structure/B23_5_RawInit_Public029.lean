module
public import Structure.B23_5_RawInit_PaddedArchive028
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Public029
open Turing RationalControllerComputation

theorem empty_fin16 : ∃ path final,
    Runs PaddedFront.machine (encode []) path final ∧ final.q=PaddedFront.haltPort ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode [])) ∧
      path.length≤32000*((encode []).length+1)^3 ∧ ∀ clock,
        visitedSpace PaddedFront.machine (encode []).length (path.take clock)≤
          100000*((encode []).length+1)^3 := PaddedFront.actual []

theorem nonempty_archive (data : List Datum) (nonempty : data≠[]) : ∃ digits path final,
    Runs PaddedFront.machine (encode data) path final ∧ final.q=PaddedFront.haltPort ∧
      final.Tape=PSTRSymbolicCursorArchive.archiveTape data
        (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) digits [] true ∧
      2≤digits.length ∧ digits.length≤(PSTRTMNatValue017.rawPayload data.length).length+1 ∧
      PSTRTMIncrement009.valueDigits digits≤1 ∧ path.length≤32000*((encode data).length+1)^3 ∧
      ∀ clock, visitedSpace PaddedFront.machine (encode data).length (path.take clock)≤
        100000*((encode data).length+1)^3 := PaddedArchive.actual data nonempty

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Public029
