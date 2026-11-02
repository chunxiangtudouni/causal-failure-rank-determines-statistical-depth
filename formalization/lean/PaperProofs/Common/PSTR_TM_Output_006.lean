module
public import PaperProofs.Common.PSTR_TM_Codec_001

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOutput006
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCodec001

theorem blankExtends_eq_of_true_end (xs ys : List Bool)
    (hys : ys.getLast? = some true) (h : Turing.BlankExtends xs ys) : xs = ys := by
  obtain ⟨n, rfl⟩ := h
  cases n with
  | zero => simp
  | succ n =>
    simp [List.getLast?_append, List.getLast?_replicate] at hys

/-- The final true delimiter makes exact encoded outputs unambiguous even
on TM0's quotient tape, where arbitrary trailing false bits are blanks. -/
theorem encodedTape_injective :
    Function.Injective (fun data : List Datum => Turing.ListBlank.mk (encode data)) := by
  intro xs ys h
  have hr : Turing.BlankRel (encode xs) (encode ys) := Quotient.exact h
  have hx : (encode xs).getLast? = some true := by simp [encode]
  have hy : (encode ys).getLast? = some true := by simp [encode]
  apply encode_injective
  rcases hr with hr | hr
  · exact blankExtends_eq_of_true_end _ _ hy hr
  · exact (blankExtends_eq_of_true_end _ _ hx hr).symm

theorem actionTape_injective (I : Instance) :
    Function.Injective (fun action : Action I => Turing.ListBlank.mk (encode (encodeAction action))) := by
  intro a b h
  exact encodeAction_injective I (encodedTape_injective h)

theorem historyTape_injective (I : Instance) :
    Function.Injective (fun history : List (VisibleEvent I) =>
      Turing.ListBlank.mk (encode (encodeHistory history))) := by
  intro a b h
  exact encodeHistory_injective I (encodedTape_injective h)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOutput006
