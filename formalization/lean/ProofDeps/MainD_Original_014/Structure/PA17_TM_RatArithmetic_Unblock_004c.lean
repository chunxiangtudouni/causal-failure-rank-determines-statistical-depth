module
public import Structure.PA17_TM_RatArithmetic_Unblock_004b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004
open PSTRTMUnblock018

theorem framed_time_le (archive digits suffix : List Bool) :
    (framedTrace archive digits suffix).length ≤ 32*(digits.length+1)^2 := by
  rw [framed_length]
  nlinarith

theorem framed_visitedSpace_le (archive digits suffix : List Bool) (inputLength : Nat) :
    visitedSpace unblockMachine inputLength (framedTrace archive digits suffix) ≤
      inputLength+64*(digits.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le unblockMachine inputLength (framedTrace archive digits suffix)
  rw [framed_length] at hs
  nlinarith

theorem rawWord_payload (n : Nat) : PSTRTMUnblockTrace019.rawWord (PSTRTMNatValue017.rawPayload n) = encodeNat n := by
  simp [PSTRTMUnblockTrace019.rawWord,PSTRTMNatValue017.rawPayload,encodeNat,List.append_assoc]

theorem originalNat_runsFrom (n : Nat) (archive suffix : List Bool) :
    PSTRTMSeq005.RunsFrom unblockMachine
      (state 0 (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n) ++ false::false::suffix))
      (framedTrace archive (PSTRTMNatValue017.rawPayload n) suffix)
      (state 19 (false::archive) (encodeNat n ++ false::suffix)) := by
  rw [← rawWord_payload]
  exact framed_runsFrom archive (PSTRTMNatValue017.rawPayload n) suffix

theorem framed_encoder (archive digits suffix : List Bool) :
    ∃ trace final,
      PSTRTMSeq005.RunsFrom unblockMachine
        ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits ++ false::false::suffix)⟩ trace final ∧
      final.q = 19 ∧ final.Tape = Turing.Tape.mk₂ (false::archive) (PSTRTMUnblockTrace019.rawWord digits ++ false::suffix) ∧
      trace.length ≤ 32*(digits.length+1)^2 ∧
      ∀ inputLength, visitedSpace unblockMachine inputLength trace ≤ inputLength+64*(digits.length+1)^2 :=
  ⟨framedTrace archive digits suffix,state 19 (false::archive) (PSTRTMUnblockTrace019.rawWord digits ++ false::suffix),
    framed_runsFrom archive digits suffix,rfl,rfl,framed_time_le archive digits suffix,
    framed_visitedSpace_le archive digits suffix⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004
