module

public import Common.PSTR_SYM_FirstNatTest_025

/-! Actual restoration of the original outer count after the N-tag test.
The first original Natural tag is FALSE and supplies the genuine second
OWN cell. Both suffix and original left blank survive; fieldBack and
Unblock really return to the beginning of the original raw count. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront

open Turing PSTRTMSeq005
open PSTRSymbolicLocator (outerLeft rawPayload_length)
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticUnblock004

def restoreCountMachine : Machine 25 := seqMachine fieldBackMachine PSTRTMUnblock018.unblockMachine

def restoreCountTrace (count : Nat) (suffix : List Bool) : List (MachineState 25) :=
  (fieldBackTrace [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)).map (leftCfg (b := 19)) ++
    (framedTrace [] (PSTRTMNatValue017.rawPayload count) suffix).map (rightCfg (a := 5))

def restoreCountFinal (count : Nat) (suffix : List Bool) : MachineState 25 :=
  rightCfg (a := 5) (PSTRTMUnblock018.state 19 [false] (encodeNat count ++ false :: suffix))

theorem restoreCount_runsFrom (count : Nat) (suffix : List Bool) :
    RunsFrom restoreCountMachine ⟨0, Tape.mk₂ (outerLeft [] count) (false :: suffix)⟩
      (restoreCountTrace count suffix) (restoreCountFinal count suffix) := by
  apply seq_runsFrom fieldBackMachine PSTRTMUnblock018.unblockMachine
    ⟨0, Tape.mk₂ (outerLeft [] count) (false :: suffix)⟩
    (fieldBackFinal [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (PSTRTMUnblock018.state 19 [false] (encodeNat count ++ false :: suffix))
    (fieldBackTrace [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (framedTrace [] (PSTRTMNatValue017.rawPayload count) suffix)
  · rw [PSTRSymbolicZeroTail.outer_guard]
    exact fieldBack_runsFrom [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)
  · rw [fieldBack_final_tape]
    exact originalNat_runsFrom count [] suffix

theorem restoreCount_final_tape (count : Nat) (suffix : List Bool) :
    (restoreCountFinal count suffix).Tape = Tape.mk₁ (encodeNat count ++ false :: suffix) := by
  have blank : Tape.mk₂ [false] (encodeNat count ++ false :: suffix) =
      Tape.mk₂ [] (encodeNat count ++ false :: suffix) := by
    simpa only [List.nil_append, List.replicate_succ, List.replicate_zero] using
      PSTRSymbolicZeroTail.tape_false_left [] (encodeNat count ++ false :: suffix) 1
  exact blank

theorem restoreCount_length (count : Nat) (suffix : List Bool) :
    (restoreCountTrace count suffix).length = (natBits count)^2 + 13 * natBits count + 10 := by
  simp only [restoreCountTrace, List.length_append, List.length_map, fieldBackTrace_length,
    framed_length, rawPayload_length]
  omega

theorem restoreCount_time_le (count : Nat) (suffix : List Bool) :
    (restoreCountTrace count suffix).length ≤ 32 * (natBits count + 1)^2 := by
  rw [restoreCount_length]
  nlinarith [Nat.zero_le ((natBits count)^2)]

theorem restoreCount_space (count : Nat) (suffix : List Bool) (inputLength : Nat) :
    visitedSpace restoreCountMachine inputLength (restoreCountTrace count suffix) ≤
      inputLength + 64 * (natBits count + 1)^2 + 1 := by
  have bound := PSTRTMTrace002.visitedSpace_le restoreCountMachine inputLength (restoreCountTrace count suffix)
  have time := restoreCount_time_le count suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront
