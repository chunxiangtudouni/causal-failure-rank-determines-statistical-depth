module

public import Common.PSTR_SYM_RawBootstrapRun_057

/-! Physical transition to the second stream and the original count
parser with retained LEFT data. The old first EOF is really cleared to a
FALSE guard, then RIGHT is really executed. A true callee HALT is not a
free inline transfer; the eventual containing program must charge it. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRetainedBootstrap

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002 PSTRTMRawNat010
open PSTRSymbolicCounter PSTRSymbolicRawBootstrap

def secondGuardMachine : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .right)
  | _ => none

def secondGuardTrace (archive second : List Bool) : List (MachineState 2) :=
  [⟨0,Tape.mk₂ archive (true :: second)⟩,
   ⟨1,Tape.mk₂ archive (false :: second)⟩,
   ⟨2,Tape.mk₂ (false :: archive) second⟩]

theorem second_guard_runsFrom (archive second : List Bool) :
    RunsFrom secondGuardMachine ⟨0,Tape.mk₂ archive (true :: second)⟩
      (secondGuardTrace archive second) ⟨2,Tape.mk₂ (false :: archive) second⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [secondGuardTrace,List.isChain_cons_cons,TM0.step,secondGuardMachine,Tape.mk₂]
  · simp [TM0.step,secondGuardMachine]

theorem second_guard_length (archive second : List Bool) :
    (secondGuardTrace archive second).length = 3 := rfl

theorem second_guard_space (archive second : List Bool) (inputLength clock : Nat) :
    visitedSpace secondGuardMachine inputLength ((secondGuardTrace archive second).take clock) ≤ inputLength + 7 := by
  have cells := PSTRTMTrace002.visitedSpace_le secondGuardMachine inputLength
    ((secondGuardTrace archive second).take clock)
  have length : ((secondGuardTrace archive second).take clock).length ≤ 3 := by
    simp only [List.length_take,second_guard_length]
    omega
  omega

def counterEntryTraceFrom (archive : List Bool) (count : Nat) (suffix : List Bool) : List (MachineState 23) :=
  (streamTrace (false :: archive) [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)).map (leftCfg (b := 5)) ++
    (fieldBackTrace archive (PSTRTMNatValue017.rawPayload count) (false :: suffix)).map (rightCfg (a := 17))

def counterEntryFinalFrom (archive : List Bool) (count : Nat) (suffix : List Bool) : MachineState 23 :=
  rightCfg (a := 17) (fieldBackFinal archive (PSTRTMNatValue017.rawPayload count) (false :: suffix))

/-- Internal positive-record entry. The LEFT guard is an ACTUAL cell,
produced by second_guard_runsFrom, not an assumed blank before archive. -/
theorem counterEntry_from_guard (archive : List Bool) (count : Nat) (suffix : List Bool) :
    RunsFrom counterEntryMachine
      ⟨0,Tape.mk₂ (false :: archive) (encodeNat count ++ false :: suffix)⟩
      (counterEntryTraceFrom archive count suffix) (counterEntryFinalFrom archive count suffix) := by
  apply seq_runsFrom streamMachine fieldBackMachine
    ⟨0,Tape.mk₂ (false :: archive) (encodeNat count ++ false :: suffix)⟩
    (streamFinal (false :: archive) (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (fieldBackFinal archive (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (streamTrace (false :: archive) [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (fieldBackTrace archive (PSTRTMNatValue017.rawPayload count) (false :: suffix))
  · exact encodeNat_stream_runsFrom (false :: archive) (false :: suffix) count
  · exact fieldBack_runsFrom archive (PSTRTMNatValue017.rawPayload count) (false :: suffix)

theorem counterEntry_from_guard_tape (archive : List Bool) (count : Nat) (suffix : List Bool) :
    (counterEntryFinalFrom archive count suffix).Tape = Tape.mk₂ (false :: archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload count) ++ false :: false :: suffix) :=
  fieldBack_final_tape archive (PSTRTMNatValue017.rawPayload count) (false :: suffix)

theorem counterEntry_from_guard_time (archive : List Bool) (count : Nat) (suffix : List Bool) :
    (counterEntryTraceFrom archive count suffix).length ≤ 32 * (natBits count + 1)^2 := by
  have header := stream_length_le (false :: archive) (PSTRTMNatValue017.rawPayload count) (false :: suffix)
  rw [PSTRSymbolicLocator.rawPayload_length] at header
  simp only [counterEntryTraceFrom,List.length_append,List.length_map,fieldBackTrace_length,
    PSTRSymbolicLocator.rawPayload_length]
  nlinarith [Nat.zero_le ((natBits count)^2)]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRetainedBootstrap
