module

public import Common.PSTR_SYM_ZeroCursor_022
public import Structure.PA17_TM_RatArithmetic_Parse_002g

/-! The retained original count is not computed by the host. A real static
suffix write creates the first OWN FALSE, fieldBack actually rewinds its
flagged record, frozen Unblock really contracts it, and a real static prefix
write completes the exact original four-Datum N0 output frame. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail

open Turing PSTRTMSeq005 PSTRTMPrepend022 PSTRSymbolicLiteral
open PSTRSymbolicLocator (zeroPrefix zeroSuffix outerLeft rawPayload_length)
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticUnblock004

abbrev prefixCap : Nat := prefixStates zeroPrefix
abbrev suffixCap : Nat := prefixStates zeroSuffix

theorem zeroPrefix_length : zeroPrefix.length = 8 := by decide
theorem zeroSuffix_length : zeroSuffix.length = 17 := by decide

def suffixTail : List Bool := zeroSuffix.tail

theorem zeroSuffix_cons : zeroSuffix = false :: suffixTail := by decide

theorem outer_guard (count : Nat) (right : List Bool) :
    Tape.mk₂ (outerLeft [] count) right =
      Tape.mk₂ (false :: (PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload count).reverse ++ [false])) right := by
  simpa only [outerLeft, List.append_nil, List.replicate_succ, List.replicate_zero,
    List.cons_append, List.nil_append]
    using (tape_false_left (false :: PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload count).reverse) right 1).symm

def finishMachine : Machine (19 + prefixCap + 1) :=
  seqMachine PSTRTMUnblock018.unblockMachine (prefixMachine zeroPrefix)

def prefixOutputTrace (count : Nat) : List (MachineState prefixCap) :=
  prefixFrameTrace zeroPrefix [false] (encodeNat count ++ zeroSuffix)

def prefixOutputFinal (count : Nat) : MachineState prefixCap :=
  prefixFrameFinal zeroPrefix [false] (encodeNat count ++ zeroSuffix)

theorem prefixOutput_tape (count : Nat) :
    (prefixOutputFinal count).Tape = Tape.mk₂ [] (zeroPrefix ++ encodeNat count ++ zeroSuffix) := by
  have actual := prefixFrame_final_tape zeroPrefix [false] (encodeNat count ++ zeroSuffix)
  simpa only [prefixOutputFinal, zeroPrefix_length, show ([false] : List Bool).drop 8 = [] by decide,
    List.append_assoc] using actual

def finishTrace (count : Nat) : List (MachineState (19 + prefixCap + 1)) :=
  (framedTrace [] (PSTRTMNatValue017.rawPayload count) suffixTail).map (leftCfg (b := prefixCap)) ++
    (prefixOutputTrace count).map (rightCfg (a := 19))

def finishFinal (count : Nat) : MachineState (19 + prefixCap + 1) :=
  rightCfg (a := 19) (prefixOutputFinal count)

theorem finish_runsFrom (count : Nat) :
    RunsFrom finishMachine
      ⟨0, Tape.mk₂ [false] (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload count) ++ false :: zeroSuffix)⟩
      (finishTrace count) (finishFinal count) := by
  apply seq_runsFrom PSTRTMUnblock018.unblockMachine (prefixMachine zeroPrefix)
    ⟨0, Tape.mk₂ [false] (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload count) ++ false :: zeroSuffix)⟩
    (PSTRTMUnblock018.state 19 [false] (encodeNat count ++ false :: suffixTail))
    (prefixOutputFinal count)
    (framedTrace [] (PSTRTMNatValue017.rawPayload count) suffixTail) (prefixOutputTrace count)
  · simpa only [PSTRTMUnblock018.state, zeroSuffix_cons] using originalNat_runsFrom count [] suffixTail
  · have actual := prefix_runsFrom zeroPrefix [false] (encodeNat count ++ zeroSuffix)
    simpa only [PSTRTMUnblock018.state, prefixOutputTrace, prefixOutputFinal, zeroSuffix_cons] using actual

abbrev rewindCap : Nat := 5 + (19 + prefixCap + 1) + 1

def rewindEmitMachine : Machine rewindCap := seqMachine fieldBackMachine finishMachine

def rewindEmitTrace (count : Nat) : List (MachineState rewindCap) :=
  (fieldBackTrace [] (PSTRTMNatValue017.rawPayload count) zeroSuffix).map
      (leftCfg (b := 19 + prefixCap + 1)) ++
    (finishTrace count).map (rightCfg (a := 5))

def rewindEmitFinal (count : Nat) : MachineState rewindCap := rightCfg (a := 5) (finishFinal count)

theorem rewindEmit_runsFrom (count : Nat) :
    RunsFrom rewindEmitMachine ⟨0, Tape.mk₂ (outerLeft [] count) zeroSuffix⟩
      (rewindEmitTrace count) (rewindEmitFinal count) := by
  apply seq_runsFrom fieldBackMachine finishMachine
    ⟨0, Tape.mk₂ (outerLeft [] count) zeroSuffix⟩
    (fieldBackFinal [] (PSTRTMNatValue017.rawPayload count) zeroSuffix) (finishFinal count)
    (fieldBackTrace [] (PSTRTMNatValue017.rawPayload count) zeroSuffix) (finishTrace count)
  · rw [outer_guard]
    exact fieldBack_runsFrom [] (PSTRTMNatValue017.rawPayload count) zeroSuffix
  · rw [fieldBack_final_tape]
    exact finish_runsFrom count

abbrev emitCap : Nat := suffixCap + rewindCap + 1

def emitMachine : Machine emitCap := seqMachine (prefixMachine zeroSuffix) rewindEmitMachine

def emitTrace (count : Nat) : List (MachineState emitCap) :=
  (prefixFrameTrace zeroSuffix (List.replicate 17 false ++ outerLeft [] count) []).map
      (leftCfg (b := rewindCap)) ++
    (rewindEmitTrace count).map (rightCfg (a := suffixCap))

def emitFinal (count : Nat) : MachineState emitCap := rightCfg (a := suffixCap) (rewindEmitFinal count)

theorem suffix_written (count : Nat) :
    (prefixFrameFinal zeroSuffix (List.replicate 17 false ++ outerLeft [] count) []).Tape =
      Tape.mk₂ (outerLeft [] count) zeroSuffix := by
  have actual := prefixFrame_reserved zeroSuffix (List.replicate 17 false) (outerLeft [] count) []
    (by simpa only [List.length_replicate] using zeroSuffix_length.symm)
  simpa only [List.append_nil] using actual

theorem emit_runsFrom (count : Nat) :
    RunsFrom emitMachine ⟨0, Tape.mk₂ (List.replicate 17 false ++ outerLeft [] count) []⟩
      (emitTrace count) (emitFinal count) := by
  apply seq_runsFrom (prefixMachine zeroSuffix) rewindEmitMachine
    ⟨0, Tape.mk₂ (List.replicate 17 false ++ outerLeft [] count) []⟩
    (prefixFrameFinal zeroSuffix (List.replicate 17 false ++ outerLeft [] count) [])
    (rewindEmitFinal count)
    (prefixFrameTrace zeroSuffix (List.replicate 17 false ++ outerLeft [] count) [])
    (rewindEmitTrace count)
  · exact prefix_runsFrom zeroSuffix (List.replicate 17 false ++ outerLeft [] count) []
  · rw [suffix_written]
    exact rewindEmit_runsFrom count

theorem emit_final_tape (count : Nat) :
    (emitFinal count).Tape = Tape.mk₂ [] (zeroPrefix ++ encodeNat count ++ zeroSuffix) := by
  exact prefixOutput_tape count

theorem emit_length (count : Nat) :
    (emitTrace count).length = (natBits count)^2 + 13 * natBits count + 87 := by
  simp only [emitTrace, rewindEmitTrace, finishTrace, prefixOutputTrace, List.length_append,
    List.length_map, prefixFrame_length, fieldBackTrace_length, framed_length,
    rawPayload_length, zeroPrefix_length, zeroSuffix_length]
  omega

theorem emit_time_le (count : Nat) :
    (emitTrace count).length ≤ 128 * (natBits count + 1)^2 := by
  rw [emit_length]
  nlinarith [Nat.zero_le ((natBits count)^2)]

theorem emit_space (count inputLength : Nat) :
    visitedSpace emitMachine inputLength (emitTrace count) ≤
      inputLength + 256 * (natBits count + 1)^2 + 1 := by
  have bound := PSTRTMTrace002.visitedSpace_le emitMachine inputLength (emitTrace count)
  have time := emit_time_le count
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail
