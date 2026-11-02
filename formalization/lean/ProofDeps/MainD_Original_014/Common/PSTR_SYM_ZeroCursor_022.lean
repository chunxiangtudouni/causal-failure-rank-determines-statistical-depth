module

public import Common.PSTR_SYM_ZeroPorts_021

/-! SAME actual run: clear old EOF, LEFT over the physically cleared strip
to the retained last count flag, then nineteen real RIGHT moves. The final
seventeen left cells were really traversed. No pre-existing17-cell reserve,
allocator or free movement is assumed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail

open Turing PSTRTMSeq005 PA17TMRatArithmeticAllocate013

theorem false_head_blank (left : List Bool) : Tape.mk₂ left [false] = Tape.mk₂ left [] := by
  simpa using tape_false_suffix left [] 1

theorem seek_final_blank (zeros : Nat) (archive : List Bool) :
    (seekState 1 archive (true :: (List.replicate zeros false ++ [false]))).Tape =
      Tape.mk₂ archive [true] := by
  simpa only [seekState, List.replicate_succ', List.cons_append, List.nil_append]
    using tape_false_suffix archive [true] (zeros + 1)

def postClearMachine : Machine 21 := seqMachine (gapSeekMachine .left) right19Machine

def postClearTrace (zeros : Nat) (archive : List Bool) : List (MachineState 21) :=
  (seekFalseTrace zeros archive []).map (leftCfg (b := 19)) ++
    (rightTrace 0 19 (by omega) (Tape.mk₂ archive [true])).map (rightCfg (a := 1))

def postClearFinal (archive : List Bool) : MachineState 21 :=
  rightCfg (a := 1)
    (rightState 19 (by omega) (Tape.mk₂ (List.replicate 18 false ++ true :: archive) []))

theorem postClear_runsFrom (zeros : Nat) (archive : List Bool) :
    RunsFrom postClearMachine
      ⟨0, Tape.mk₂ (List.replicate zeros false ++ true :: archive) []⟩
      (postClearTrace zeros archive) (postClearFinal archive) := by
  have first : RunsFrom (gapSeekMachine .left)
      ⟨0, Tape.mk₂ (List.replicate zeros false ++ true :: archive) []⟩
      (seekFalseTrace zeros archive [])
      (seekState 1 archive (true :: (List.replicate zeros false ++ [false]))) := by
    simpa only [seekState, false_head_blank] using seekFalse_runsFrom zeros archive []
  apply seq_runsFrom (gapSeekMachine .left) right19Machine
    ⟨0, Tape.mk₂ (List.replicate zeros false ++ true :: archive) []⟩
    (seekState 1 archive (true :: (List.replicate zeros false ++ [false])))
    (rightState 19 (by omega) (Tape.mk₂ (List.replicate 18 false ++ true :: archive) []))
    (seekFalseTrace zeros archive []) (rightTrace 0 19 (by omega) (Tape.mk₂ archive [true]))
  · exact first
  · rw [seek_final_blank]
    simpa only [right19_from_flag] using right19_runsFrom (Tape.mk₂ archive [true])

theorem postClear_length (zeros : Nat) (archive : List Bool) :
    (postClearTrace zeros archive).length = zeros + 22 := by
  simp only [postClearTrace, List.length_append, List.length_map, seekFalse_length, rightTrace_length]

def cursorTailMachine : Machine 23 := seqMachine clearEOFMachine postClearMachine

def cursorTailTrace (zeros : Nat) (archive : List Bool) : List (MachineState 23) :=
  (clearEOFTrace (List.replicate zeros false ++ true :: archive)).map (leftCfg (b := 21)) ++
    (postClearTrace zeros archive).map (rightCfg (a := 1))

def cursorTailFinal (archive : List Bool) : MachineState 23 :=
  rightCfg (a := 1) (postClearFinal archive)

theorem cursorTail_runsFrom (zeros : Nat) (archive : List Bool) :
    RunsFrom cursorTailMachine
      ⟨0, Tape.mk₂ (List.replicate zeros false ++ true :: archive) [true]⟩
      (cursorTailTrace zeros archive) (cursorTailFinal archive) := by
  apply seq_runsFrom clearEOFMachine postClearMachine
    ⟨0, Tape.mk₂ (List.replicate zeros false ++ true :: archive) [true]⟩
    ⟨1, Tape.mk₂ (List.replicate zeros false ++ true :: archive) []⟩
    (postClearFinal archive)
    (clearEOFTrace (List.replicate zeros false ++ true :: archive)) (postClearTrace zeros archive)
  · exact clearEOF_runsFrom _
  · exact postClear_runsFrom zeros archive

theorem cursorTail_final_tape (archive : List Bool) :
    (cursorTailFinal archive).Tape =
      Tape.mk₂ (List.replicate 18 false ++ true :: archive) [] := rfl

theorem cursorTail_length (zeros : Nat) (archive : List Bool) :
    (cursorTailTrace zeros archive).length = zeros + 24 := by
  simp only [cursorTailTrace, List.length_append, List.length_map, clearEOF_length, postClear_length]
  omega

theorem cursorTail_space (zeros : Nat) (archive : List Bool) (inputLength : Nat) :
    visitedSpace cursorTailMachine inputLength (cursorTailTrace zeros archive) ≤
      inputLength + 2 * zeros + 49 := by
  have bound := PSTRTMTrace002.visitedSpace_le cursorTailMachine inputLength (cursorTailTrace zeros archive)
  rw [cursorTail_length] at bound
  omega

/-- The actual parsed count ALWAYS has a last TRUE flag. This describes
its canonical bits; it is not a supplied coordinate or a runtime length. -/
theorem count_reverse_cons (count : Nat) :
    ∃ (bit : Bool) (earlier : List Bool), (PSTRTMNatValue017.rawPayload count).reverse = bit :: earlier := by
  have positive : 0 < (PSTRTMNatValue017.rawPayload count).reverse.length := by
    rw [List.length_reverse, PSTRSymbolicLocator.rawPayload_length]
    unfold natBits
    omega
  cases shape : (PSTRTMNatValue017.rawPayload count).reverse with
  | nil => simp only [shape, List.length_nil] at positive; omega
  | cons bit earlier => exact ⟨bit, earlier, rfl⟩

theorem cursor_input_layout (count dataBits : Nat) (bit : Bool) (earlier : List Bool)
    (shape : (PSTRTMNatValue017.rawPayload count).reverse = bit :: earlier) :
    List.replicate dataBits false ++ PSTRSymbolicLocator.outerLeft [] count =
      List.replicate (dataBits + 1) false ++ true :: bit :: PSTRTMRawNat010.leftBlocks earlier := by
  simp only [PSTRSymbolicLocator.outerLeft, shape, PSTRTMRawNat010.leftBlocks,
    List.flatMap_cons, List.cons_append, List.nil_append, List.append_nil]
  rw [PSTRSymbolicCleanup.zero_push]

theorem cursor_output_layout (count : Nat) (bit : Bool) (earlier : List Bool)
    (shape : (PSTRTMNatValue017.rawPayload count).reverse = bit :: earlier) :
    List.replicate 18 false ++ true :: bit :: PSTRTMRawNat010.leftBlocks earlier =
      List.replicate 17 false ++ PSTRSymbolicLocator.outerLeft [] count := by
  simp only [PSTRSymbolicLocator.outerLeft, shape, PSTRTMRawNat010.leftBlocks,
    List.flatMap_cons, List.cons_append, List.nil_append, List.append_nil]
  rw [PSTRSymbolicCleanup.zero_push]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail
