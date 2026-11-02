module
public import Common.PSTR_TM_TrimBackward_110

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdTrimBack206
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103

/-- The EXISTING17-label trimmer on the retained threshold archive.
Only its positive branch is needed for4*(B+1)-1; no zero-case context
extension or new allocator is presumed. -/
def initial (archive : List Bool) : List Bool → MachineState 16
  | [] => state 3 archive [false]
  | bit::earlier => state 3 (bit::(PSTRTMRawNat010.leftBlocks earlier ++ false::archive)) [true]

def zeroUnit (archive earlier : List Bool) : List (MachineState 16) :=
  let left := PSTRTMRawNat010.leftBlocks earlier ++ false::archive
  [initial archive (false::earlier),state 4 left [false,true],state 5 (false::left) [true],
    state 6 (false::left) [],state 7 left []]

theorem zero_head (archive earlier : List Bool) :
    (zeroUnit archive earlier).head? = some (initial archive (false::earlier)) := rfl

theorem zero_last (archive earlier : List Bool) :
    (zeroUnit archive earlier).getLast? =
      some (state 7 (PSTRTMRawNat010.leftBlocks earlier ++ false::archive) []) := rfl

theorem zero_chain (archive earlier : List Bool) :
    (zeroUnit archive earlier).IsChain (fun x y => Turing.TM0.step trimMachine x = some y) := by
  simp [zeroUnit,initial,List.isChain_cons_cons,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_single_false]

theorem zero_advance (archive earlier : List Bool) :
    Turing.TM0.step trimMachine (state 7 (PSTRTMRawNat010.leftBlocks earlier ++ false::archive) []) =
      some (initial archive earlier) := by
  cases earlier <;> simp [initial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]

def trueTrace (archive earlier : List Bool) : List (MachineState 16) :=
  let left := PSTRTMRawNat010.leftBlocks earlier ++ false::archive
  [initial archive (true::earlier),state 4 left [true,true],state 10 (true::left) [true]]

theorem true_head (archive earlier : List Bool) :
    (trueTrace archive earlier).head? = some (initial archive (true::earlier)) := rfl

theorem true_last (archive earlier : List Bool) :
    (trueTrace archive earlier).getLast? =
      some (state 10 (true::(PSTRTMRawNat010.leftBlocks earlier ++ false::archive)) [true]) := rfl

theorem true_chain (archive earlier : List Bool) :
    (trueTrace archive earlier).IsChain (fun x y => Turing.TM0.step trimMachine x = some y) := by
  simp [trueTrace,initial,List.isChain_cons_cons,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]

theorem true_advance (archive earlier : List Bool) :
    Turing.TM0.step trimMachine
        (state 10 (true::(PSTRTMRawNat010.leftBlocks earlier ++ false::archive)) [true]) =
      some (state 11 (PSTRTMRawNat010.leftBlocks (true::earlier) ++ false::archive) []) := by
  simp [Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks]

def backTrace (archive : List Bool) : List Bool → List (MachineState 16)
  | [] => []
  | false::earlier => zeroUnit archive earlier ++ backTrace archive earlier
  | true::earlier => trueTrace archive earlier ++ PSTRTMTrimRewind109.rewindTrace archive (true::earlier) []

theorem back_head (archive reversed : List Bool) (hp : true ∈ reversed) :
    (backTrace archive reversed).head? = some (initial archive reversed) := by
  cases reversed with
  | nil => simp at hp
  | cons bit earlier => cases bit <;>
      simp only [backTrace,List.head?_append,zero_head,true_head,Option.some_or]

theorem back_last (archive reversed : List Bool) (hp : true ∈ reversed) :
    (backTrace archive reversed).getLast? = some (state 14 (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMTrimBackward110.output reversed))) := by
  induction reversed with
  | nil => simp at hp
  | cons bit earlier ih =>
    cases bit with
    | false =>
      have ht : true ∈ earlier := by simpa only [List.mem_cons,Bool.true_eq_false,false_or] using hp
      simp only [backTrace,List.getLast?_append,ih ht,Option.some_or,
        PSTRTMTrimBackward110.output,keepReverse]
    | true =>
      simp only [backTrace,List.getLast?_append,PSTRTMTrimRewind109.rewind_last,
        List.append_nil,Option.some_or,PSTRTMTrimBackward110.output,keepReverse]

theorem back_chain (archive reversed : List Bool) (hp : true ∈ reversed) :
    (backTrace archive reversed).IsChain (fun x y => Turing.TM0.step trimMachine x = some y) := by
  induction reversed with
  | nil => simp at hp
  | cons bit earlier ih =>
    cases bit with
    | false =>
      have ht : true ∈ earlier := by simpa only [List.mem_cons,Bool.true_eq_false,false_or] using hp
      apply (zero_chain archive earlier).append (ih ht)
      intro before hb after ha
      rw [zero_last] at hb
      rw [back_head archive earlier ht] at ha
      have eb := Option.mem_some_iff.mp hb
      have ea := Option.mem_some_iff.mp ha
      subst before
      subst after
      exact zero_advance _ _
    | true =>
      apply (true_chain archive earlier).append
        (PSTRTMTrimRewind109.rewind_chain _ (PSTRTMPairRewind105.full_chain archive (true::earlier) []))
      intro before hb after ha
      rw [true_last] at hb
      change after ∈ (PSTRTMTrimRewind109.rewindTrace archive (true::earlier) []).head? at ha
      rw [PSTRTMTrimRewind109.rewind_head] at ha
      have eb := Option.mem_some_iff.mp hb
      have ea := Option.mem_some_iff.mp ha
      subst before
      subst after
      exact true_advance _ _

theorem back_length_le (archive reversed : List Bool) :
    (backTrace archive reversed).length ≤ 7*reversed.length + 6 := by
  induction reversed with
  | nil => simp [backTrace]
  | cons bit earlier ih =>
    cases bit with
    | false =>
      simp only [backTrace,List.length_append,zeroUnit,List.length_cons,List.length_nil]
      omega
    | true =>
      simp only [backTrace,List.length_append,trueTrace,List.length_cons,List.length_nil,
        PSTRTMTrimRewind109.rewind_length]
      omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdTrimBack206
