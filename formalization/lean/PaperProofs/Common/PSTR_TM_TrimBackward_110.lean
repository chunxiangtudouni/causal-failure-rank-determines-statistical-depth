module
public import PaperProofs.Common.PSTR_TM_TrimRewind_109
public import PaperProofs.Common.PSTR_TM_TrimValue_104

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimBackward110
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103

def output (reversed : List Bool) : List Bool := match keepReverse reversed with
  | [] => [false]
  | first::later => (first::later).reverse
def initial : List Bool → MachineState 16
  | [] => state 3 [] [false]
  | bit::earlier => state 3 (bit::(PSTRTMRawNat010.leftBlocks earlier++[false])) [true]
def zeroTrace : List (MachineState 16) :=
  [initial [],state 8 [false] [],state 9 [false] [false],state 15 [false,false] [],
    state 16 [false,false] [true],state 14 [false] [false,true]]
theorem zero_head : zeroTrace.head?=some (initial []) := rfl
theorem zero_last : zeroTrace.getLast?=some (state 14 [false] (PSTRTMIncrement009.blocks [false])) := rfl
theorem zero_chain : zeroTrace.IsChain (fun x y => Turing.TM0.step trimMachine x=some y) := by
  have hz : Turing.ListBlank.mk [false,false]=Turing.ListBlank.mk ([] : List Bool) := by
    calc
      _ = Turing.ListBlank.mk [false] := PSTRTMRawNat010.blank_append_false [false]
      _ = Turing.ListBlank.mk ([] : List Bool) := PSTRTMRawNat010.blank_single_false
  simp [zeroTrace,initial,List.isChain_cons_cons,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_single_false,hz]

def zeroUnit (earlier : List Bool) : List (MachineState 16) :=
  let left := PSTRTMRawNat010.leftBlocks earlier++[false]
  [initial (false::earlier),state 4 left [false,true],state 5 (false::left) [true],
    state 6 (false::left) [],state 7 left []]
theorem zeroUnit_head (earlier : List Bool) : (zeroUnit earlier).head?=some (initial (false::earlier)) := rfl
theorem zeroUnit_last (earlier : List Bool) : (zeroUnit earlier).getLast?=some (state 7 (PSTRTMRawNat010.leftBlocks earlier++[false]) []) := rfl
theorem zeroUnit_chain (earlier : List Bool) :
    (zeroUnit earlier).IsChain (fun x y => Turing.TM0.step trimMachine x=some y) := by
  simp [zeroUnit,initial,List.isChain_cons_cons,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_single_false]
theorem zeroUnit_advance (earlier : List Bool) :
    Turing.TM0.step trimMachine (state 7 (PSTRTMRawNat010.leftBlocks earlier++[false]) [])=some (initial earlier) := by
  cases earlier <;> simp [initial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]

def trueTrace (earlier : List Bool) : List (MachineState 16) :=
  let left := PSTRTMRawNat010.leftBlocks earlier++[false]
  [initial (true::earlier),state 4 left [true,true],state 10 (true::left) [true]]
theorem true_head (earlier : List Bool) : (trueTrace earlier).head?=some (initial (true::earlier)) := rfl
theorem true_last (earlier : List Bool) : (trueTrace earlier).getLast?=some (state 10 (true::(PSTRTMRawNat010.leftBlocks earlier++[false])) [true]) := rfl
theorem true_chain (earlier : List Bool) :
    (trueTrace earlier).IsChain (fun x y => Turing.TM0.step trimMachine x=some y) := by
  simp [trueTrace,initial,List.isChain_cons_cons,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]
theorem true_advance (earlier : List Bool) :
    Turing.TM0.step trimMachine (state 10 (true::(PSTRTMRawNat010.leftBlocks earlier++[false])) [true])=
      some (state 11 (PSTRTMRawNat010.leftBlocks (true::earlier)++[false]) []) := by
  simp [Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks]

def backTrace : List Bool → List (MachineState 16)
  | [] => zeroTrace
  | false::earlier => zeroUnit earlier++backTrace earlier
  | true::earlier => trueTrace earlier++PSTRTMTrimRewind109.rewindTrace [] (true::earlier) []

theorem back_head (reversed : List Bool) : (backTrace reversed).head?=some (initial reversed) := by
  cases reversed with
  | nil => exact zero_head
  | cons bit earlier => cases bit <;> simp only [backTrace,List.head?_append,zeroUnit_head,true_head,Option.some_or]
theorem back_last (reversed : List Bool) :
    (backTrace reversed).getLast?=some (state 14 [false] (PSTRTMIncrement009.blocks (output reversed))) := by
  induction reversed with
  | nil => exact zero_last
  | cons bit earlier ih =>
    cases bit with
    | false => simp only [backTrace,List.getLast?_append,ih,Option.some_or,output,keepReverse]
    | true =>
      simp only [backTrace,List.getLast?_append,PSTRTMTrimRewind109.rewind_last,
        List.append_nil,Option.some_or,output,keepReverse]

theorem back_chain (reversed : List Bool) :
    (backTrace reversed).IsChain (fun x y => Turing.TM0.step trimMachine x=some y) := by
  induction reversed with
  | nil => exact zero_chain
  | cons bit earlier ih =>
    cases bit with
    | false =>
      apply (zeroUnit_chain earlier).append ih
      intro before hb after ha
      rw [zeroUnit_last] at hb
      rw [back_head] at ha
      have he := Option.mem_some_iff.mp hb
      have hf := Option.mem_some_iff.mp ha
      subst before
      subst after
      exact zeroUnit_advance earlier
    | true =>
      apply (true_chain earlier).append
        (PSTRTMTrimRewind109.rewind_chain _ (PSTRTMPairRewind105.full_chain [] (true::earlier) []))
      intro before hb after ha
      rw [true_last] at hb
      change after ∈ (PSTRTMTrimRewind109.rewindTrace [] (true::earlier) []).head? at ha
      rw [PSTRTMTrimRewind109.rewind_head] at ha
      have he := Option.mem_some_iff.mp hb
      have hf := Option.mem_some_iff.mp ha
      subst before
      subst after
      exact true_advance earlier

theorem back_length_le (reversed : List Bool) : (backTrace reversed).length ≤ 7*reversed.length+6 := by
  induction reversed with
  | nil => decide
  | cons bit earlier ih =>
    cases bit with
    | false =>
      simp only [backTrace,List.length_append,zeroUnit,List.length_cons,List.length_nil]
      omega
    | true =>
      simp only [backTrace,List.length_append,trueTrace,List.length_cons,List.length_nil,PSTRTMTrimRewind109.rewind_length]
      omega

/-- Actual high-zero erasure on the SAME tape, then real pair rewind;
the all-zero branch WRITES one canonical zero pair. The actual trace is
linear in original width, including erasures, branches and final HALT. -/
theorem back_runsFrom (digits : List Bool) :
    PSTRTMSeq005.RunsFrom trimMachine (initial digits.reverse) (backTrace digits.reverse)
      (state 14 [false] (PSTRTMIncrement009.blocks (trimmed digits))) := by
  refine ⟨back_head _,back_chain _,?_,trim_halt _ _⟩
  exact back_last digits.reverse

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimBackward110
