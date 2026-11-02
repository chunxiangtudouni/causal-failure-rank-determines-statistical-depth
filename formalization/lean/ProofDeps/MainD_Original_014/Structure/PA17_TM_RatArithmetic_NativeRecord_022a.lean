module
public import Structure.PA17_TM_RatArithmetic_Store_019b
public import Structure.PA17_TM_RatArithmetic_NatDivCall_011b
public import Common.PSTR_TM_PackFinish_039

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeRecord022

open Turing

/-- Reuse the fixed six-label anchor program, overriding only its actual
write at label2. This clears a real working anchor before a native call. -/
def clearAnchorMachine : Machine 5 := fun q symbol =>
  if q.val=2 then some (3,.write false) else
    PA17TMRatArithmeticStore019.anchorMachine q symbol

def clearAnchorTrace (archive raw : List Bool) : List (MachineState 5) :=
  [PA17TMRatArithmeticStore019.anchorState 0 (false::true::archive) raw,
   PA17TMRatArithmeticStore019.anchorState 1 (true::archive) (false::raw),
   PA17TMRatArithmeticStore019.anchorState 2 archive (true::false::raw),
   PA17TMRatArithmeticStore019.anchorState 3 archive (false::false::raw),
   PA17TMRatArithmeticStore019.anchorState 4 (false::archive) (false::raw),
   PA17TMRatArithmeticStore019.anchorState 5 (false::false::archive) raw]

theorem clearAnchor_runsFrom (archive raw : List Bool) :
    PSTRTMSeq005.RunsFrom clearAnchorMachine
      (PA17TMRatArithmeticStore019.anchorState 0 (false::true::archive) raw)
      (clearAnchorTrace archive raw)
      (PA17TMRatArithmeticStore019.anchorState 5 (false::false::archive) raw) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [clearAnchorTrace,List.isChain_cons_cons,TM0.step,clearAnchorMachine,
      PA17TMRatArithmeticStore019.anchorMachine,PA17TMRatArithmeticStore019.anchorState,Tape.mk₂]
  · simp [TM0.step,clearAnchorMachine,PA17TMRatArithmeticStore019.anchorMachine,
      PA17TMRatArithmeticStore019.anchorState]

theorem clearAnchor_length (archive raw : List Bool) : (clearAnchorTrace archive raw).length=6 := rfl

theorem two_false_reserve (n : Nat) (reserve : 2≤n) (archive : List Bool) :
    false::false::(List.replicate (n-2) false++archive) = List.replicate n false++archive := by
  have hn : 2+(n-2)=n := by omega
  calc
    _ = (List.replicate 2 false++List.replicate (n-2) false)++archive := rfl
    _ = List.replicate (2+(n-2)) false++archive := by rw [List.replicate_add]
    _ = List.replicate n false++archive := by rw [hn]

/-- Only actual infinite blank tails permit this displayed reserve to be
omitted. No external TRUE suffix is discarded by the equality. -/
theorem right_blank_reserve (left word : List Bool) (n : Nat) :
    Tape.mk₂ left (word++List.replicate n false++[]) = Tape.mk₂ left word := by
  simp only [List.append_nil]
  unfold Tape.mk₂
  rw [PSTRTMPackFinish039.blank_false_suffix]

def rawRecordMachine {states : Nat} (machine : Machine states) : Machine (states+27+1) :=
  PSTRTMSeq005.seqMachine machine PA17TMRatArithmeticStore019.storeMachine

/-- Same native code between two real anchor/record programs. No value,
width, time budget or output is a field of this code. -/
def recordMachine {states : Nat} (machine : Machine states) : Machine (5+(states+27+1)+1) :=
  PSTRTMSeq005.seqMachine clearAnchorMachine (rawRecordMachine machine)

def recordFirst {states : Nat} (_machine : Machine states) (reserve : Nat)
    (archive input : List Bool) : MachineState (5+(states+27+1)+1) :=
  PSTRTMSeq005.leftCfg (b:=states+27+1)
    (PA17TMRatArithmeticStore019.anchorState 0
      (false::true::(List.replicate (reserve-2) false++archive)) input)

theorem record_first_zero {states : Nat} (machine : Machine states) (reserve : Nat)
    (archive input : List Bool) :
    recordFirst machine reserve archive input =
      ⟨0,Tape.mk₂ (false::true::(List.replicate (reserve-2) false++archive)) input⟩ := by
  simp only [recordFirst,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,
    PA17TMRatArithmeticStore019.anchorState,Fin.val_zero,Fin.mk_zero]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeRecord022
