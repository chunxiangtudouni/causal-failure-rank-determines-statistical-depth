module
public import Common.PSTR_TM_Overlap_132

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthSeek163
open PaperProofs.Common.Native.RationalControllerComputation

/-- Threshold's real leftward return over a cleared gap. The nearest
true source flag is detected by the code, not a width/fuel input. Both
the archived cells beyond it and the entire right counter are retained. -/
def seekMachine : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (if symbol then 2 else 1,if symbol then .write true else .move .left)
  | _ => none

def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def scanInitial (left right : List Bool) : Nat → MachineState 2
  | 0 => state 1 left (true::right)
  | gap+1 => state 1 (List.replicate gap false++true::left) (false::right)

def scanTrace (left right : List Bool) : Nat → List (MachineState 2)
  | 0 => [scanInitial left right 0,state 2 left (true::right)]
  | gap+1 => scanInitial left right (gap+1)::scanTrace left (false::right) gap

theorem scan_head (left right : List Bool) (gap : Nat) :
    (scanTrace left right gap).head?=some (scanInitial left right gap) := by cases gap <;> rfl

theorem scan_last (left right : List Bool) (gap : Nat) :
    (scanTrace left right gap).getLast?=some
      (state 2 left (true::(List.replicate gap false++right))) := by
  induction gap generalizing right with
  | zero => rfl
  | succ gap ih =>
    have hn : scanTrace left (false::right) gap≠[] := by
      intro h
      have hh := scan_head left (false::right) gap
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    rw [scanTrace,List.getLast?_cons_of_ne_nil hn,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]

theorem scan_chain (left right : List Bool) (gap : Nat) :
    (scanTrace left right gap).IsChain
      (fun before after => Turing.TM0.step seekMachine before=some after) := by
  induction gap generalizing right with
  | zero => simp [scanTrace,scanInitial,List.isChain_cons_cons,Turing.TM0.step,seekMachine,state,Turing.Tape.mk₂]
  | succ gap ih =>
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [scan_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases gap <;> simp [scanInitial,Turing.TM0.step,seekMachine,state,Turing.Tape.mk₂,List.replicate_succ]
    · exact ih _

theorem scan_length (left right : List Bool) (gap : Nat) : (scanTrace left right gap).length=gap+2 := by
  induction gap generalizing right with
  | zero => rfl
  | succ gap ih => simp only [scanTrace,List.length_cons,ih]

def seekTrace (left right : List Bool) (gap : Nat) : List (MachineState 2) :=
  state 0 (List.replicate gap false++true::left) right::scanTrace left right gap

theorem seek_runsFrom (left right : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom seekMachine (state 0 (List.replicate gap false++true::left) right)
      (seekTrace left right gap) (state 2 left (true::(List.replicate gap false++right))) := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [scan_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases gap <;> simp [scanInitial,Turing.TM0.step,seekMachine,state,Turing.Tape.mk₂,List.replicate_succ]
    · exact scan_chain _ _ _
  · have hn : scanTrace left right gap≠[] := by
      intro h
      have hh := scan_head left right gap
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    exact (List.getLast?_cons_of_ne_nil hn).trans (scan_last _ _ _)
  · simp [Turing.TM0.step,seekMachine,state]

theorem seek_length (left right : List Bool) (gap : Nat) : (seekTrace left right gap).length=gap+3 := by
  simp only [seekTrace,List.length_cons,scan_length]

theorem seek_visitedSpace_le (left right : List Bool) (gap : Nat) :
    visitedSpace seekMachine (left.length+gap+1+right.length) (seekTrace left right gap)≤
      left.length+right.length+3*gap+8 := by
  have h := PSTRTMTrace002.visitedSpace_le seekMachine (left.length+gap+1+right.length) (seekTrace left right gap)
  rw [seek_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthSeek163
