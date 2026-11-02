module
public import Structure.PA17_TM_RatArithmetic_Allocate_013c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013

open Turing

/-- One initial move, followed by a real scan over false cells to the next
true marker. Direction is compiled before all tapes; gap length is not input. -/
def gapSeekMachine (direction : Dir) : Machine 1 := fun q symbol =>
  if q.val=0 then some (1,.move direction)
  else if symbol then none else some (1,.move direction)

def seekState (q : Fin 2) (left right : List Bool) : MachineState 1 :=
  ⟨q,Tape.mk₂ left right⟩

def seekRightTrace (n : Nat) (left suffix : List Bool) : List (MachineState 1) :=
  match n with
  | 0 => [seekState 1 left (true::suffix)]
  | n+1 => seekState 1 left (false::(List.replicate n false++true::suffix)) ::
    seekRightTrace n (false::left) suffix

theorem seekRight_head (n : Nat) (left suffix : List Bool) :
    (seekRightTrace n left suffix).head? =
      some (seekState 1 left (List.replicate n false++true::suffix)) := by
  cases n <;> rfl

theorem seekRight_last (n : Nat) (left suffix : List Bool) :
    (seekRightTrace n left suffix).getLast? =
      some (seekState 1 (List.replicate n false++left) (true::suffix)) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    change ([seekState 1 left (false::(List.replicate n false++true::suffix))] ++
      seekRightTrace n (false::left) suffix).getLast? = _
    rw [List.getLast?_append,ih]
    simp only [Option.some_or,List.replicate_succ',List.append_assoc,List.singleton_append]

theorem seekRight_length (n : Nat) (left suffix : List Bool) :
    (seekRightTrace n left suffix).length = n+1 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp [seekRightTrace,ih]

theorem seekRight_chain (n : Nat) (left suffix : List Bool) :
    (seekRightTrace n left suffix).IsChain
      (fun before after => TM0.step (gapSeekMachine .right) before = some after) := by
  induction n generalizing left with
  | zero => simp [seekRightTrace]
  | succ n ih =>
    apply List.IsChain.cons (ih (false::left))
    intro next hn
    rw [seekRight_head] at hn
    simp only [Option.mem_some_iff] at hn
    subst next
    simp [TM0.step,gapSeekMachine,seekState,Tape.mk₂]

def forwardGapTrace (n : Nat) (left suffix : List Bool) : List (MachineState 1) :=
  seekState 0 left (true::(List.replicate n false++true::suffix)) ::
    seekRightTrace n (true::left) suffix

theorem forwardGap_runsFrom (n : Nat) (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (gapSeekMachine .right)
      (seekState 0 left (true::(List.replicate n false++true::suffix)))
      (forwardGapTrace n left suffix)
      (seekState 1 (List.replicate n false++true::left) (true::suffix)) := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.IsChain.cons (seekRight_chain n (true::left) suffix)
    intro next hn
    rw [seekRight_head] at hn
    simp only [Option.mem_some_iff] at hn
    subst next
    simp [TM0.step,gapSeekMachine,seekState,Tape.mk₂]
  · change ([seekState 0 left (true::(List.replicate n false++true::suffix))] ++
      seekRightTrace n (true::left) suffix).getLast? = _
    rw [List.getLast?_append,seekRight_last]
    rfl
  · simp [TM0.step,gapSeekMachine,seekState,Tape.mk₂]

def seekLeftTrace (n : Nat) (archive suffix : List Bool) : List (MachineState 1) :=
  match n with
  | 0 => [seekState 1 archive (true::suffix)]
  | n+1 => seekState 1 (List.replicate n false++true::archive) (false::suffix) ::
    seekLeftTrace n archive (false::suffix)

theorem seekLeft_head (n : Nat) (archive suffix : List Bool) :
    (seekLeftTrace n archive suffix).head? =
      some ⟨1,(Tape.mk₂ (List.replicate n false++true::archive) suffix).move .left⟩ := by
  cases n <;> simp [seekLeftTrace,seekState,List.replicate_succ,Tape.mk₂]

theorem seekLeft_last (n : Nat) (archive suffix : List Bool) :
    (seekLeftTrace n archive suffix).getLast? =
      some (seekState 1 archive (true::(List.replicate n false++suffix))) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
    change ([seekState 1 (List.replicate n false++true::archive) (false::suffix)] ++
      seekLeftTrace n archive (false::suffix)).getLast? = _
    rw [List.getLast?_append,ih]
    simp only [Option.some_or,List.replicate_succ',List.append_assoc,List.singleton_append]

theorem seekLeft_length (n : Nat) (archive suffix : List Bool) :
    (seekLeftTrace n archive suffix).length = n+1 := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih => simp [seekLeftTrace,ih]

theorem seekLeft_chain (n : Nat) (archive suffix : List Bool) :
    (seekLeftTrace n archive suffix).IsChain
      (fun before after => TM0.step (gapSeekMachine .left) before = some after) := by
  induction n generalizing suffix with
  | zero => simp [seekLeftTrace]
  | succ n ih =>
    apply List.IsChain.cons (ih (false::suffix))
    intro next hn
    rw [seekLeft_head] at hn
    simp only [Option.mem_some_iff] at hn
    subst next
    simp [TM0.step,gapSeekMachine,seekState,Tape.mk₂]

def returnGapTrace (n : Nat) (archive suffix : List Bool) : List (MachineState 1) :=
  seekState 0 (List.replicate n false++true::archive) (true::suffix) ::
    seekLeftTrace n archive (true::suffix)

theorem returnGap_runsFrom (n : Nat) (archive suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (gapSeekMachine .left)
      (seekState 0 (List.replicate n false++true::archive) (true::suffix))
      (returnGapTrace n archive suffix)
      (seekState 1 archive (true::(List.replicate n false++true::suffix))) := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.IsChain.cons (seekLeft_chain n archive (true::suffix))
    intro next hn
    rw [seekLeft_head] at hn
    simp only [Option.mem_some_iff] at hn
    subst next
    simp [TM0.step,gapSeekMachine,seekState]
  · change ([seekState 0 (List.replicate n false++true::archive) (true::suffix)] ++
      seekLeftTrace n archive (true::suffix)).getLast? = _
    rw [List.getLast?_append,seekLeft_last]
    rfl
  · simp [TM0.step,gapSeekMachine,seekState,Tape.mk₂]

theorem forwardGap_length (n : Nat) (left suffix : List Bool) :
    (forwardGapTrace n left suffix).length = n+2 := by
  simp [forwardGapTrace,seekRight_length]

theorem returnGap_length (n : Nat) (archive suffix : List Bool) :
    (returnGapTrace n archive suffix).length = n+2 := by
  simp [returnGapTrace,seekLeft_length]

private theorem seek_prefix_bound (direction : Dir) (trace : List (MachineState 1))
    (n : Nat) (hlen : trace.length=n+2) (prefixLength inputLength : Nat) :
    visitedSpace (gapSeekMachine direction) inputLength (trace.take prefixLength) ≤ inputLength+2*n+5 := by
  have hs := PSTRTMTrace002.visitedSpace_le (gapSeekMachine direction) inputLength
    (trace.take prefixLength)
  have hp : (trace.take prefixLength).length ≤ trace.length := by
    simp only [List.length_take]
    omega
  omega

theorem forwardGap_prefix_space (n : Nat) (left suffix : List Bool) (prefixLength inputLength : Nat) :
    visitedSpace (gapSeekMachine .right) inputLength ((forwardGapTrace n left suffix).take prefixLength) ≤
      inputLength+2*n+5 :=
  seek_prefix_bound .right _ n (forwardGap_length n left suffix) prefixLength inputLength

theorem returnGap_prefix_space (n : Nat) (archive suffix : List Bool) (prefixLength inputLength : Nat) :
    visitedSpace (gapSeekMachine .left) inputLength ((returnGapTrace n archive suffix).take prefixLength) ≤
      inputLength+2*n+5 :=
  seek_prefix_bound .left _ n (returnGap_length n archive suffix) prefixLength inputLength

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013
