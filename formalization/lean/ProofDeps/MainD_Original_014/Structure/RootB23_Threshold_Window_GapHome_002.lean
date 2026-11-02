module

public import Structure.RootB23_Threshold_Window_GapFlags_001

/-! Charged real return from the runtime far marker. The same fixed return
machine either retains the new flags or erases them while travelling WEST.
Both alternatives preserve the entire original archive and far suffix. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005

theorem pairs_snoc (flag : Bool) (n : Nat) (suffix : List Bool) :
    pairs flag n ++ false :: flag :: suffix = pairs flag (n + 1) ++ suffix := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pairs, List.cons_append] using congrArg (false :: flag :: ·) ih

def gapHomeMachine (keep : Bool) : Machine 4 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => if symbol then some (2, .write keep) else some (4, .move .right)
  | 2 => some (3, .move .left)
  | 3 => some (1, .move .left)
  | _ => none

def homeState (q : Fin 5) (left right : List Bool) : MachineState 4 :=
  ⟨q, Tape.mk₂ left right⟩

def homeReady (archive suffix : List Bool) : Nat → MachineState 4
  | 0 => homeState 1 archive (false :: suffix)
  | n + 1 => homeState 1 (false :: (marks n ++ false :: archive)) (true :: suffix)

def gapHomeInner (keep : Bool) (archive : List Bool) : Nat → List Bool → List (MachineState 4)
  | 0, suffix => [homeState 1 archive (false :: suffix), homeState 4 (false :: archive) suffix]
  | n + 1, suffix =>
      [homeState 1 (false :: (marks n ++ false :: archive)) (true :: suffix),
       homeState 2 (false :: (marks n ++ false :: archive)) (keep :: suffix),
       homeState 3 (marks n ++ false :: archive) (false :: keep :: suffix)] ++
        gapHomeInner keep archive n (false :: keep :: suffix)

def gapHomeTrace (keep : Bool) (archive suffix : List Bool) (n : Nat) : List (MachineState 4) :=
  homeState 0 (marks n ++ false :: archive) suffix :: gapHomeInner keep archive n suffix

theorem gapHomeInner_head (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    (gapHomeInner keep archive n suffix).head? = some (homeReady archive suffix n) := by
  cases n <;> rfl

theorem gapHomeInner_last (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    (gapHomeInner keep archive n suffix).getLast? =
      some (homeState 4 (false :: archive) (pairs keep n ++ suffix)) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
    rw [gapHomeInner, List.getLast?_append, ih, pairs_snoc]
    rfl

theorem gapHomeInner_chain (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    (gapHomeInner keep archive n suffix).IsChain
      (fun a b => TM0.step (gapHomeMachine keep) a = some b) := by
  induction n generalizing suffix with
  | zero => simp [gapHomeInner, List.isChain_cons_cons, TM0.step, gapHomeMachine, homeState, Tape.mk₂]
  | succ n ih =>
    simp only [gapHomeInner, List.cons_append, List.nil_append, List.isChain_cons_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp [TM0.step, gapHomeMachine, homeState, Tape.mk₂]
    · simp [TM0.step, gapHomeMachine, homeState, Tape.mk₂]
    · apply (ih (false :: keep :: suffix)).cons
      intro state member
      rw [gapHomeInner_head] at member
      have equal := Option.mem_some_iff.mp member
      subst state
      cases n <;> simp [homeReady, marks, TM0.step, gapHomeMachine, homeState, Tape.mk₂]

theorem gapHome_runsFrom (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    RunsFrom (gapHomeMachine keep) (homeState 0 (marks n ++ false :: archive) suffix)
      (gapHomeTrace keep archive suffix n)
      (homeState 4 (false :: archive) (pairs keep n ++ suffix)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply (gapHomeInner_chain keep archive suffix n).cons
    intro state member
    rw [gapHomeInner_head] at member
    have equal := Option.mem_some_iff.mp member
    subst state
    cases n <;> simp [homeReady, marks, TM0.step, gapHomeMachine, homeState, Tape.mk₂]
  · have nonempty : gapHomeInner keep archive n suffix ≠ [] := by
      intro empty
      have head := gapHomeInner_head keep archive suffix n
      simp [empty] at head
    rw [gapHomeTrace, List.getLast?_cons_of_ne_nil nonempty, gapHomeInner_last]
  · simp [TM0.step, gapHomeMachine, homeState]

theorem gapHomeInner_length (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    (gapHomeInner keep archive n suffix).length = 3 * n + 2 := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih => simp only [gapHomeInner, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem gapHome_length (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    (gapHomeTrace keep archive suffix n).length = 3 * n + 3 := by
  simp only [gapHomeTrace, List.length_cons, gapHomeInner_length]

/-- One fixed eight-state-capacity program marks exactly the actually present
gap and physically returns. `n` is proof metadata, absent from code. -/
def gapCodecMachine (keep : Bool) : Machine 8 := seqMachine gapFlagsMachine (gapHomeMachine keep)

def gapCodecTrace (keep : Bool) (archive suffix : List Bool) (n : Nat) : List (MachineState 8) :=
  (gapFlagsTrace suffix n (false :: archive)).map (leftCfg (b := 4)) ++
    (gapHomeTrace keep archive (true :: suffix) n).map (rightCfg (a := 3))

theorem gapCodec_runsFrom (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    RunsFrom (gapCodecMachine keep)
      ⟨0, Tape.mk₂ (false :: archive) (List.replicate (2 * n) false ++ true :: suffix)⟩
      (gapCodecTrace keep archive suffix n)
      (rightCfg (a := 3) (homeState 4 (false :: archive) (pairs keep n ++ true :: suffix))) := by
  exact seq_runsFrom gapFlagsMachine (gapHomeMachine keep) _ _ _ _ _
    (gapFlags_runsFrom suffix n (false :: archive))
    (gapHome_runsFrom keep archive (true :: suffix) n)

theorem gapCodec_length (keep : Bool) (archive suffix : List Bool) (n : Nat) :
    (gapCodecTrace keep archive suffix n).length = 6 * n + 5 := by
  simp only [gapCodecTrace, List.length_append, List.length_map, gapFlags_length, gapHome_length]
  omega

theorem gapCodec_prefix_space (keep : Bool) (archive suffix : List Bool) (n inputLength clock : Nat) :
    visitedSpace (gapCodecMachine keep) inputLength ((gapCodecTrace keep archive suffix n).take clock) ≤
      inputLength + 12 * n + 11 := by
  have general := PSTRTMTrace002.visitedSpace_le (gapCodecMachine keep) inputLength
    ((gapCodecTrace keep archive suffix n).take clock)
  have taken : ((gapCodecTrace keep archive suffix n).take clock).length ≤ 6 * n + 5 := by
    rw [List.length_take, gapCodec_length]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
