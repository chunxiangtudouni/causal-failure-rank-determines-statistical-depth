module

public import Common.PSTR_TM_Seq_005
public import Common.PSTR_TM_Increment_009

/-! Actual bounded-gap marking. The runtime length is read from the physical
far TRUE, not supplied to finite control. This is one internal producer step;
it does not by itself allocate the quartic RAW-multiplication window. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005

def marks : Nat → List Bool
  | 0 => []
  | n + 1 => true :: false :: marks n

def pairs (flag : Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => false :: flag :: pairs flag n

theorem marks_snoc (n : Nat) (left : List Bool) :
    marks n ++ true :: false :: left = marks (n + 1) ++ left := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [marks, List.cons_append] using congrArg (true :: false :: ·) ih

theorem pairs_true (n : Nat) : pairs true n = PSTRTMIncrement009.blocks (List.replicate n false) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pairs, List.replicate_succ, PSTRTMIncrement009.blocks,
      List.flatMap_cons, List.cons_append, List.nil_append] using congrArg (false :: true :: ·) ih

theorem pairs_false (n : Nat) : pairs false n = List.replicate (2 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, List.replicate_add]
    simp only [pairs, ih]
    simp [List.replicate_succ]

def gapFlagsMachine : Machine 3 := fun q symbol =>
  match q.val with
  | 0 => if symbol then some (3, .write true) else some (1, .move .right)
  | 1 => some (2, .write true)
  | 2 => some (0, .move .right)
  | _ => none

def flagsState (q : Fin 4) (left right : List Bool) : MachineState 3 :=
  ⟨q, Tape.mk₂ left right⟩

def gapFlagsTrace (suffix : List Bool) : Nat → List Bool → List (MachineState 3)
  | 0, left => [flagsState 0 left (true :: suffix), flagsState 3 left (true :: suffix)]
  | n + 1, left =>
      [flagsState 0 left (false :: false :: (List.replicate (2 * n) false ++ true :: suffix)),
       flagsState 1 (false :: left) (false :: (List.replicate (2 * n) false ++ true :: suffix)),
       flagsState 2 (false :: left) (true :: (List.replicate (2 * n) false ++ true :: suffix))] ++
        gapFlagsTrace suffix n (true :: false :: left)

theorem gapFlags_head (suffix : List Bool) (n : Nat) (left : List Bool) :
    (gapFlagsTrace suffix n left).head? =
      some (flagsState 0 left (List.replicate (2 * n) false ++ true :: suffix)) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, List.replicate_add]
    rfl

theorem gapFlags_last (suffix : List Bool) (n : Nat) (left : List Bool) :
    (gapFlagsTrace suffix n left).getLast? =
      some (flagsState 3 (marks n ++ left) (true :: suffix)) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    rw [gapFlagsTrace, List.getLast?_append, ih, marks_snoc]
    rfl

theorem gapFlags_length (suffix : List Bool) (n : Nat) (left : List Bool) :
    (gapFlagsTrace suffix n left).length = 3 * n + 2 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [gapFlagsTrace, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem gapFlags_chain (suffix : List Bool) (n : Nat) (left : List Bool) :
    (gapFlagsTrace suffix n left).IsChain (fun a b => TM0.step gapFlagsMachine a = some b) := by
  induction n generalizing left with
  | zero => simp [gapFlagsTrace, List.isChain_cons_cons, TM0.step, gapFlagsMachine, flagsState, Tape.mk₂]
  | succ n ih =>
    simp only [gapFlagsTrace, List.cons_append, List.nil_append, List.isChain_cons_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp [TM0.step, gapFlagsMachine, flagsState, Tape.mk₂]
    · simp [TM0.step, gapFlagsMachine, flagsState, Tape.mk₂]
    · apply (ih (true :: false :: left)).cons
      intro state member
      rw [gapFlags_head] at member
      have equal := Option.mem_some_iff.mp member
      subst state
      simp [TM0.step, gapFlagsMachine, flagsState, Tape.mk₂]

/-- Arbitrary near archive and arbitrary far suffix are both preserved. The
head actually travels to the old far marker; no free return is claimed. -/
theorem gapFlags_runsFrom (suffix : List Bool) (n : Nat) (left : List Bool) :
    RunsFrom gapFlagsMachine
      (flagsState 0 left (List.replicate (2 * n) false ++ true :: suffix))
      (gapFlagsTrace suffix n left)
      (flagsState 3 (marks n ++ left) (true :: suffix)) :=
  ⟨gapFlags_head suffix n left, gapFlags_chain suffix n left, gapFlags_last suffix n left,
    by simp [TM0.step, gapFlagsMachine, flagsState]⟩

theorem gapFlags_prefix_space (suffix : List Bool) (n : Nat) (left : List Bool)
    (inputLength clock : Nat) :
    visitedSpace gapFlagsMachine inputLength ((gapFlagsTrace suffix n left).take clock) ≤
      inputLength + 6 * n + 5 := by
  have general := PSTRTMTrace002.visitedSpace_le gapFlagsMachine inputLength
    ((gapFlagsTrace suffix n left).take clock)
  have taken : ((gapFlagsTrace suffix n left).take clock).length ≤ 3 * n + 2 := by
    rw [List.length_take, gapFlags_length]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
