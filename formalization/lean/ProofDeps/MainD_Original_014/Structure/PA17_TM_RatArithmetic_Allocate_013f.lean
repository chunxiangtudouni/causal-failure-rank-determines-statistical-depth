module
public import Structure.PA17_TM_RatArithmetic_Allocate_013e

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013

open Turing PA17TMDivisionCompose006

attribute [local implicit_reducible] expandCap PA17TMDivisionCompose006.totalStates

def expandFirst (k n : Nat) (archive : List Bool) : MachineState (expandCap k) :=
  expandLift k 0 (by omega : 1≤3*k+1)
    (seekState 0 archive (false::(List.replicate n false++[true])))

def expandLast (k n : Nat) (archive : List Bool) : MachineState (expandCap k) :=
  expandLift k 4 (by omega : 1≤3*k+1)
    (seekState 1 archive (false::(List.replicate (k+n) false++[true])))

def expandTrace (k n : Nat) (archive : List Bool) : List (MachineState (expandCap k)) :=
  (((expandLiftTrace k 0 (by omega : 1≤3*k+1)
      (setMarkerTrace false true archive (List.replicate n false++[true])) ++
    expandLiftTrace k 1 (by omega : 1≤3*k+1) (forwardGapTrace n archive [])) ++
    expandLiftTrace k 2 (by omega : 3*k≤3*k+1)
      (gapTrace k 0 k (by omega) (List.replicate n false++true::archive) [])) ++
    expandLiftTrace k 3 (by omega : 1≤3*k+1) (returnGapTrace (k+n) archive [])) ++
    expandLiftTrace k 4 (by omega : 1≤3*k+1)
      (setMarkerTrace true false archive (List.replicate (k+n) false++[true]))

theorem expandLiftTrace_length {a : Nat} (k : Nat) (phase : Fin 5) (h : a≤3*k+1)
    (trace : List (MachineState a)) : (expandLiftTrace k phase h trace).length=trace.length := by
  change ((trace.map (padCfg h)).map (blockCfg (p:=4) (s:=3*k+1) phase)).length=trace.length
  rw [List.length_map,List.length_map]

theorem expand_first_zero (k n : Nat) (archive : List Bool) :
    expandFirst k n archive = ⟨0,Tape.mk₂ archive (false::(List.replicate n false++[true]))⟩ := by
  simp [expandFirst,expandLift,blockCfg,padCfg,padLabel,label,seekState]

/-- A fixed machine, independent of the existing gap length n, grows that
gap by k actual cells and returns to the same clamped source footer. All
outbound/return scans and control transfers occur on this very trace. -/
theorem expand_runsFrom (k n : Nat) (archive : List Bool) :
    PSTRTMSeq005.RunsFrom (expandMachine k) (expandFirst k n archive)
      (expandTrace k n archive) (expandLast k n archive) := by
  let hsmall : 1≤3*k+1 := by omega
  let hgap : 3*k≤3*k+1 := by omega
  let r0 := setMarker_runsFrom false true archive (List.replicate n false++[true])
  let r1 := forwardGap_runsFrom n archive []
  let r2 := gap_runsFrom_blank k (List.replicate n false++true::archive)
  let r3 := returnGap_runsFrom (k+n) archive []
  let r4 := setMarker_runsFrom true false archive (List.replicate (k+n) false++[true])
  have p0 := expand_lift_segment k 0 hsmall (setMarkerMachine true) rfl _ _ _ r0
  have p1 := expand_lift_segment k 1 hsmall (gapSeekMachine .right) rfl _ _ _ r1
  have p2 := expand_lift_segment k 2 hgap (gapMachine k) rfl _ _ _ r2
  have p3 := expand_lift_segment k 3 hsmall (gapSeekMachine .left) rfl _ _ _ r3
  have p4 := expand_lift_segment k 4 hsmall (setMarkerMachine false) rfl _ _ _ r4
  have t0 : TM0.step (expandMachine k)
      (expandLift k 0 hsmall (seekState 1 archive (true::(List.replicate n false++[true])))) =
      some (expandLift k 1 hsmall
        (seekState 0 archive (true::(List.replicate n false++[true])))) := by
    simpa [expandLift,padCfg,padLabel,seekState] using
      expand_transfer k 0 (by decide) hsmall (setMarkerMachine true) rfl _ r0.2.2.2
  have t1 : TM0.step (expandMachine k)
      (expandLift k 1 hsmall
        (seekState 1 (List.replicate n false++true::archive) [true])) =
      some (expandLift k 2 hgap
        (gapState k 0 (by omega) (List.replicate n false++true::archive) [true])) := by
    simpa [expandLift,padCfg,padLabel,seekState,gapState] using
      expand_transfer k 1 (by decide) hsmall (gapSeekMachine .right) rfl _ r1.2.2.2
  have hrep : List.replicate k false++(List.replicate n false++true::archive) =
      List.replicate (k+n) false++true::archive := by
    simp only [List.replicate_add,List.append_assoc]
  have t2 : TM0.step (expandMachine k)
      (expandLift k 2 hgap
        (gapState k (3*k) (by omega)
          (List.replicate k false++(List.replicate n false++true::archive)) [true])) =
      some (expandLift k 3 hsmall
        (seekState 0 (List.replicate (k+n) false++true::archive) [true])) := by
    simpa [expandLift,padCfg,padLabel,seekState,gapState,hrep] using
      expand_transfer k 2 (by decide) hgap (gapMachine k) rfl _ r2.2.2.2
  have t3 : TM0.step (expandMachine k)
      (expandLift k 3 hsmall
        (seekState 1 archive (true::(List.replicate (k+n) false++[true])))) =
      some (expandLift k 4 hsmall
        (seekState 0 archive (true::(List.replicate (k+n) false++[true])))) := by
    simpa [expandLift,padCfg,padLabel,seekState] using
      expand_transfer k 3 (by decide) hsmall (gapSeekMachine .left) rfl _ r3.2.2.2
  have p01 := segment_append _ _ _ _ _ _ _ p0 p1 t0
  have p012 := segment_append _ _ _ _ _ _ _ p01 p2 t1
  have p0123 := segment_append _ _ _ _ _ _ _ p012 p3 t2
  have pall := segment_append _ _ _ _ _ _ _ p0123 p4 t3
  exact segment_runsFrom _ _ _ _ pall
    (expand_last_halt k hsmall (setMarkerMachine false) rfl _ r4.2.2.2)

theorem expand_length (k n : Nat) (archive : List Bool) :
    (expandTrace k n archive).length = 2*n+4*k+9 := by
  simp only [expandTrace,List.length_append,expandLiftTrace_length,
    forwardGap_length,gap_length,returnGap_length,setMarkerTrace,List.length_cons,List.length_nil]
  omega

theorem expand_prefix_space (k n : Nat) (archive : List Bool) (prefixLength inputLength : Nat) :
    visitedSpace (expandMachine k) inputLength ((expandTrace k n archive).take prefixLength) ≤
      inputLength+4*n+8*k+19 := by
  have hs := PSTRTMTrace002.visitedSpace_le (expandMachine k) inputLength
    ((expandTrace k n archive).take prefixLength)
  have ht := expand_length k n archive
  have hp : ((expandTrace k n archive).take prefixLength).length ≤ (expandTrace k n archive).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013
