module
public import Structure.PA17_TM_RatArithmetic_Outer_025a

/-! Actual counted-loop compiler for the specific original-header/Nx ABI.
This is an INTERNAL composition lemma. It does not close the allocator until
the real frozen023 body discharges its whole-tape running contract. Counts,
growth and the trace-cost recurrence below are proof metadata only. The
fixed machine obtains termination exclusively from the real unary popper. -/
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025

open Turing PA17TMDivisionCompose006

def loopFamily {states : Nat} (body : Machine states) (phase : Fin 2) : Machine (states+16) :=
  if phase.val=0 then padMachine (by omega : 15≤states+16) popNxMachine
  else padMachine (by omega : states≤states+16) body

def loopPorts (states : Nat) (phase : Fin 2) (q : Fin (states+16+1)) :
    Option (Fin 2 × Fin (states+16+1)) :=
  if phase.val=0 ∧ q.val=15 then some (1,0)
  else if phase.val=1 ∧ q.val=states then some (0,0) else none

def loopMachine {states : Nat} (body : Machine states) : Machine (totalStates 1 (states+16)) :=
  blockMachine (loopFamily body) (loopPorts states)

def loopInitial {states : Nat} (_body : Machine states) (h : Nat) (sx : Bool) (bank : List Bool) :
    MachineState (totalStates 1 (states+16)) :=
  blockCfg (0 : Fin 2) (padCfg (by omega : 15≤states+16) (popNxInitial h sx bank))

def loopFinal {states : Nat} (_body : Machine states) (sx : Bool) (bank : List Bool) :
    MachineState (totalStates 1 (states+16)) :=
  blockCfg (0 : Fin 2) (padCfg (by omega : 15≤states+16) (popNxEmpty sx bank))

def loopCost (fee : Nat→Nat) (growth : Nat) : Nat→Nat→Nat
  | 0,_ => 5
  | h+1,n => 2*h+16+fee n+loopCost fee growth h (n+growth)

/-- Each internal body contract must be proved by an ACTUAL closed body.
The header/Nx heads differ physically and the pop/7RIGHT/port transitions
are all in this trace, with no relabel or head reset for free. -/
theorem loop_runsFrom {states : Nat} (body : Machine states) (sx : Bool)
    (bank : Nat→List Bool) (growth : Nat) (fee : Nat→Nat)
    (bodyRun : ∀ h n, ∃ trace,
      PSTRTMSeq005.RunsFrom body
        ⟨0,(popNxFound h sx (bank n)).Tape⟩ trace
        ⟨Fin.last states,(popNxInitial h sx (bank (n+growth))).Tape⟩ ∧ trace.length≤fee n)
    (h n : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (loopMachine body)
      (loopInitial body h sx (bank n)) trace
      (loopFinal body sx (bank (n+growth*h))) ∧ trace.length≤loopCost fee growth h n := by
  induction h generalizing n with
  | zero =>
    have hp := pad_runsFrom (by omega : 15≤states+16) popNxMachine _ _ _
      (popNx_zero_runsFrom sx (bank n))
    have hf : PSTRTMSeq005.RunsFrom (loopFamily body (0 : Fin 2))
        (padCfg (by omega : 15≤states+16) (popNxInitial 0 sx (bank n)))
        ((popNxZeroTrace sx (bank n)).map (padCfg (by omega : 15≤states+16)))
        (padCfg (by omega : 15≤states+16) (popNxEmpty sx (bank n))) := by
      simpa [loopFamily] using hp
    have hr := block_runsFrom (loopFamily body) (loopPorts states) (0 : Fin 2) _ _ _ hf
      (by simp [loopPorts,padCfg,padLabel,popNxEmpty,blockCfg,label,ROOTTMGCDPop016.state])
    refine ⟨((popNxZeroTrace sx (bank n)).map
      (padCfg (by omega : 15≤states+16))).map (blockCfg (0 : Fin 2)),?_,?_⟩
    · simpa only [loopMachine,loopInitial,loopFinal,Nat.mul_zero,Nat.add_zero] using hr
    · simpa only [List.length_map,popNx_zero_length,loopCost] using (Nat.le_refl 5)
  | succ h ih =>
    obtain ⟨middle,middleRun,middleBound⟩ := bodyRun h n
    obtain ⟨tail,tailRun,tailBound⟩ := ih (n+growth)
    have hp := pad_runsFrom (by omega : 15≤states+16) popNxMachine _ _ _
      (popNx_succ_runsFrom h sx (bank n))
    have popRun : PSTRTMSeq005.RunsFrom (loopFamily body (0 : Fin 2))
        (padCfg (by omega : 15≤states+16) (popNxInitial (h+1) sx (bank n)))
        ((popNxSuccTrace h sx (bank n)).map (padCfg (by omega : 15≤states+16)))
        (padCfg (by omega : 15≤states+16) (popNxFound h sx (bank n))) := by
      simpa [loopFamily] using hp
    have hbody := pad_runsFrom (by omega : states≤states+16) body _ _ _ middleRun
    have bodyPadded : PSTRTMSeq005.RunsFrom (loopFamily body (1 : Fin 2))
        (padCfg (by omega : states≤states+16) (⟨0,(popNxFound h sx (bank n)).Tape⟩ : MachineState states))
        (middle.map (padCfg (by omega : states≤states+16)))
        (padCfg (by omega : states≤states+16)
          (⟨Fin.last states,(popNxInitial h sx (bank (n+growth))).Tape⟩ : MachineState states)) := by
      simpa [loopFamily] using hbody
    have leftSegment := block_segment (loopFamily body) (loopPorts states) (0 : Fin 2) _ _ _ popRun
    have rightSegment := block_segment (loopFamily body) (loopPorts states) (1 : Fin 2) _ _ _ bodyPadded
    have toBody := block_transfer (loopFamily body) (loopPorts states) (0 : Fin 2)
      (padCfg (by omega : 15≤states+16) (popNxFound h sx (bank n))) (1,0) popRun.2.2.2
      (by simp [loopPorts,padCfg,padLabel,popNxFound,blockCfg,label,PA17TMRatArithmeticWidth018.sevenState])
    have firstSegment := segment_append (loopMachine body) _ _ _ _ _ _ leftSegment rightSegment toBody
    have toCounter : TM0.step (loopMachine body)
        (blockCfg (1 : Fin 2) (padCfg (by omega : states≤states+16)
          (⟨Fin.last states,(popNxInitial h sx (bank (n+growth))).Tape⟩ : MachineState states))) =
        some (loopInitial body h sx (bank (n+growth))) := by
      have transfer := block_transfer (loopFamily body) (loopPorts states) (1 : Fin 2)
        (padCfg (by omega : states≤states+16)
          (⟨Fin.last states,(popNxInitial h sx (bank (n+growth))).Tape⟩ : MachineState states))
        (0,0) bodyPadded.2.2.2 (by simp [loopPorts,padCfg,padLabel])
      simpa [loopMachine,loopInitial,padCfg,padLabel,popNxInitial,blockCfg,label,ROOTTMGCDPop016.state] using transfer
    have tailSegment : Segment (loopMachine body) _ tail _ :=
      ⟨tailRun.1,tailRun.2.1,tailRun.2.2.1⟩
    have fullSegment := segment_append (loopMachine body) _ _ _ _ _ _ firstSegment tailSegment toCounter
    have fullRun := segment_runsFrom (loopMachine body) _ _ _ fullSegment tailRun.2.2.2
    have index : (n+growth)+growth*h=n+growth*(h+1) := by
      rw [Nat.mul_succ]
      omega
    refine ⟨(((popNxSuccTrace h sx (bank n)).map (padCfg (by omega : 15≤states+16))).map
      (blockCfg (0 : Fin 2)) ++
      (middle.map (padCfg (by omega : states≤states+16))).map (blockCfg (1 : Fin 2)))++tail,?_,?_⟩
    · simpa only [loopInitial,index] using fullRun
    · simp only [List.length_append,List.length_map,popNx_succ_length,loopCost]
      omega

theorem loop_prefix_space {states : Nat} (body : Machine states) (trace : List (MachineState (totalStates 1 (states+16))))
    (fee : Nat→Nat) (growth h n : Nat) (time : trace.length≤loopCost fee growth h n)
    (prefixLength inputLength : Nat) :
    visitedSpace (loopMachine body) inputLength (trace.take prefixLength) ≤
      inputLength+2*loopCost fee growth h n+1 := by
  have hs := PSTRTMTrace002.visitedSpace_le (loopMachine body) inputLength (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025
