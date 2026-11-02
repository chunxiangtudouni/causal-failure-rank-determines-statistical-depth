module
public import Structure.PA17_TM_RatArithmetic_Outer_025c
public import Structure.PA17_TM_RatArithmetic_Width_018k

/-! Fixed raw-width/32-memory transfer code for the eventual allocator.
The only row choice comes from the real Width018 HALT label. This file does
not assume a caller-supplied saved-bit tuple or change a tape/head for free.
The actual023 body instantiation is still required to close the allocator. -/
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018

def rawLoopCapacity (states : Nat) : Nat := 79265+totalStates 1 (states+16)

def decodeWidthMemory (q : Nat) : Fin 32 :=
  ⟨((q-645)/2402-1)%32,Nat.mod_lt _ (by decide)⟩

theorem decodeWidthMemory_actual (memory : Fin 32) (tape : Tape Bool) :
    decodeWidthMemory (widthFinal memory tape).q.val=memory := by
  apply Fin.ext
  change (((widthFinal memory tape).q.val-645)/2402-1)%32=memory.val
  rw [widthFinal_label]
  have hm := memory.isLt
  omega

def rawLoopFamily {states : Nat} (body : Machine states) (phase : Fin 33) :
    Machine (rawLoopCapacity states) :=
  if phase.val=0 then
    padMachine (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) widthMachine
  else padMachine (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states)
    (loopMachine body)

def rawLoopPorts (states : Nat) (phase : Fin 33) (q : Fin (rawLoopCapacity states+1)) :
    Option (Fin 33 × Fin (rawLoopCapacity states+1)) :=
  if phase.val=0 then some (savedPhase (decodeWidthMemory q.val),0) else none

def rawLoopMachine {states : Nat} (body : Machine states) :
    Machine (totalStates 32 (rawLoopCapacity states)) :=
  blockMachine (rawLoopFamily body) (rawLoopPorts states)

def rawLoopSavedEntry {states : Nat} (_body : Machine states) (memory : Fin 32) (tape : Tape Bool) :
    MachineState (totalStates 32 (rawLoopCapacity states)) :=
  blockCfg (savedPhase memory)
    (padCfg (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states)
      (⟨0,tape⟩ : MachineState (totalStates 1 (states+16))))

def rawLoopSavedFinal {states : Nat} (body : Machine states) (memory : Fin 32)
    (sx : Bool) (bank : List Bool) : MachineState (totalStates 32 (rawLoopCapacity states)) :=
  blockCfg (savedPhase memory)
    (padCfg (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states)
      (loopFinal body sx bank))

theorem rawLoop_actual_transfer {states : Nat} (body : Machine states)
    (memory : Fin 32) (tape : Tape Bool)
    (halt : TM0.step widthMachine (widthFinal memory tape)=none) :
    TM0.step (rawLoopMachine body)
      (blockCfg (0 : Fin 33)
        (padCfg (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) (widthFinal memory tape))) =
      some (rawLoopSavedEntry body memory tape) := by
  have hp : TM0.step (rawLoopFamily body (0 : Fin 33))
      (padCfg (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) (widthFinal memory tape))=none := by
    change TM0.step (padMachine (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) widthMachine)
      (padCfg (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) (widthFinal memory tape))=none
    simp only [pad_step,halt,Option.map_none]
  have transfer := block_transfer (rawLoopFamily body) (rawLoopPorts states) (0 : Fin 33)
    (padCfg (by unfold rawLoopCapacity;omega : 79265≤rawLoopCapacity states) (widthFinal memory tape))
    (savedPhase memory,0) hp
    (by simp [rawLoopPorts,padCfg,padLabel,decodeWidthMemory_actual])
  simpa only [rawLoopMachine,rawLoopSavedEntry,padCfg,padLabel,widthFinal,blockCfg_tape,
    Fin.val_zero,Fin.mk_zero] using transfer

theorem rawLoop_saved_runsFrom {states : Nat} (body : Machine states) (memory : Fin 32)
    (first last : MachineState (totalStates 1 (states+16)))
    (trace : List (MachineState (totalStates 1 (states+16))))
    (run : PSTRTMSeq005.RunsFrom (loopMachine body) first trace last) :
    PSTRTMSeq005.RunsFrom (rawLoopMachine body)
      (blockCfg (savedPhase memory)
        (padCfg (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states) first))
      ((trace.map (padCfg (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states))).map
        (blockCfg (savedPhase memory)))
      (blockCfg (savedPhase memory)
        (padCfg (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states) last)) := by
  have hp := pad_runsFrom
    (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states)
    (loopMachine body) first last trace run
  have hf := hp
  change PSTRTMSeq005.RunsFrom (padMachine _ (loopMachine body)) _ _ _ at hf
  have family : rawLoopFamily body (savedPhase memory)=
      padMachine (by unfold rawLoopCapacity;omega : totalStates 1 (states+16)≤rawLoopCapacity states)
        (loopMachine body) := by simp [rawLoopFamily,savedPhase]
  rw [←family] at hf
  exact block_runsFrom (rawLoopFamily body) (rawLoopPorts states) (savedPhase memory) _ _ _ hf
    (by simp [rawLoopPorts,savedPhase])

theorem rawLoop_saved_final_label {states : Nat} (body : Machine states)
    (memory : Fin 32) (sx : Bool) (bank : List Bool) :
    (rawLoopSavedFinal body memory sx bank).q.val=
      (memory.val+1)*(rawLoopCapacity states+1)+7 := by
  simp [rawLoopSavedFinal,blockCfg,label,savedPhase,padCfg,padLabel,loopFinal,
    popNxEmpty,ROOTTMGCDPop016.state]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025
