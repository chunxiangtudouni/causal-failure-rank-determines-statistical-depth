module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038a

/-! Arbitrary incoming finite carry survives a real cached-bit read and
both physical restores. The saved observation occupies actual control
ports; it never overwrites a pre-existing32/64-row caller memory bit. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006

def rows (p : Nat) (localMachine : Machine 4) : Fin (p+1) → Machine 4 := fun _ => localMachine
def ports (p : Nat) : Fin (p+1) → Fin 5 → Option (Fin (p+1) × Fin 5) := fun _ _ => none
def familyMachine (p : Nat) (localMachine : Machine 4) : Machine (totalStates p 4) :=
  blockMachine (rows p localMachine) (ports p)

def readFamily (p : Nat) : Machine (totalStates p 4) := familyMachine p readMachine
def restoreFamily (p : Nat) : Machine (totalStates p 4) := familyMachine p restoreMachine
def restoreAgainFamily (p : Nat) : Machine (totalStates p 4) := familyMachine p restoreAgainMachine
def roundFamily (p : Nat) : Machine (totalStates p 4) := familyMachine p roundMachine

theorem family_runs (p : Nat) (localMachine : Machine 4) (memory : Fin (p+1))
    (first last : MachineState 4) (trace : List (MachineState 4))
    (run : PSTRTMSeq005.RunsFrom localMachine first trace last) :
    PSTRTMSeq005.RunsFrom (familyMachine p localMachine) (blockCfg memory first)
      (trace.map (blockCfg memory)) (blockCfg memory last) :=
  block_runsFrom (rows p localMachine) (ports p) memory first last trace run rfl

theorem read_family_runs (p : Nat) (memory : Fin (p+1)) (left : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (readFamily p) (blockCfg memory (state 0 left (bit::suffix)))
      ((readTrace left bit suffix).map (blockCfg memory))
      (blockCfg memory (state (savedPort bit) left (false::suffix))) :=
  family_runs p readMachine memory _ _ _ (read_runsFrom left bit suffix)

theorem restore_family_runs (p : Nat) (memory : Fin (p+1)) (left : List Bool) (old bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (restoreFamily p) (blockCfg memory (state (savedPort bit) left (old::suffix)))
      ((restoreTrace left old bit suffix).map (blockCfg memory))
      (blockCfg memory (state (restoredPort bit) left (bit::suffix))) :=
  family_runs p restoreMachine memory _ _ _ (restore_runsFrom left old bit suffix)

theorem restoreAgain_family_runs (p : Nat) (memory : Fin (p+1)) (left : List Bool) (old bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (restoreAgainFamily p) (blockCfg memory (state (restoredPort bit) left (old::suffix)))
      ((restoreAgainTrace left old bit suffix).map (blockCfg memory))
      (blockCfg memory (state (savedPort bit) left (bit::suffix))) :=
  family_runs p restoreAgainMachine memory _ _ _ (restoreAgain_runsFrom left old bit suffix)

theorem round_family_runs (p : Nat) (memory : Fin (p+1)) (left : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (roundFamily p) (blockCfg memory (state 0 left (bit::suffix)))
      ((roundTrace left bit suffix).map (blockCfg memory))
      (blockCfg memory (state (restoredPort bit) left (bit::suffix))) :=
  family_runs p roundMachine memory _ _ _ (round_runsFrom left bit suffix)

theorem carry_preserved (p : Nat) (memory : Fin (p+1)) (q : Fin 5) (tape : Tape Bool) :
    phaseOf (p:=p) (s:=4) (blockCfg memory (⟨q,tape⟩ : MachineState 4)).q=memory :=
  phaseOf_label _ _

theorem saved_observation (p : Nat) (memory : Fin (p+1)) (bit : Bool) (tape : Tape Bool) :
    (localOf (p:=p) (s:=4) (blockCfg memory (⟨savedPort bit,tape⟩ : MachineState 4)).q).val=
      if bit then 2 else 1 := by
  change (localOf (p:=p) (s:=4) (label memory (savedPort bit))).val=if bit then 2 else 1
  rw [localOf_label]
  cases bit <;> rfl

theorem restored_observation (p : Nat) (memory : Fin (p+1)) (bit : Bool) (tape : Tape Bool) :
    (localOf (p:=p) (s:=4) (blockCfg memory (⟨restoredPort bit,tape⟩ : MachineState 4)).q).val=
      if bit then 4 else 3 := by
  change (localOf (p:=p) (s:=4) (label memory (restoredPort bit))).val=if bit then 4 else 3
  rw [localOf_label]
  cases bit <;> rfl

theorem entry_label (p : Nat) (memory : Fin (p+1)) (tape : Tape Bool) :
    (blockCfg memory (⟨0,tape⟩ : MachineState 4)).q.val=5*memory.val := by
  simp only [blockCfg,label,Fin.val_zero,Nat.add_zero,Nat.mul_comm]

theorem round_prefix_space (p : Nat) (memory : Fin (p+1)) (left : List Bool) (bit : Bool) (suffix : List Bool)
    (inputLength k : Nat) :
    visitedSpace (roundFamily p) inputLength (((roundTrace left bit suffix).map (blockCfg memory)).take k) ≤
      inputLength+7 := by
  have hs := PSTRTMTrace002.visitedSpace_le (roundFamily p) inputLength
    (((roundTrace left bit suffix).map (blockCfg memory)).take k)
  have hl : (((roundTrace left bit suffix).map (blockCfg memory)).take k).length≤3 := by
    simp only [List.length_take,List.length_map,roundTrace_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
