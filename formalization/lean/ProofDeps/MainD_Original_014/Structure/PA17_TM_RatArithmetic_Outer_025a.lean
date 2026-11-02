module
public import Structure.PA17_TM_RatArithmetic_Width_018c
public import Common.ROOT_TM_GCD_PopTrace_017
public import Structure.PA17_TM_Division_Compose_006a

/-! The real outer-counter branch used by the allocation loop. One mark is
removed by the frozen physical popper. A found mark performs an actual
write-self transfer and seven RIGHT moves to Nx; empty returns by a distinct
real HALT at the original input header. No count or zero flag is supplied. -/
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018

def popNxFamily (phase : Fin 2) : Machine 7 :=
  if phase.val=0 then ROOTTMGCDPop016.popMachine else sevenMachine .right

def popNxPorts (phase : Fin 2) (q : Fin 8) : Option (Fin 2 × Fin 8) :=
  if phase.val=0 ∧ q.val=6 then some (1,0) else none

def popNxMachine : Machine 15 := blockMachine popNxFamily popNxPorts

def popNxInitial (h : Nat) (sx : Bool) (bank : List Bool) : MachineState 15 :=
  blockCfg (0 : Fin 2) (ROOTTMGCDPop016.state 0
    (false::ROOTTMGCDPop016.ones h) (prefixRight sx bank))

def popNxFound (h : Nat) (sx : Bool) (bank : List Bool) : MachineState 15 :=
  blockCfg (1 : Fin 2) (sevenState 7
    (prefixLeft sx (false::ROOTTMGCDPop016.ones h)) bank)

def popNxEmpty (sx : Bool) (bank : List Bool) : MachineState 15 :=
  blockCfg (0 : Fin 2) (ROOTTMGCDPop016.state 7 [false] (prefixRight sx bank))

def popNxSuccTrace (h : Nat) (sx : Bool) (bank : List Bool) : List (MachineState 15) :=
  (ROOTTMGCDPop016.succTrace h (prefixRight sx bank)).map (blockCfg (0 : Fin 2)) ++
    (rightSevenTrace sx (false::ROOTTMGCDPop016.ones h) bank).map (blockCfg (1 : Fin 2))

def popNxZeroTrace (sx : Bool) (bank : List Bool) : List (MachineState 15) :=
  (ROOTTMGCDPop016.zeroTrace (prefixRight sx bank)).map (blockCfg (0 : Fin 2))

theorem popNx_succ_runsFrom (h : Nat) (sx : Bool) (bank : List Bool) :
    PSTRTMSeq005.RunsFrom popNxMachine (popNxInitial (h+1) sx bank)
      (popNxSuccTrace h sx bank) (popNxFound h sx bank) := by
  have hp : PSTRTMSeq005.RunsFrom (popNxFamily (0 : Fin 2))
      (ROOTTMGCDPop016.state 0 (false::ROOTTMGCDPop016.ones (h+1)) (prefixRight sx bank))
      (ROOTTMGCDPop016.succTrace h (prefixRight sx bank))
      (ROOTTMGCDPop016.state 6 (false::ROOTTMGCDPop016.ones h) (prefixRight sx bank)) := by
    simpa [popNxFamily] using
      ROOTTMGCDPop016.pop_succ_runsFrom h (prefixRight sx bank)
  have hr : PSTRTMSeq005.RunsFrom (popNxFamily (1 : Fin 2))
      (sevenState 0 (false::ROOTTMGCDPop016.ones h) (prefixRight sx bank))
      (rightSevenTrace sx (false::ROOTTMGCDPop016.ones h) bank)
      (sevenState 7 (prefixLeft sx (false::ROOTTMGCDPop016.ones h)) bank) := by
    simpa [popNxFamily] using rightSeven_runsFrom sx (false::ROOTTMGCDPop016.ones h) bank
  have hs := block_segment popNxFamily popNxPorts (0 : Fin 2) _ _ _ hp
  have ht := block_segment popNxFamily popNxPorts (1 : Fin 2) _ _ _ hr
  have hx := block_transfer popNxFamily popNxPorts (0 : Fin 2)
    (ROOTTMGCDPop016.state 6 (false::ROOTTMGCDPop016.ones h) (prefixRight sx bank))
    (1,0) hp.2.2.2 (by simp [popNxPorts,ROOTTMGCDPop016.state])
  have hf := segment_append popNxMachine _ _ _ _ _ _ hs ht hx
  apply segment_runsFrom _ _ _ _ hf
  exact block_halt popNxFamily popNxPorts (1 : Fin 2) _ hr.2.2.2 (by simp [popNxPorts])

theorem popNx_zero_runsFrom (sx : Bool) (bank : List Bool) :
    PSTRTMSeq005.RunsFrom popNxMachine (popNxInitial 0 sx bank)
      (popNxZeroTrace sx bank) (popNxEmpty sx bank) := by
  have hp : PSTRTMSeq005.RunsFrom (popNxFamily (0 : Fin 2))
      (ROOTTMGCDPop016.state 0 [false] (prefixRight sx bank))
      (ROOTTMGCDPop016.zeroTrace (prefixRight sx bank))
      (ROOTTMGCDPop016.state 7 [false] (prefixRight sx bank)) := by
    simpa [popNxFamily] using
      ROOTTMGCDPop016.pop_zero_runsFrom (prefixRight sx bank)
  exact block_runsFrom popNxFamily popNxPorts (0 : Fin 2) _ _ _ hp
    (by simp [popNxPorts,ROOTTMGCDPop016.state])

theorem popNx_initial_label (h : Nat) (sx : Bool) (bank : List Bool) :
    (popNxInitial h sx bank).q=0 := rfl

theorem popNx_found_label (h : Nat) (sx : Bool) (bank : List Bool) :
    (popNxFound h sx bank).q=15 := rfl

theorem popNx_empty_label (sx : Bool) (bank : List Bool) :
    (popNxEmpty sx bank).q=7 := rfl

theorem popNx_succ_length (h : Nat) (sx : Bool) (bank : List Bool) :
    (popNxSuccTrace h sx bank).length=2*h+16 := by
  simp only [popNxSuccTrace,List.length_append,List.length_map,ROOTTMGCDPop016.succ_length]
  rfl

theorem popNx_zero_length (sx : Bool) (bank : List Bool) :
    (popNxZeroTrace sx bank).length=5 := by
  simp only [popNxZeroTrace,List.length_map,ROOTTMGCDPop016.zeroTrace]
  rfl

theorem popNx_succ_prefix_space (h : Nat) (sx : Bool) (bank : List Bool)
    (prefixLength inputLength : Nat) :
    visitedSpace popNxMachine inputLength ((popNxSuccTrace h sx bank).take prefixLength) ≤
      inputLength+4*h+33 := by
  have hs := PSTRTMTrace002.visitedSpace_le popNxMachine inputLength
    ((popNxSuccTrace h sx bank).take prefixLength)
  have hp : ((popNxSuccTrace h sx bank).take prefixLength).length≤2*h+16 := by
    rw [List.length_take,popNx_succ_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025
