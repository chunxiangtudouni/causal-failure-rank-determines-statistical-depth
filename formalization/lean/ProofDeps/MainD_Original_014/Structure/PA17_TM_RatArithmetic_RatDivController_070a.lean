module
public import Structure.PA17_TM_RatArithmetic_DivPrefix_067b
public import Structure.PA17_TM_RatArithmetic_DivZero_068b
public import Structure.PA17_TM_RatArithmetic_RatDivSuffix_069c

/-! One finite Bool program: real division prefix, physically written zero
finish, or the unchanged057 program entered at its actual phase4. Only the
prefix HALT dispatches, by its ACTUALLY OBSERVED finite-control bit6. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivController070

open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticMulController057 (Component widen64 narrow64)
open PA17TMRatArithmeticDivPrefix067 (prefixCap prefixMachine prefixComponent prefixMemory)
open PA17TMRatArithmeticDivZero068 (zeroCap zeroMachine)
open scoped BigOperators

def normalStates : Nat := PA17TMRatArithmeticMulController057.controllerCap
def componentStates (phase : Fin 3) : Nat :=
  match phase.val with
  | 0 => prefixCap
  | 1 => zeroCap
  | _ => normalStates
def commonCap : Nat := ∑ phase : Fin 3, componentStates phase
def controllerCap : Nat := totalStates 2 commonCap
attribute [local implicit_reducible] totalStates normalStates controllerCap

def normalMachine : Machine normalStates := PA17TMRatArithmeticMulController057.mulMachine
def zeroComponent : Component := ⟨zeroCap,zeroMachine,fun _ => 0,fun _ => 0⟩
def normalComponent : Component :=
  ⟨normalStates,normalMachine,fun memory =>
    (PA17TMRatArithmeticMulController057.entryCfg (4 : Fin 17) (widen64 (narrow64 memory))
      (Tape.mk₁ [])).q,fun _ => 0⟩
def component (phase : Fin 3) : Component :=
  match phase.val with
  | 0 => prefixComponent
  | 1 => zeroComponent
  | _ => normalComponent
attribute [local implicit_reducible] component prefixComponent zeroComponent normalComponent

theorem component_states (phase : Fin 3) : (component phase).states=componentStates phase := by
  fin_cases phase <;> rfl
theorem component_fits (phase : Fin 3) : (component phase).states≤commonCap := by
  rw [component_states]
  exact Finset.single_le_sum (fun other _ => Nat.zero_le (componentStates other)) (Finset.mem_univ phase)

def family (phase : Fin 3) : Machine commonCap := padMachine (component_fits phase) (component phase).code
def localCode (phase : Fin 3) (q : Fin (commonCap+1)) : Fin ((component phase).states+1) :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex (component phase).states commonCap q
def branchPhase (memory : Fin 128) : Fin 3 := if memory.val/64=1 then 1 else 2
def ports (phase : Fin 3) (q : Fin (commonCap+1)) : Option (Fin 3 × Fin (commonCap+1)) :=
  if phase.val=0 then
    let memory := (component phase).decode (localCode phase q)
    let target := branchPhase memory
    some (target,padLabel (component_fits target) ((component target).entry memory))
  else none

/-- ONE code before ALL x,y. No zero flag, sign, width, gap or answer input. -/
def divMachine : Machine controllerCap := blockMachine family ports
def liftCfg (phase : Fin 3) (state : MachineState (component phase).states) : MachineState controllerCap :=
  blockCfg phase (padCfg (component_fits phase) state)
def entryCfg (phase : Fin 3) (memory : Fin 128) (tape : Tape Bool) : MachineState controllerCap :=
  liftCfg phase ⟨(component phase).entry memory,tape⟩
def liftTrace (phase : Fin 3) (trace : List (MachineState (component phase).states)) :
    List (MachineState controllerCap) := trace.map (liftCfg phase)

theorem localCode_pad (phase : Fin 3) (q : Fin ((component phase).states+1)) :
    localCode phase (padLabel (component_fits phase) q)=q :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex_pad (component_fits phase) q
theorem liftTrace_length (phase : Fin 3) (trace : List (MachineState (component phase).states)) :
    (liftTrace phase trace).length=trace.length := List.length_map _
theorem lift_tape (phase : Fin 3) (state : MachineState (component phase).states) :
    (liftCfg phase state).Tape=state.Tape := rfl
theorem entry_zero (memory : Fin 128) (tape : Tape Bool) :
    entryCfg (1 : Fin 3) memory tape=liftCfg (1 : Fin 3) (⟨0,tape⟩ : MachineState zeroCap) := rfl
theorem entry_normal (memory : Fin 128) (tape : Tape Bool) :
    entryCfg (2 : Fin 3) memory tape=liftCfg (2 : Fin 3)
      (PA17TMRatArithmeticMulController057.entryCfg (4 : Fin 17) (widen64 (narrow64 memory)) tape) := rfl

theorem component_segment (phase : Fin 3) (first last : MachineState (component phase).states)
    (trace : List (MachineState (component phase).states))
    (run : PSTRTMSeq005.RunsFrom (component phase).code first trace last) :
    Segment divMachine (liftCfg phase first) (liftTrace phase trace) (liftCfg phase last) := by
  have padded := pad_runsFrom (component_fits phase) (component phase).code first last trace run
  have lifted : Segment (states:=controllerCap) divMachine (liftCfg phase first)
      ((trace.map (padCfg (component_fits phase))).map (blockCfg (p:=2) (s:=commonCap) phase))
      (liftCfg phase last) := block_segment (p:=2) (s:=commonCap) family ports phase _ _ _ padded
  have maps : (trace.map (padCfg (component_fits phase))).map (blockCfg (p:=2) (s:=commonCap) phase)=
      liftTrace phase trace := by rw [List.map_map];rfl
  rw [maps] at lifted
  exact lifted

/-- Actual write-self dispatch at the prefix's true HALT; the entire tape
and head are retained, and only the genuinely decoded memory selects code. -/
theorem paid_prefix_transfer (last : MachineState prefixCap)
    (halt : TM0.step prefixMachine last=none) :
    TM0.step divMachine (liftCfg (0 : Fin 3) last)=
      some (entryCfg (branchPhase (prefixMemory last.q)) (prefixMemory last.q) last.Tape) := by
  change TM0.step (component (0 : Fin 3)).code last=none at halt
  have halted : TM0.step (family (0 : Fin 3)) (padCfg (component_fits (0 : Fin 3)) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  have port : ports (0 : Fin 3) (padCfg (component_fits (0 : Fin 3)) last).q=
      some (branchPhase (prefixMemory last.q),padLabel (component_fits (branchPhase (prefixMemory last.q)))
        ((component (branchPhase (prefixMemory last.q))).entry (prefixMemory last.q))) := by
    let choose : Fin 128 → Option (Fin 3 × Fin (commonCap+1)) := fun memory =>
      some (branchPhase memory,padLabel (component_fits (branchPhase memory))
        ((component (branchPhase memory)).entry memory))
    have decoded : (component (0 : Fin 3)).decode
        (localCode (0 : Fin 3) (padLabel (component_fits (0 : Fin 3)) last.q))=prefixMemory last.q :=
      congrArg ((component (0 : Fin 3)).decode) (localCode_pad (0 : Fin 3) last.q)
    change choose ((component (0 : Fin 3)).decode
      (localCode (0 : Fin 3) (padLabel (component_fits (0 : Fin 3)) last.q)))=choose (prefixMemory last.q)
    exact congrArg choose decoded
  change TM0.step (blockMachine (p:=2) (s:=commonCap) family ports)
      (blockCfg (p:=2) (s:=commonCap) (0 : Fin 3) (padCfg (component_fits (0 : Fin 3)) last))=
    some (blockCfg (p:=2) (s:=commonCap) (branchPhase (prefixMemory last.q))
      (⟨padLabel (component_fits (branchPhase (prefixMemory last.q)))
        ((component (branchPhase (prefixMemory last.q))).entry (prefixMemory last.q)),last.Tape⟩ : MachineState commonCap))
  exact block_transfer (p:=2) (s:=commonCap) family ports (0 : Fin 3)
    (padCfg (component_fits (0 : Fin 3)) last)
    (branchPhase (prefixMemory last.q),padLabel (component_fits (branchPhase (prefixMemory last.q)))
      ((component (branchPhase (prefixMemory last.q))).entry (prefixMemory last.q))) halted port

theorem terminal_halt (phase : Fin 3) (hphase : phase.val≠0)
    (last : MachineState (component phase).states) (halt : TM0.step (component phase).code last=none) :
    TM0.step divMachine (liftCfg phase last)=none := by
  have halted : TM0.step (family phase) (padCfg (component_fits phase) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  exact block_halt (p:=2) (s:=commonCap) family ports phase _ halted (by simp only [ports,ite_eq_right hphase])

theorem terminal_runs (phase : Fin 3) (hphase : phase.val≠0)
    (first last : MachineState (component phase).states) (trace : List (MachineState (component phase).states))
    (run : PSTRTMSeq005.RunsFrom (component phase).code first trace last) :
    PSTRTMSeq005.RunsFrom divMachine (liftCfg phase first) (liftTrace phase trace) (liftCfg phase last) :=
  segment_runsFrom _ _ _ _ (component_segment phase first last trace run)
    (terminal_halt phase hphase last run.2.2.2)

theorem initial_mapped (input : List Bool) :
    liftCfg (0 : Fin 3) (TM0.init input : MachineState prefixCap)=(TM0.init input : MachineState controllerCap) := by
  change blockCfg (0 : Fin 3) (padCfg (component_fits (0 : Fin 3))
    (⟨0,Tape.mk₁ input⟩ : MachineState prefixCap))=(⟨0,Tape.mk₁ input⟩ : MachineState controllerCap)
  rw [PA17TMRatArithmeticBookmark014.pad_zero,blockCfg_zero]

theorem join_prefix (input : List Bool) (tp : List (MachineState prefixCap)) (lastP : MachineState prefixCap)
    (prefixRun : PSTRTMSeq005.RunsFrom prefixMachine (TM0.init input) tp lastP)
    (first last : MachineState controllerCap) (tail : List (MachineState controllerCap))
    (tailRun : PSTRTMSeq005.RunsFrom divMachine first tail last)
    (step : TM0.step divMachine (liftCfg (0 : Fin 3) lastP)=some first) :
    Runs divMachine input (liftTrace (0 : Fin 3) tp++tail) last := by
  have sp := component_segment (0 : Fin 3) _ _ _ prefixRun
  have initialSegment : Segment divMachine (TM0.init input) (liftTrace (0 : Fin 3) tp)
      (liftCfg (0 : Fin 3) lastP) :=
    ⟨sp.1.trans (congrArg some (initial_mapped input)),sp.2.1,sp.2.2⟩
  have st : Segment divMachine first tail last := ⟨tailRun.1,tailRun.2.1,tailRun.2.2.1⟩
  have joined := segment_append divMachine _ _ _ _ _ _ initialSegment st step
  exact PSTRTMTrace002.runs_of_chain _ _ _ _ joined.1 joined.2.1 joined.2.2 tailRun.2.2.2

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivController070
