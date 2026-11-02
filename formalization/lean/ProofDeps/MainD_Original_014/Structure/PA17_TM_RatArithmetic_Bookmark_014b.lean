module
public import Structure.PA17_TM_RatArithmetic_Bookmark_014a

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
open PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

def memoryPhase (stage : Fin 12) (memory : Fin 32) : Fin 384 :=
  ⟨stage.val*32+memory.val,by have hs:=stage.isLt;have hm:=memory.isLt;omega⟩
def stageOf (phase : Fin 384) : Fin 12 := ⟨phase.val/32,by have h:=phase.isLt;omega⟩
def memoryOf (phase : Fin 384) : Fin 32 := ⟨phase.val%32,Nat.mod_lt _ (by decide)⟩

theorem stageOf_memoryPhase (stage : Fin 12) (memory : Fin 32) : stageOf (memoryPhase stage memory)=stage := by
  apply Fin.ext
  change (stage.val*32+memory.val)/32=stage.val
  omega
theorem memoryOf_memoryPhase (stage : Fin 12) (memory : Fin 32) : memoryOf (memoryPhase stage memory)=memory := by
  apply Fin.ext
  change (stage.val*32+memory.val)%32=memory.val
  omega

def saveBit (memory : Fin 32) (weight : Nat) (bit : Bool) : Fin 32 :=
  ⟨(memory.val+(if bit then weight else 0))%32,Nat.mod_lt _ (by decide)⟩
def readWeight (stage : Fin 12) : Nat :=
  match stage.val with
  | 2 => 1
  | 4 => 2
  | 6 => 4
  | 8 => 8
  | 10 => 16
  | _ => 0
def IsRead (stage : Fin 12) : Prop := stage.val=2 ∨ stage.val=4 ∨ stage.val=6 ∨ stage.val=8 ∨ stage.val=10
instance (stage : Fin 12) : Decidable (IsRead stage) :=
  inferInstanceAs (Decidable (stage.val=2 ∨ stage.val=4 ∨ stage.val=6 ∨ stage.val=8 ∨ stage.val=10))

def stageMachine (stage : Fin 12) : Machine 5 :=
  match stage.val with
  | 0 => padMachine (by decide : 4≤5) markerMachine
  | 1 => fieldBackMachine
  | 2 => padMachine (by decide : 2≤5) readClearMachine
  | 3 => fieldBackMachine
  | 4 => padMachine (by decide : 2≤5) readClearMachine
  | 5 => padMachine (by decide : 2≤5) headerBackMachine
  | 6 => padMachine (by decide : 2≤5) readClearMachine
  | 7 => fieldBackMachine
  | 8 => padMachine (by decide : 2≤5) readClearMachine
  | 9 => fieldBackMachine
  | 10 => padMachine (by decide : 2≤5) readClearMachine
  | _ => fun _ _ => none

def family (phase : Fin 384) : Machine 5 := stageMachine (stageOf phase)
def nextStage (stage : Fin 12) (h : stage.val<11) : Fin 12 := ⟨stage.val+1,by omega⟩
def ports (phase : Fin 384) (localLabel : Fin 6) : Option (Fin 384 × Fin 6) :=
  let stage:=stageOf phase
  let memory:=memoryOf phase
  if h : stage.val<11 then
    let updated := if IsRead stage then saveBit memory (readWeight stage) (decide (localLabel.val=2)) else memory
    some (memoryPhase (nextStage stage h) updated,0)
  else none

/-- ONE fixed finite-control program. Twelve code stages times thirty-two
memory values times six local labels. Initial numeric label0 is independent
of all rationals; only actual read/HALT ports update the five saved bits. -/
def bookmarkMachine : Machine 2303 := blockMachine family ports
def memoryCfg (stage : Fin 12) (memory : Fin 32) (localState : MachineState 5) : MachineState 2303 :=
  blockCfg (memoryPhase stage memory) localState

theorem family_memoryPhase (stage : Fin 12) (memory : Fin 32) :
    family (memoryPhase stage memory)=stageMachine stage := by
  simp only [family,stageOf_memoryPhase]

theorem family_read (stage : Fin 12) (memory : Fin 32) (hr : IsRead stage) :
    family (memoryPhase stage memory)=padMachine (by decide : 2≤5) readClearMachine := by
  rw [family_memoryPhase]
  fin_cases stage <;> simp_all [IsRead,stageMachine] <;> rfl

theorem ports_read (stage : Fin 12) (memory : Fin 32) (bit : Bool) (hr : IsRead stage)
    (hnext : stage.val<11) :
    ports (memoryPhase stage memory) (padLabel (by decide : 2≤5) (readPort bit)) =
      some (memoryPhase (nextStage stage hnext) (saveBit memory (readWeight stage) bit),0) := by
  cases bit <;> simp [ports,stageOf_memoryPhase,memoryOf_memoryPhase,hr,hnext,padLabel,readPort]

def readBlockTrace (stage : Fin 12) (memory : Fin 32) (archive : List Bool) (bit : Bool) (suffix : List Bool) :
    List (MachineState 2303) :=
  ((readClearTrace archive bit suffix).map (padCfg (by decide : 2≤5))).map (blockCfg (memoryPhase stage memory))

theorem read_block_segment (stage : Fin 12) (memory : Fin 32) (archive : List Bool) (bit : Bool)
    (suffix : List Bool) (hr : IsRead stage) :
    Segment bookmarkMachine
      (memoryCfg stage memory (padCfg (by decide : 2≤5) (readState 0 archive (bit::suffix))))
      (readBlockTrace stage memory archive bit suffix)
      (memoryCfg stage memory (padCfg (by decide : 2≤5) (readState (readPort bit) archive (false::suffix)))) := by
  have h := pad_runsFrom (by decide : 2≤5) readClearMachine _ _ _ (readClear_runsFrom archive bit suffix)
  have hh : PSTRTMSeq005.RunsFrom (family (memoryPhase stage memory))
      (padCfg (by decide : 2≤5) (readState 0 archive (bit::suffix)))
      ((readClearTrace archive bit suffix).map (padCfg (by decide : 2≤5)))
      (padCfg (by decide : 2≤5) (readState (readPort bit) archive (false::suffix))) := by
    rw [family_read stage memory hr]
    exact h
  exact block_segment family ports (memoryPhase stage memory) _ _ _ hh

/-- The observed bit enters memory only at this real write-self transfer,
after the actual read/write step has chosen its finite HALT label. -/
theorem read_block_transfer (stage : Fin 12) (memory : Fin 32) (archive : List Bool) (bit : Bool)
    (suffix : List Bool) (hr : IsRead stage) (hnext : stage.val<11) :
    Turing.TM0.step bookmarkMachine
      (memoryCfg stage memory (padCfg (by decide : 2≤5) (readState (readPort bit) archive (false::suffix)))) =
      some (memoryCfg (nextStage stage hnext) (saveBit memory (readWeight stage) bit)
        ⟨0,Turing.Tape.mk₂ archive (false::suffix)⟩) := by
  have h := pad_runsFrom (by decide : 2≤5) readClearMachine _ _ _ (readClear_runsFrom archive bit suffix)
  have hh : Turing.TM0.step (family (memoryPhase stage memory))
      (padCfg (by decide : 2≤5) (readState (readPort bit) archive (false::suffix)))=none := by
    rw [family_read stage memory hr]
    exact h.2.2.2
  exact block_transfer family ports (memoryPhase stage memory) _ _ hh (ports_read stage memory bit hr hnext)

theorem readBlockTrace_length (stage : Fin 12) (memory : Fin 32) (archive : List Bool) (bit : Bool)
    (suffix : List Bool) : (readBlockTrace stage memory archive bit suffix).length=2 := by
  change (((readClearTrace archive bit suffix).map (padCfg (by decide : 2≤5))).map
    (blockCfg (memoryPhase stage memory))).length=2
  rw [List.length_map,List.length_map]
  rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
