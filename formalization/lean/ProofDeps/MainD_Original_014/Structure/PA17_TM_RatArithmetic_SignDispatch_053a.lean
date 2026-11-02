module
public import Structure.PA17_TM_RatArithmetic_OutputFinish_044c
public import Structure.PA17_TM_RatArithmetic_BankWalk_033b

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignDispatch053
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticOutputFinish044
attribute [local implicit_reducible] outputCap

def memoryPhase (memory : Fin 128) : Fin 129 := ⟨memory.val,by have h:=memory.isLt;omega⟩
def dispatchCap (j : Nat) : Nat := totalStates 128 (outputCap j)
attribute [local implicit_reducible] dispatchCap
theorem identity_fits (j : Nat) : 0≤outputCap j := Nat.zero_le _

/-- All128 incoming control rows contain only the same genuine identity
HALT. The output/cleanup body occurs ONCE, in shared phase128. -/
def dispatchFamily (j : Nat) (phase : Fin 129) : Machine (outputCap j) :=
  if phase.val<128 then padMachine (identity_fits j) identityMachine else outputFinishMachine j

/-- signTable is a compiled finite table, fixed before all actual tapes.
It is not an original sign field or a runtime sign-answer argument. -/
def dispatchPorts (j : Nat) (signTable : Fin 128→Bool) (phase : Fin 129) (_q : Fin (outputCap j+1)) :
    Option (Fin 129 × Fin (outputCap j+1)) :=
  if h : phase.val<128 then some (128,outputEntry j (signTable ⟨phase.val,h⟩)) else none

def dispatchMachine (j : Nat) (signTable : Fin 128→Bool) : Machine (dispatchCap j) :=
  blockMachine (dispatchFamily j) (dispatchPorts j signTable)

def dispatchEntry (j : Nat) (memory : Fin 128) : Fin (dispatchCap j+1) :=
  label (memoryPhase memory) (padLabel (identity_fits j) (0 : Fin 1))
def entryState (j : Nat) (memory : Fin 128) (tape : Tape Bool) : MachineState (dispatchCap j) :=
  blockCfg (memoryPhase memory) (padCfg (identity_fits j) (⟨0,tape⟩ : MachineState 0))
def bodyState (j : Nat) (q : Fin (outputCap j+1)) (tape : Tape Bool) : MachineState (dispatchCap j) :=
  blockCfg (128 : Fin 129) (⟨q,tape⟩ : MachineState (outputCap j))
def dispatchPort (j : Nat) : Fin (dispatchCap j+1) := label (128 : Fin 129) (outputPort j)

theorem family_memory (j : Nat) (memory : Fin 128) :
    dispatchFamily j (memoryPhase memory)=padMachine (identity_fits j) identityMachine := by
  simp [dispatchFamily,memoryPhase,memory.isLt]
theorem family_body (j : Nat) : dispatchFamily j (128 : Fin 129)=outputFinishMachine j := rfl
theorem ports_memory (j : Nat) (signTable : Fin 128→Bool) (memory : Fin 128) (q : Fin (outputCap j+1)) :
    dispatchPorts j signTable (memoryPhase memory) q=some (128,outputEntry j (signTable memory)) := by
  simp [dispatchPorts,memoryPhase,memory.isLt]
theorem ports_body (j : Nat) (signTable : Fin 128→Bool) (q : Fin (outputCap j+1)) :
    dispatchPorts j signTable (128 : Fin 129) q=none := rfl

/-- The only entry action is a REAL write-self transfer at the same head
and ENTIRE Tape. A prior actual producer must enter dispatchEntry memory. -/
theorem dispatch_step (j : Nat) (signTable : Fin 128→Bool) (memory : Fin 128) (tape : Tape Bool) :
    TM0.step (dispatchMachine j signTable) (entryState j memory tape)=
      some (bodyState j (outputEntry j (signTable memory)) tape) := by
  have halt : TM0.step (dispatchFamily j (memoryPhase memory))
      (padCfg (identity_fits j) (⟨0,tape⟩ : MachineState 0))=none := by
    rw [family_memory]
    simp only [pad_step,show TM0.step identityMachine (⟨0,tape⟩ : MachineState 0)=none from rfl,
      Option.map_none]
  exact block_transfer (dispatchFamily j) (dispatchPorts j signTable) (memoryPhase memory)
    (padCfg (identity_fits j) (⟨0,tape⟩ : MachineState 0))
    (128,outputEntry j (signTable memory)) halt (ports_memory j signTable memory _)

theorem dispatchCap_eq (j : Nat) : dispatchCap j=18576*j+60371 := by
  simp only [dispatchCap,totalStates,outputCap_eq]
  omega
theorem dispatchEntry_value (j : Nat) (memory : Fin 128) :
    (dispatchEntry j memory).val=memory.val*(outputCap j+1) := by
  simp only [dispatchEntry,label,memoryPhase,padLabel,Fin.val_zero,Nat.add_zero]
theorem entryState_q (j : Nat) (memory : Fin 128) (tape : Tape Bool) :
    (entryState j memory tape).q=dispatchEntry j memory := rfl
theorem bodyState_label (j : Nat) (q : Fin (outputCap j+1)) (tape : Tape Bool) :
    (bodyState j q tape).q.val=128*(outputCap j+1)+q.val := rfl
theorem entryState_tape (j : Nat) (memory : Fin 128) (tape : Tape Bool) :
    (entryState j memory tape).Tape=tape := rfl
theorem bodyState_tape (j : Nat) (q : Fin (outputCap j+1)) (tape : Tape Bool) :
    (bodyState j q tape).Tape=tape := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignDispatch053
