module
public import Structure.PA17_TM_RatArithmetic_MulStart_049a

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticOuter025 PA17TMRatArithmeticSignRead021

def allocatorCap (k : Nat) : Nat := totalStates 32 (rawLoopCapacity (PA17TMRatArithmeticAllocatePass023.passCap k))
def allocatorMachine (k : Nat) : Machine (allocatorCap k) :=
  rawLoopMachine (PA17TMRatArithmeticAllocatePass023.passMachine k)
def stageCap (k : Nat) : Nat := allocatorCap k+479+511
def mulStartCap (k : Nat) : Nat := totalStates 2 (stageCap k)
attribute [local implicit_reducible] allocatorCap stageCap mulStartCap

theorem allocator_le_stage (k : Nat) : allocatorCap k≤stageCap k := by unfold stageCap;omega
theorem read_le_stage (k : Nat) : 479≤stageCap k := by unfold stageCap;omega
theorem home_le_stage (k : Nat) : 511≤stageCap k := by unfold stageCap;omega

def decodeAllocatorMemory (k : Nat) (q : Fin (stageCap k+1)) : Fin 32 :=
  ⟨((q.val/(rawLoopCapacity (PA17TMRatArithmeticAllocatePass023.passCap k)+1))-1)%32,
    Nat.mod_lt _ (by decide)⟩

theorem decodeAllocatorMemory_actual (k : Nat) (memory : Fin 32) (sx : Bool) (bank : List Bool) :
    decodeAllocatorMemory k (padLabel (allocator_le_stage k)
      (rawLoopSavedFinal (PA17TMRatArithmeticAllocatePass023.passMachine k) memory sx bank).q)=memory := by
  apply Fin.ext
  change (((rawLoopSavedFinal (PA17TMRatArithmeticAllocatePass023.passMachine k) memory sx bank).q.val /
    (rawLoopCapacity (PA17TMRatArithmeticAllocatePass023.passCap k)+1))-1)%32=memory.val
  rw [rawLoop_saved_final_label]
  have hsmall : 7<rawLoopCapacity (PA17TMRatArithmeticAllocatePass023.passCap k)+1 := by
    unfold rawLoopCapacity;omega
  rw [Nat.mul_comm (memory.val+1),Nat.mul_add_div (by omega),Nat.div_eq_of_lt hsmall,Nat.add_zero]
  simp only [Nat.add_sub_cancel,Nat.mod_eq_of_lt memory.isLt]

def readCode (k : Nat) (q : Fin (stageCap k+1)) : Fin 480 :=
  ⟨q.val%480,Nat.mod_lt _ (by decide)⟩

theorem readCode_pad (k : Nat) (q : Fin 480) : readCode k (padLabel (read_le_stage k) q)=q := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt q.isLt

def startFamily (k : Nat) (phase : Fin 3) : Machine (stageCap k) :=
  if phase.val=0 then padMachine (allocator_le_stage k) (allocatorMachine k)
  else if phase.val=1 then padMachine (read_le_stage k) readMemoryMachine
  else padMachine (home_le_stage k) homeMemoryMachine

def startPorts (k : Nat) (phase : Fin 3) (q : Fin (stageCap k+1)) :
    Option (Fin 3 × Fin (stageCap k+1)) :=
  if phase.val=0 then some (1,padLabel (read_le_stage k) (label (decodeAllocatorMemory k q) (0 : Fin 15)))
  else if phase.val=1 then some (2,padLabel (home_le_stage k)
    (label (decodeReadMemory (readCode k q)) (0 : Fin 8))) else none

/-- Fixed K code. Neither the saved five bits nor the observed sx is a
caller argument: both port tables consume real finite-control exits. -/
def mulStartMachine (k : Nat) : Machine (mulStartCap k) := blockMachine (startFamily k) (startPorts k)

def allocated (k : Nat) (memory : Fin 32) (sx : Bool) (bank : List Bool) : MachineState (mulStartCap k) :=
  blockCfg (0 : Fin 3) (padCfg (allocator_le_stage k)
    (rawLoopSavedFinal (PA17TMRatArithmeticAllocatePass023.passMachine k) memory sx bank))
def readInitial (k : Nat) (memory : Fin 32) (sx : Bool) (counter bank : List Bool) : MachineState (mulStartCap k) :=
  blockCfg (1 : Fin 3) (padCfg (read_le_stage k)
    (readMemoryInitial memory (Tape.mk₂ counter (prefixRight sx bank))))
def readFinal (k : Nat) (memory : Fin 32) (sx : Bool) (counter bank : List Bool) : MachineState (mulStartCap k) :=
  blockCfg (1 : Fin 3) (padCfg (read_le_stage k)
    (readMemoryFinal memory sx (Tape.mk₂ (prefixLeft sx counter) bank)))
def homeInitial (k : Nat) (memory : Fin 64) (sx : Bool) (counter bank : List Bool) : MachineState (mulStartCap k) :=
  blockCfg (2 : Fin 3) (padCfg (home_le_stage k)
    (homeMemoryInitial memory (Tape.mk₂ (prefixLeft sx counter) bank)))
def homeFinal (k : Nat) (memory : Fin 64) (sx : Bool) (counter bank : List Bool) : MachineState (mulStartCap k) :=
  blockCfg (2 : Fin 3) (padCfg (home_le_stage k)
    (homeMemoryFinal memory (Tape.mk₂ counter (prefixRight sx bank))))

theorem mulStartCap_eq (k : Nat) : mulStartCap k=23760*k+7968608 := by
  unfold mulStartCap stageCap allocatorCap rawLoopCapacity PA17TMRatArithmeticAllocatePass023.passCap totalStates
  omega

theorem homeFinal_label (k : Nat) (memory : Fin 64) (sx : Bool) (counter bank : List Bool) :
    (homeFinal k memory sx counter bank).q.val=2*(stageCap k+1)+8*memory.val+7 := by
  change 2*(stageCap k+1)+(homeMemoryFinal memory (Tape.mk₂ counter (prefixRight sx bank))).q.val=_
  rw [homeMemoryFinal_label]
  omega

theorem homeFinal_tape (k : Nat) (memory : Fin 64) (sx : Bool) (counter bank : List Bool) :
    (homeFinal k memory sx counter bank).Tape=Tape.mk₂ counter (prefixRight sx bank) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049
