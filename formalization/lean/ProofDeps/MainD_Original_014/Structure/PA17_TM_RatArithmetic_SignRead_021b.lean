module
public import Structure.PA17_TM_RatArithmetic_SignRead_021a

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignRead021

open PA17TMDivisionCompose006

def memoryFamily (_memory : Fin 32) : Machine 6 := sensorMachine
def memoryPorts (_memory : Fin 32) (_localLabel : Fin 7) : Option (Fin 32 × Fin 7) := none

/-- Thirty-two existing control memories, each executing the SAME real
read kernel. The 64 final ports carry the old five bits plus the observed sx.
The caller must reach the appropriate old-memory entry by actual control;
no saved-bit tuple or relabeling is supplied to an original Rat input. -/
def memoryMachine : Machine 223 := blockMachine memoryFamily memoryPorts

def memoryInitial (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) : MachineState 223 :=
  blockCfg memory (sensorInitial archive bit right)

def memoryHalt (memory : Fin 32) (bit : Bool) : Fin 224 := label memory (readPort bit)

def memoryFinal (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) : MachineState 223 :=
  blockCfg memory (sensorFinal archive bit right)

def memoryTrace (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) : List (MachineState 223) :=
  (sensorTrace archive bit right).map (blockCfg memory)

theorem memory_runsFrom (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) :
    PSTRTMSeq005.RunsFrom memoryMachine (memoryInitial memory archive bit right)
      (memoryTrace memory archive bit right) (memoryFinal memory archive bit right) :=
  block_runsFrom memoryFamily memoryPorts memory _ _ _ (sensor_runsFrom archive bit right) rfl

theorem memory_same_tape (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) :
    (memoryFinal memory archive bit right).Tape = (memoryInitial memory archive bit right).Tape := rfl

theorem memory_initial_label (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) :
    (memoryInitial memory archive bit right).q.val = 7*memory.val := by
  simp [memoryInitial,sensorInitial,sensorState,blockCfg,label,Nat.mul_comm]

theorem memory_final_label (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) :
    (memoryFinal memory archive bit right).q.val = 7*memory.val+(if bit then 6 else 5) := by
  cases bit <;> simp [memoryFinal,sensorFinal,sensorState,readPort,blockCfg,label,Nat.mul_comm]

def selectedMemory (memory : Fin 32) (bit : Bool) : Fin 64 :=
  ⟨memory.val+(if bit then 32 else 0),by have h:=memory.isLt; split <;> omega⟩

/-- A fixed decoder of finite HALT labels, suitable as the next controller's
static port table. It is not a numeric oracle or a runtime tape operation. -/
def decodedMemory (q : Fin 224) : Fin 64 :=
  ⟨(phaseOf (p:=31) (s:=6) q).val+(if (localOf (p:=31) (s:=6) q).val=6 then 32 else 0),
    by have h:=(phaseOf (p:=31) (s:=6) q).isLt; split <;> omega⟩

theorem decoded_actual_port (memory : Fin 32) (bit : Bool) :
    decodedMemory (memoryHalt memory bit) = selectedMemory memory bit := by
  apply Fin.ext
  simp only [decodedMemory,memoryHalt,phaseOf_label,localOf_label,selectedMemory]
  cases bit <;> rfl

theorem memory_final_decoded (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) :
    decodedMemory (memoryFinal memory archive bit right).q = selectedMemory memory bit :=
  decoded_actual_port memory bit

theorem selectedMemory_relation (memory : Fin 32) (bit : Bool) :
    (selectedMemory memory bit).val = memory.val+32*(if bit then 1 else 0) := by
  cases bit <;> simp [selectedMemory]

theorem selectedMemory_retains_old (memory : Fin 32) (bit : Bool) :
    (selectedMemory memory bit).val%32 = memory.val := by
  have h:=memory.isLt
  cases bit <;> simp [selectedMemory]

theorem selectedMemory_observed_sign (memory : Fin 32) (bit : Bool) :
    (selectedMemory memory bit).val/32 = if bit then 1 else 0 := by
  have h:=memory.isLt
  cases bit <;> simp [selectedMemory]

/-- All 64 combinations are physically distinct HALT labels. -/
theorem memoryHalt_injective (first second : Fin 32) (a b : Bool)
    (same : memoryHalt first a = memoryHalt second b) : first=second ∧ a=b := by
  have hm : first=second := by
    simpa only [memoryHalt,phaseOf_label] using congrArg (phaseOf (p:=31) (s:=6)) same
  have hp : readPort a=readPort b := by
    simpa only [memoryHalt,localOf_label] using congrArg (localOf (p:=31) (s:=6)) same
  cases a <;> cases b <;> simp_all [readPort]

theorem memoryTrace_length (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool) :
    (memoryTrace memory archive bit right).length = 5 := by
  simp only [memoryTrace,List.length_map,sensorTrace_length]

theorem memory_prefix_space (memory : Fin 32) (archive : List Bool) (bit : Bool) (right : List Bool)
    (prefixLength chargedLength : Nat) :
    visitedSpace memoryMachine chargedLength ((memoryTrace memory archive bit right).take prefixLength) ≤
      chargedLength+11 := by
  have hs := PSTRTMTrace002.visitedSpace_le memoryMachine chargedLength
    ((memoryTrace memory archive bit right).take prefixLength)
  have hp : ((memoryTrace memory archive bit right).take prefixLength).length ≤ 5 := by
    have ht := memoryTrace_length memory archive bit right
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignRead021
