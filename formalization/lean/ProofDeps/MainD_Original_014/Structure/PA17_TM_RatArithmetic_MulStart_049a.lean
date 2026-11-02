module
public import Structure.PA17_TM_RatArithmetic_Outer_025g
public import Structure.PA17_TM_RatArithmetic_SignRead_021b

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticSignRead021

/-- Real header-to-Nx walk followed by the frozen physical sx sensor. -/
def headerReadMachine : Machine 14 := PSTRTMSeq005.seqMachine forwardNxMachine sensorMachine
def headerReadPort (bit : Bool) : Fin 15 := PSTRTMSeq005.rightLabel (a:=7) (readPort bit)

theorem headerReadPort_value (bit : Bool) : (headerReadPort bit).val=if bit then 14 else 13 := by
  cases bit <;> rfl

theorem headerRead_bounded (sx : Bool) (counter bank : List Bool) :
    BoundedRun headerReadMachine (Tape.mk₂ counter (prefixRight sx bank))
      (headerReadPort sx) (Tape.mk₂ (prefixLeft sx counter) bank) 13 := by
  have hf : BoundedRun forwardNxMachine (Tape.mk₂ counter (prefixRight sx bank))
      (7 : Fin 8) (Tape.mk₂ (prefixLeft sx counter) bank) 8 :=
    ⟨forwardNxTrace sx counter bank,forwardNx_runsFrom sx counter bank,by rfl⟩
  have hs : BoundedRun sensorMachine (Tape.mk₂ (prefixLeft sx counter) bank)
      (readPort sx) (Tape.mk₂ (prefixLeft sx counter) bank) 5 :=
    ⟨sensorTrace ([true,false,false,true,true]++counter) sx bank,
      sensor_runsFrom ([true,false,false,true,true]++counter) sx bank,by rfl⟩
  exact hf.seq hs

def readFamily (_memory : Fin 32) : Machine 14 := headerReadMachine
def readPorts (_memory : Fin 32) (_q : Fin 15) : Option (Fin 32 × Fin 15) := none
def readMemoryMachine : Machine 479 := blockMachine readFamily readPorts
def readMemoryInitial (memory : Fin 32) (tape : Tape Bool) : MachineState 479 :=
  blockCfg memory (⟨0,tape⟩ : MachineState 14)
def readMemoryFinal (memory : Fin 32) (sx : Bool) (tape : Tape Bool) : MachineState 479 :=
  blockCfg memory (⟨headerReadPort sx,tape⟩ : MachineState 14)
def readMemoryHalt (memory : Fin 32) (sx : Bool) : Fin 480 := label memory (headerReadPort sx)

theorem read_memory_bounded (memory : Fin 32) (sx : Bool) (counter bank : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom readMemoryMachine
      (readMemoryInitial memory (Tape.mk₂ counter (prefixRight sx bank))) trace
      (readMemoryFinal memory sx (Tape.mk₂ (prefixLeft sx counter) bank)) ∧ trace.length≤13 := by
  obtain ⟨trace,hr,hl⟩ := headerRead_bounded sx counter bank
  have hs := block_runsFrom readFamily readPorts memory _ _ _ hr rfl
  exact ⟨trace.map (blockCfg (s:=14) memory),hs,by simpa only [List.length_map] using hl⟩

/-- The actual local sensor exit selects the high bit of the next row. -/
def decodeReadMemory (q : Fin 480) : Fin 64 :=
  selectedMemory (phaseOf (p:=31) (s:=14) q) ((localOf (p:=31) (s:=14) q).val=14)

theorem decodeReadMemory_actual (memory : Fin 32) (sx : Bool) :
    decodeReadMemory (readMemoryHalt memory sx)=selectedMemory memory sx := by
  simp only [decodeReadMemory,readMemoryHalt,phaseOf_label,localOf_label]
  cases sx <;> rfl

def homeFamily (_memory : Fin 64) : Machine 7 := sevenMachine .left
def homePorts (_memory : Fin 64) (_q : Fin 8) : Option (Fin 64 × Fin 8) := none
def homeMemoryMachine : Machine 511 := blockMachine homeFamily homePorts
def homeMemoryInitial (memory : Fin 64) (tape : Tape Bool) : MachineState 511 :=
  blockCfg memory (⟨0,tape⟩ : MachineState 7)
def homeMemoryFinal (memory : Fin 64) (tape : Tape Bool) : MachineState 511 :=
  blockCfg memory (⟨7,tape⟩ : MachineState 7)

theorem home_memory_bounded (memory : Fin 64) (sx : Bool) (counter bank : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom homeMemoryMachine
      (homeMemoryInitial memory (Tape.mk₂ (prefixLeft sx counter) bank)) trace
      (homeMemoryFinal memory (Tape.mk₂ counter (prefixRight sx bank))) ∧ trace.length≤8 := by
  have hr := block_runsFrom homeFamily homePorts memory _ _ _ (leftSeven_runsFrom sx counter bank) rfl
  exact ⟨(leftSevenTrace sx counter bank).map (blockCfg (s:=7) memory),hr,by rfl⟩

theorem readMemoryInitial_label (memory : Fin 32) (tape : Tape Bool) :
    (readMemoryInitial memory tape).q.val=15*memory.val := by
  simp [readMemoryInitial,blockCfg,label,Nat.mul_comm]

theorem homeMemoryInitial_label (memory : Fin 64) (tape : Tape Bool) :
    (homeMemoryInitial memory tape).q.val=8*memory.val := by
  simp [homeMemoryInitial,blockCfg,label,Nat.mul_comm]

theorem homeMemoryFinal_label (memory : Fin 64) (tape : Tape Bool) :
    (homeMemoryFinal memory tape).q.val=8*memory.val+7 := by
  simp [homeMemoryFinal,blockCfg,label,Nat.mul_comm]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049
