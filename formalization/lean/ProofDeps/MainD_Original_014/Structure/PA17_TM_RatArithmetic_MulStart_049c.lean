module
public import Structure.PA17_TM_RatArithmetic_MulStart_049b

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticOuter025 PA17TMRatArithmeticSignRead021
attribute [local implicit_reducible] allocatorCap stageCap mulStartCap

/-- This transition really writes the current symbol to itself before
entering the already-observed old-memory read row. -/
theorem allocator_to_read (k : Nat) (memory : Fin 32) (sx : Bool) (bank : List Bool)
    (halt : TM0.step (allocatorMachine k)
      (rawLoopSavedFinal (PA17TMRatArithmeticAllocatePass023.passMachine k) memory sx bank)=none) :
    TM0.step (mulStartMachine k) (allocated k memory sx bank)=
      some (readInitial k memory sx [false] bank) := by
  let last := padCfg (allocator_le_stage k)
    (rawLoopSavedFinal (PA17TMRatArithmeticAllocatePass023.passMachine k) memory sx bank)
  have hf : TM0.step (startFamily k (0 : Fin 3)) last=none := by
    change TM0.step (padMachine (allocator_le_stage k) (allocatorMachine k)) last=none
    simp only [last,pad_step,halt,Option.map_none]
  have port : startPorts k (0 : Fin 3) last.q=
      some (1,padLabel (read_le_stage k) (label memory (0 : Fin 15))) := by
    simp only [startPorts,Fin.val_zero,ite_true,last,padCfg,decodeAllocatorMemory_actual]
  have ht := block_transfer (startFamily k) (startPorts k) (0 : Fin 3) last
    (1,padLabel (read_le_stage k) (label memory (0 : Fin 15))) hf port
  have target : blockCfg (1 : Fin 3)
      (⟨padLabel (read_le_stage k) (label memory (0 : Fin 15)),last.Tape⟩ : MachineState (stageCap k))=
      readInitial k memory sx [false] bank := rfl
  rw [target] at ht
  exact ht

theorem read_to_home (k : Nat) (memory : Fin 32) (sx : Bool) (counter bank : List Bool)
    (halt : TM0.step readMemoryMachine
      (readMemoryFinal memory sx (Tape.mk₂ (prefixLeft sx counter) bank))=none) :
    TM0.step (mulStartMachine k) (readFinal k memory sx counter bank)=
      some (homeInitial k (selectedMemory memory sx) sx counter bank) := by
  let last := padCfg (read_le_stage k)
    (readMemoryFinal memory sx (Tape.mk₂ (prefixLeft sx counter) bank))
  have hf : TM0.step (startFamily k (1 : Fin 3)) last=none := by
    change TM0.step (padMachine (read_le_stage k) readMemoryMachine) last=none
    simp only [last,pad_step,halt,Option.map_none]
  have hd : decodeReadMemory (readCode k last.q)=selectedMemory memory sx := by
    rw [show last.q=padLabel (read_le_stage k) (readMemoryHalt memory sx) from rfl,readCode_pad]
    exact decodeReadMemory_actual memory sx
  have port : startPorts k (1 : Fin 3) last.q=
      some (2,padLabel (home_le_stage k) (label (selectedMemory memory sx) (0 : Fin 8))) := by
    simp only [startPorts,show (1 : Fin 3).val=1 from rfl,Nat.one_ne_zero,ite_false,ite_true,hd]
  have ht := block_transfer (startFamily k) (startPorts k) (1 : Fin 3) last
    (2,padLabel (home_le_stage k) (label (selectedMemory memory sx) (0 : Fin 8))) hf port
  have target : blockCfg (2 : Fin 3)
      (⟨padLabel (home_le_stage k) (label (selectedMemory memory sx) (0 : Fin 8)),last.Tape⟩ : MachineState (stageCap k))=
      homeInitial k (selectedMemory memory sx) sx counter bank := rfl
  rw [target] at ht
  exact ht

theorem read_segment (k : Nat) (memory : Fin 32) (sx : Bool) (counter bank : List Bool) :
    ∃ trace, Segment (mulStartMachine k) (readInitial k memory sx counter bank) trace
      (readFinal k memory sx counter bank) ∧
      TM0.step (mulStartMachine k) (readFinal k memory sx counter bank)=
        some (homeInitial k (selectedMemory memory sx) sx counter bank) ∧ trace.length≤13 := by
  obtain ⟨trace,hr,hl⟩ := read_memory_bounded memory sx counter bank
  have hp := pad_runsFrom (read_le_stage k) readMemoryMachine _ _ _ hr
  have hf : PSTRTMSeq005.RunsFrom (startFamily k (1 : Fin 3))
      (padCfg (read_le_stage k) (readMemoryInitial memory (Tape.mk₂ counter (prefixRight sx bank))))
      (trace.map (padCfg (read_le_stage k)))
      (padCfg (read_le_stage k) (readMemoryFinal memory sx (Tape.mk₂ (prefixLeft sx counter) bank))) := by
    simpa only [startFamily,Fin.val_one,show ¬(1 : Nat)=0 from by decide,ite_false,ite_true] using hp
  have hs := block_segment (startFamily k) (startPorts k) (1 : Fin 3) _ _ _ hf
  refine ⟨(trace.map (padCfg (read_le_stage k))).map (blockCfg (s:=stageCap k) (1 : Fin 3)),
    hs,read_to_home k memory sx counter bank hr.2.2.2,?_⟩
  simpa only [List.length_map] using hl

theorem home_runsFrom (k : Nat) (memory : Fin 64) (sx : Bool) (counter bank : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (mulStartMachine k) (homeInitial k memory sx counter bank) trace
      (homeFinal k memory sx counter bank) ∧ trace.length≤8 := by
  obtain ⟨trace,hr,hl⟩ := home_memory_bounded memory sx counter bank
  have hp := pad_runsFrom (home_le_stage k) homeMemoryMachine _ _ _ hr
  have hf : PSTRTMSeq005.RunsFrom (startFamily k (2 : Fin 3))
      (padCfg (home_le_stage k) (homeMemoryInitial memory (Tape.mk₂ (prefixLeft sx counter) bank)))
      (trace.map (padCfg (home_le_stage k)))
      (padCfg (home_le_stage k) (homeMemoryFinal memory (Tape.mk₂ counter (prefixRight sx bank)))) := by
    simpa only [startFamily,show (2 : Fin 3).val=2 from rfl,show ¬(2 : Nat)=0 from by decide,
      show ¬(2 : Nat)=1 from by decide,ite_false] using hp
  have hs := block_runsFrom (startFamily k) (startPorts k) (2 : Fin 3) _ _ _ hf
    (by simp only [startPorts,show (2 : Fin 3).val=2 from rfl,show ¬(2 : Nat)=0 from by decide,
      show ¬(2 : Nat)=1 from by decide,ite_false])
  refine ⟨(trace.map (padCfg (home_le_stage k))).map (blockCfg (s:=stageCap k) (2 : Fin 3)),hs,?_⟩
  simpa only [List.length_map] using hl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049
