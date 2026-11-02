module
public import Structure.PA17_TM_RatArithmetic_BankCopy_024g
public import Structure.PA17_TM_RatArithmetic_Allocate_013e
public import Structure.PA17_TM_RatArithmetic_Bookmark_014g

/-! Restore only the copied first DATA bit. The source remains clamped.
Incoming memory is carried by the ACTUAL control label. The complete finite
row dispatcher is fixed before every tape/input, including all 32/64 rows. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRestore029
open PA17TMDivisionCompose006

def sourceLeft (archive tail : List Bool) : List Bool :=
  PA17TMRatArithmeticCopy006.sourceLeft archive (false::tail)

def outputLeft (archive tail : List Bool) (gap : Nat) : List Bool :=
  PA17TMRatArithmeticBankCopy024.destinationLeft gap (sourceLeft archive tail)

def copyFirst (archive tail : List Bool) (gap : Nat) : MachineState 58 :=
  PA17TMRatArithmeticBankCopy024.state 0 (sourceLeft archive tail)
    (true::(List.replicate gap false ++ [true,false]))

def copyLast (archive tail : List Bool) (gap : Nat) : MachineState 58 :=
  PA17TMRatArithmeticBankCopy024.state 58 (outputLeft archive tail gap)
    (PSTRTMIncrement009.blocks (false::tail) ++ [false,false])

/-- Local row, used only inside the fixed finite dispatcher below. -/
def rowMachine (which memory : Nat) : Machine 60 :=
  PSTRTMSeq005.seqMachine PA17TMRatArithmeticBankCopy024.copyMachine
    (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit which))

def rowFirst (archive tail : List Bool) (gap : Nat) : MachineState 60 :=
  PSTRTMSeq005.leftCfg (b:=1) (copyFirst archive tail gap)

def rowLast (which memory : Nat) (archive tail : List Bool) (gap : Nat) : MachineState 60 :=
  PSTRTMSeq005.rightCfg (a:=58)
    (PA17TMRatArithmeticAllocate013.seekState 1 (outputLeft archive tail gap)
      (memory.testBit which::true::(PSTRTMIncrement009.blocks tail ++ [false,false])))

def rowTrace (which memory : Nat) (archive tail : List Bool) (gap : Nat) : List (MachineState 60) :=
  (PA17TMRatArithmeticBankCopy024.copyTrace archive (false::tail) gap).map (PSTRTMSeq005.leftCfg (b:=1)) ++
  (PA17TMRatArithmeticAllocate013.setMarkerTrace false (memory.testBit which)
    (outputLeft archive tail gap) (true::(PSTRTMIncrement009.blocks tail ++ [false,false]))).map
    (PSTRTMSeq005.rightCfg (a:=58))

theorem row_runsFrom (which memory : Nat) (archive tail : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom (rowMachine which memory) (rowFirst archive tail gap)
      (rowTrace which memory archive tail gap) (rowLast which memory archive tail gap) := by
  have hc : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticBankCopy024.copyMachine
      (copyFirst archive tail gap) (PA17TMRatArithmeticBankCopy024.copyTrace archive (false::tail) gap)
      (copyLast archive tail gap) :=
    PA17TMRatArithmeticBankCopy024.copy_runsFrom archive (false::tail) gap
  have hs : PSTRTMSeq005.RunsFrom
      (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit which))
      ⟨0,(copyLast archive tail gap).Tape⟩
      (PA17TMRatArithmeticAllocate013.setMarkerTrace false (memory.testBit which)
        (outputLeft archive tail gap) (true::(PSTRTMIncrement009.blocks tail ++ [false,false])))
      (PA17TMRatArithmeticAllocate013.seekState 1 (outputLeft archive tail gap)
        (memory.testBit which::true::(PSTRTMIncrement009.blocks tail ++ [false,false]))) :=
    PA17TMRatArithmeticAllocate013.setMarker_runsFrom false (memory.testBit which)
      (outputLeft archive tail gap) (true::(PSTRTMIncrement009.blocks tail ++ [false,false]))
  exact PSTRTMSeq005.seq_runsFrom PA17TMRatArithmeticBankCopy024.copyMachine
    (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit which))
    (copyFirst archive tail gap) (copyLast archive tail gap)
    (PA17TMRatArithmeticAllocate013.seekState 1 (outputLeft archive tail gap)
      (memory.testBit which::true::(PSTRTMIncrement009.blocks tail ++ [false,false])))
    (PA17TMRatArithmeticBankCopy024.copyTrace archive (false::tail) gap)
    (PA17TMRatArithmeticAllocate013.setMarkerTrace false (memory.testBit which)
      (outputLeft archive tail gap) (true::(PSTRTMIncrement009.blocks tail ++ [false,false]))) hc hs

theorem rowTrace_length (which memory : Nat) (archive tail : List Bool) (gap : Nat) :
    (rowTrace which memory archive tail gap).length =
      (PA17TMRatArithmeticBankCopy024.copyTrace archive (false::tail) gap).length+2 := by
  simp only [rowTrace,List.length_append,List.length_map,PA17TMRatArithmeticAllocate013.setMarkerTrace,
    List.length_cons,List.length_nil]

def familyRows (p which : Nat) : Fin (p+1) → Machine 60 := fun memory => rowMachine which memory.val

def familyPorts (p : Nat) : Fin (p+1) → Fin 61 → Option (Fin (p+1) × Fin 61) := fun _ _ => none

/-- Code depends only on fixed row count/field slot. Runtime row selection
is phaseOf the actual label; no input value is used to construct a machine. -/
def machine (p which : Nat) : Machine (totalStates p 60) :=
  blockMachine (familyRows p which) (familyPorts p)

def initial (p : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    MachineState (totalStates p 60) := blockCfg memory (rowFirst archive tail gap)

def final (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    MachineState (totalStates p 60) := blockCfg memory (rowLast which memory.val archive tail gap)

def trace (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    List (MachineState (totalStates p 60)) :=
  (rowTrace which memory.val archive tail gap).map (blockCfg memory)

theorem runsFrom (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom (machine p which) (initial p memory archive tail gap)
      (trace p which memory archive tail gap) (final p which memory archive tail gap) := by
  have hr := row_runsFrom which memory.val archive tail gap
  have h := block_segment (familyRows p which) (familyPorts p) memory
    (rowFirst archive tail gap) (rowLast which memory.val archive tail gap)
    (rowTrace which memory.val archive tail gap) hr
  refine ⟨h.1,h.2.1,h.2.2,?_⟩
  exact block_halt (familyRows p which) (familyPorts p) memory
    (rowLast which memory.val archive tail gap) hr.2.2.2 rfl

theorem initial_label (p : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    (initial p memory archive tail gap).q.val = memory.val*61 := rfl

theorem final_label (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    (final p which memory archive tail gap).q.val = memory.val*61+60 := rfl

theorem initial_memory (p : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    phaseOf (p:=p) (s:=60) (initial p memory archive tail gap).q = memory :=
  phaseOf_label memory (rowFirst archive tail gap).q

theorem final_memory (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    phaseOf (p:=p) (s:=60) (final p which memory archive tail gap).q = memory :=
  phaseOf_label memory (rowLast which memory.val archive tail gap).q

theorem initial_tape (p : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    (initial p memory archive tail gap).Tape = Turing.Tape.mk₂ (sourceLeft archive tail)
      (true::(List.replicate gap false ++ [true,false])) := rfl

theorem final_tape (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    (final p which memory archive tail gap).Tape = Turing.Tape.mk₂ (outputLeft archive tail gap)
      (PSTRTMIncrement009.blocks (memory.val.testBit which::tail) ++ [false,false]) := rfl

def machine32 (which : Nat) : Machine 1951 := machine 31 which
def machine64 (which : Nat) : Machine 3903 := machine 63 which

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRestore029
