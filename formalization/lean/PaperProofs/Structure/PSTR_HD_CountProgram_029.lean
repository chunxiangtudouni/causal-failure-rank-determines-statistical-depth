module

public import PaperProofs.Structure.PSTR_HD_CountBounds_028

/-! One FIXED actual node-count kernel. All child traversal is a real branch
loop. No input/ROM bitmap, sum, cardinality or iteration macro is an opcode.
Origin is a compile-time code location, independent of every task/input. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PSTRCountWorkspace

def saveField (slot : Nat) : List PackingOp :=
  [.base (.base (.constant .total slot)), .base (.base (.add .address .address .total)),
   .base (.base (.storeHeap .address .value))]

def clearLoop : List PackingOp :=
  [.base (.base (.constant .total 1)), .base (.base (.add .address .address .total)),
   .base (.base (.constant .value 0)), .base (.base (.storeHeap .address .value)),
   .base (.base (.add .address .address .total)), .base (.base (.storeHeap .address .value))]

def setup : List PackingOp :=
  bootstrap ++ PSTRStaticFields.program ⟨2, by decide⟩ ++ PSTRCountWorkspace.program ++ saveField 4 ++
    PSTRStaticFields.program ⟨5, by decide⟩ ++ PSTRCountWorkspace.program ++ saveField 5 ++ clearLoop

def testLead (origin : Nat) : List PackingOp := PSTRCountWorkspace.program ++
  [.base (.base (.constant .total 4)), .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .value .address)), .base (.base (.constant .total 2)),
   .base (.base (.add .address .address .total)), .base (.base (.loadHeap .old .address)),
   .base (.subtract .flag .value .old), .base (.base (.constant .total (5 * (origin + 235))))]

def childPosition : List PackingOp :=
  [.base (.base (.constant .total 1)), .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .fresh .address)), .base (.base (.constant .total 5)),
   .base (.base (.add .address .address .total)), .base (.base (.loadHeap .old .address)),
   .base (.base (.add .index .fresh .old))]

def accumulate (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .total 0)), .base (.base (.add .index .address .total)),
   .base (.base (.loadHeap .old .address)), .base (.base (.add .address .old .value)),
   .base (.base (.loadHeap .fresh .address)), .base (.base (.constant .total 7)),
   .base (.base (.add .address .index .total)), .base (.base (.loadHeap .value .address)),
   .base (.base (.add .value .value .fresh)), .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .total 6)), .base (.base (.add .address .index .total)),
   .base (.base (.loadHeap .old .address)), .base (.base (.constant .fresh 1)),
   .base (.base (.add .old .old .fresh)), .base (.base (.storeHeap .address .old)),
   .base (.base (.constant .flag 0)), .base (.base (.constant .total (5 * (origin + 121))))]

def bodyLead (origin : Nat) : List PackingOp :=
  PSTRCountWorkspace.program ++ childPosition ++ PSTRStaticFields.program ⟨3, by decide⟩ ++
    PSTRCountWorkspace.program ++ accumulate origin

def finishStores : List PackingOp :=
  [.base (.base (.loadHeap .old .address)), .base (.base (.constant .total 2)),
   .base (.base (.add .address .address .total)), .base (.base (.loadHeap .index .address)),
   .base (.base (.constant .total 1)), .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .value .address)), .base (.base (.constant .total 2)),
   .base (.base (.add .address .address .total)), .base (.base (.loadHeap .flag .address)),
   .base (.base (.constant .total 2)), .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .fresh .address)), .base (.base (.select .value .flag .fresh .value)),
   .base (.base (.add .address .old .index)), .base (.base (.storeHeap .address .value))]

def footer : List PackingOp := PSTRCountWorkspace.program ++ finishStores

def programAt (origin : Nat) : List PackingOp := setup ++ testLead origin ++ [.jumpIfZero .flag .total] ++
  bodyLead origin ++ [.jumpIfZero .flag .total] ++ footer

theorem setup_length : setup.length = 121 := rfl
theorem testLead_length (origin : Nat) : (testLead origin).length = 27 := rfl
theorem bodyLead_length (origin : Nat) : (bodyLead origin).length = 85 := rfl
theorem footer_length : footer.length = 35 := rfl
theorem programAt_length (origin : Nat) : (programAt origin).length = 270 := rfl
theorem programAt_code_length (origin : Nat) : (packingCode (programAt origin)).length = 1355 := by
  rw [packingCode_length, programAt_length]

theorem setup_straight : StraightProgram setup := by
  simp [setup, bootstrap, PSTRCountWorkspace.program, PSTRCountWorkspace.spillProgram,
    PSTRStaticFields.program, saveField, clearLoop, StraightProgram, StraightOp]

theorem testLead_straight (origin : Nat) : StraightProgram (testLead origin) := by
  simp [testLead, PSTRCountWorkspace.program, StraightProgram, StraightOp]

theorem bodyLead_straight (origin : Nat) : StraightProgram (bodyLead origin) := by
  simp [bodyLead, PSTRCountWorkspace.program, childPosition, PSTRStaticFields.program,
    accumulate, StraightProgram, StraightOp]

theorem footer_straight : StraightProgram footer := by
  simp [footer, PSTRCountWorkspace.program, finishStores, StraightProgram, StraightOp]

def activeSteps (degree : Nat) : Nat := 184 + 114 * degree

theorem activeSteps_decompose (degree : Nat) :
    activeSteps degree = setup.length + ((testLead 0).length + 1 + (bodyLead 0).length + 1) * degree +
      ((testLead 0).length + 1) + footer.length := by
  rw [setup_length, testLead_length, bodyLead_length, footer_length]
  unfold activeSteps
  omega

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
