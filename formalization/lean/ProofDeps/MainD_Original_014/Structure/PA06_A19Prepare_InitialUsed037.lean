module

public import Structure.PA06_A19Prepare_FinalHeader033_InitialUsedROM
public import Structure.PA06_A19Prepare_BankPacked021_Prefix
public import Structure.PSTR_BuildLower_WordLoop_015
public import Structure.PA06_A19Prepare_RuntimeLayout026_Bounds
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate actual initial-used loop. Root has reserved the small
slots16/17/18 for this loop without cross-owner collision. Source is fixed:
setup33 really creates pointer/ROM cursor/count; body88 really reads ROM,
executes72 writer ops and updates two bank words; the existing real Word
loop head5/tail9 decrements the stored remaining count. No pc reset occurs.
The complete Word invariant and fetched-prefix proof remain separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower

def pointerSlot : Nat := 16
def cursorSlot : Nat := 17
def counterSlot : Nat := 18

def storeTotal (slot : Nat) : List PackingOp :=
  [.base (.base (.constant .index slot)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .total))]

def tableSetup : List PackingOp :=
  relativeRead 4 .value ++ relativeRead 1 .total ++
    [.base (.subtract .value .value .total)] ++ relativeRead 2 .total ++
    [.base (.base (.constant .fresh 1)), .base (.base (.add .total .total .fresh)),
     .base (.base (.constant .fresh 8192)), .arithmetic .multiply .total .fresh .total,
     .base (.subtract .value .value .total)] ++ relativeWrite pointerSlot

def cursorSetup : List PackingOp :=
  relativeRead 0 .total ++ relativeRead 1 .value ++
    [.arithmetic .multiply .total .total .value,
     .base (.base (.constant .fresh 2)), .base (.base (.add .total .total .fresh))] ++
    storeTotal cursorSlot ++ relativeWrite counterSlot

def setup : List PackingOp := tableSetup ++ cursorSetup

def readUsed : List PackingOp := relativeRead cursorSlot .index ++
  [.base (.base (.loadROM .input .value .index))]

def advance (slot : Nat) : List PackingOp := relativeRead slot .value ++
  [.base (.base (.constant .fresh 1)), .base (.base (.add .value .value .fresh)),
   .base (.base (.storeHeap .index .value))]

def body : List PackingOp := readUsed ++ PA06A19PrepareBankPacked021.safeWrite pointerSlot ++
  advance pointerSlot ++ advance cursorSlot

def programAt (start : Nat) : List PackingOp := setup ++ relativeLoopBlock counterSlot (start + 33) body

theorem tableSetup_length : tableSetup.length = 18 := rfl
theorem cursorSetup_length : cursorSetup.length = 15 := rfl
theorem setup_length : setup.length = 33 := rfl
theorem readUsed_length : readUsed.length = 4 := rfl
theorem advance_length (slot : Nat) : (advance slot).length = 6 := rfl
theorem body_length : body.length = 88 := rfl
theorem programAt_length (start : Nat) : (programAt start).length = 135 := rfl

theorem setup_noJump : ∀ op ∈ setup, NoJump op := by
  simp [setup, tableSetup, cursorSetup, storeTotal, pointerSlot, cursorSlot, counterSlot,
    relativeRead, relativeWrite, NoJump]

theorem body_straight : StraightProgram body := by
  simp [body, readUsed, advance, relativeRead, PA06A19PrepareBankPacked021.safeWrite,
    PA06A19PrepareBankPacked021.loadPointer, PA06A19PrepareBankPacked021.clear,
    PA06A19PrepareBankPacked021.directWrite, PA06A19PrepareRuntimePacked016.clear,
    PA06A19PrepareRuntimePacked016.directWrite, StraightProgram, StraightOp]

def tableBaseExpr (C q t : Nat) : Nat := C - q - 8192 * (t + 1)

theorem tableBaseExpr_actual (N q t : Nat) (hq : 0 < q) :
    tableBaseExpr (capacityWords 8192 N q t) q t = tableWords N q t := by
  unfold tableBaseExpr capacityWords
  rw [ite_eq_right (Nat.ne_of_gt hq)]
  omega

/- The existing five arithmetic operations are projected with a symbolic
factor before substituting8192. This avoids reducing a long concrete state
through multiplication when proving the heap of the complete setup. -/
private def tableAdjust (factor : Nat) : List PackingOp :=
  [.base (.base (.constant .fresh 1)), .base (.base (.add .total .total .fresh)),
   .base (.base (.constant .fresh factor)), .arithmetic .multiply .total .fresh .total,
   .base (.subtract .value .value .total)]

private theorem tableAdjust_heap (rom : PhysicalROM) (factor : Nat) (state : NatState) :
    (runOps rom (tableAdjust factor) state).heap = state.heap := rfl

private theorem tableAdjust_address (rom : PhysicalROM) (factor : Nat) (state : NatState) :
    (runOps rom (tableAdjust factor) state).register .address = state.register .address := rfl

private theorem tableAdjust_value (rom : PhysicalROM) (factor : Nat) (state : NatState) :
    (runOps rom (tableAdjust factor) state).register .value =
      state.register .value - factor * (state.register .total + 1) := by
  simp +decide only [tableAdjust, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, Function.update_apply, ↓reduceIte]

private def tableInputs : List PackingOp :=
  relativeRead 4 .value ++ relativeRead 1 .total ++
    [.base (.subtract .value .value .total)] ++ relativeRead 2 .total

private theorem tableInputs_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom tableInputs state).heap = state.heap := rfl

private theorem tableInputs_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom tableInputs state).register .address = state.register .address := rfl

private theorem tableInputs_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom tableInputs state).register .value =
      state.heap (state.register .address + 4) - state.heap (state.register .address + 1) := by
  simp only [tableInputs, runOps_append]
  simp +decide only [relativeRead, runOps, natExecuteOp,
    Op.execute, Instruction.execute, Function.update_apply, ↓reduceIte]

private theorem tableInputs_total (rom : PhysicalROM) (state : NatState) :
    (runOps rom tableInputs state).register .total = state.heap (state.register .address + 2) := by
  simp only [tableInputs, runOps_append]
  simp +decide only [relativeRead, runOps, natExecuteOp,
    Op.execute, Instruction.execute, Function.update_apply, ↓reduceIte]

private theorem tableFactor_heap (rom : PhysicalROM) (factor : Nat) (state : NatState) :
    (runOps rom (tableInputs ++ tableAdjust factor ++ relativeWrite pointerSlot) state).heap =
      Function.update state.heap (state.register .address + pointerSlot)
        (state.heap (state.register .address + 4) - state.heap (state.register .address + 1) -
          factor * (state.heap (state.register .address + 2) + 1)) := by
  simp only [runOps_append, relativeWrite_nat_heap, tableAdjust_heap, tableAdjust_address,
    tableAdjust_value, tableInputs_heap, tableInputs_address, tableInputs_value, tableInputs_total]

theorem tableSetup_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom tableSetup state).heap = Function.update state.heap (state.register .address + pointerSlot)
      (tableBaseExpr (state.heap (state.register .address + 4)) (state.heap (state.register .address + 1))
        (state.heap (state.register .address + 2))) := by
  have code : tableSetup = tableInputs ++ tableAdjust 8192 ++ relativeWrite pointerSlot := rfl
  rw [code]
  exact tableFactor_heap rom 8192 state

theorem tableSetup_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom tableSetup state).register .address = state.register .address := rfl

theorem cursorSetup_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom cursorSetup state).heap = Function.update
      (Function.update state.heap (state.register .address + cursorSlot)
        (state.heap (state.register .address + 0) * state.heap (state.register .address + 1) + 2))
      (state.register .address + counterSlot) (state.heap (state.register .address + 1)) := by
  simp only [cursorSetup, runOps_append]
  simp +decide only [relativeRead, relativeWrite, storeTotal, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, Function.update_apply, ↓reduceIte]

theorem cursorSetup_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom cursorSetup state).register .address = state.register .address := rfl

/-- The three stored controls are actual outputs of setup, including count.
No source pointer, ROM cursor or loop length is taken from a register premise. -/
theorem setup_heap (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : NatState) (CB : Nat) (hcb : state.register .address = CB)
    (hN : state.heap (CB + 0) = full.length) (hQ : state.heap (CB + 1) = q)
    (ht : state.heap (CB + 2) = treeSize q full)
    (hC : state.heap (CB + 4) = capacityWords 8192 full.length q (treeSize q full)) :
    (runOps (controllerInput q full used) setup state).heap = Function.update
      (Function.update (Function.update state.heap (CB + pointerSlot) (tableWords full.length q (treeSize q full)))
        (CB + cursorSlot) (2 + full.length * q)) (CB + counterSlot) q := by
  have hne0 : CB + 0 ≠ CB + pointerSlot := by dsimp only [pointerSlot]; omega
  have hne1 : CB + 1 ≠ CB + pointerSlot := by dsimp only [pointerSlot]; omega
  simp only [setup, runOps_append, cursorSetup_heap, tableSetup_heap, tableSetup_address, hcb]
  simp only [Function.update_of_ne hne0, Function.update_of_ne hne1, hN, hQ, ht, hC, tableBaseExpr_actual _ _ _ hq]
  rw [Nat.add_comm (full.length * q) 2]

theorem setup_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom setup state).register .address = state.register .address := by
  simp only [setup, runOps_append, cursorSetup_address, tableSetup_address]

theorem setup_controls (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : NatState) (CB : Nat) (hcb : state.register .address = CB)
    (hN : state.heap (CB + 0) = full.length) (hQ : state.heap (CB + 1) = q)
    (ht : state.heap (CB + 2) = treeSize q full)
    (hC : state.heap (CB + 4) = capacityWords 8192 full.length q (treeSize q full)) :
    let after := runOps (controllerInput q full used) setup state
    after.heap (CB + pointerSlot) = tableWords full.length q (treeSize q full) ∧
      after.heap (CB + cursorSlot) = 2 + full.length * q ∧ after.heap (CB + counterSlot) = q := by
  simp only [setup_heap q full used hq state CB hcb hN hQ ht hC]
  simp (disch := omega) [pointerSlot, cursorSlot, counterSlot]

/-- The existing real Word loop charges five head ops and nine tail ops.
This arithmetic identity does not assume or prove BodyExits. -/
theorem loopSteps_eq {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp)
    (count : Nat) (state : WordState bits) :
    PSTRBuildLower.WordLoop.loopSteps rom left body right counterSlot (fun _ => 88) count state = 102 * count + 5 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    simp only [PSTRBuildLower.WordLoop.loopSteps, PSTRBuildLower.WordLoop.cycleSteps, ih]
    omega

def clock (q : Nat) : Nat := 102 * q + 38

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
