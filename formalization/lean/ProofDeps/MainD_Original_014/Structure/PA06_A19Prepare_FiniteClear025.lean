module

public import PaperProofs.Structure.PA17_UniformGenerator_035g
public import PaperProofs.Structure.PackingExecutionCost
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled private finite zeroing kernel. The actual runtime index and
count are supplied by prior real setup; no address/dimension is an immediate.
Only the finite selected interval is cleared. Hardware.address is preserved,
so headers, high control/cache banks and unrelated infinite heap cells frame.
Word prefix safety and the concrete prepare initialization remain separate.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
open PA17UniformGenerator035a PA17UniformGenerator035g

def initializeControls : List PackingOp :=
  [.base (.base (.constant .value 0)), .base (.base (.constant .fresh 1)),
   .base (.base (.constant .flag 0))]

def tail (entry : Nat) : List PackingOp :=
  [.base (.base (.storeHeap .index .value)), .base (.base (.add .index .index .fresh)),
   .base (.subtract .total .total .fresh), .base (.base (.constant .old entry)),
   .jumpIfZero .flag .old]

def programAt (start : Nat) : List PackingOp :=
  initializeControls ++ copyHead (5 * (start + 10)) ++ tail (5 * (start + 3))

theorem initialize_length : initializeControls.length = 3 := rfl
theorem tail_length (entry : Nat) : (tail entry).length = 5 := rfl
theorem programAt_length (start : Nat) : (programAt start).length = 10 := rfl

def cleared (original : Nat → Nat) (base moved : Nat) : Nat → Nat :=
  fun address => if base ≤ address ∧ address < base + moved then 0 else original address

theorem cleared_zero (original : Nat → Nat) (base moved index : Nat) (hi : index < moved) :
    cleared original base moved (base + index) = 0 := by
  simp only [cleared, ite_eq_left (by omega : base ≤ base + index ∧ base + index < base + moved)]

theorem cleared_frame (original : Nat → Nat) (base moved address : Nat)
    (ha : address < base ∨ base + moved ≤ address) :
    cleared original base moved address = original address := by
  simp only [cleared, ite_eq_right (by omega : ¬ (base ≤ address ∧ address < base + moved))]

theorem cleared_update (original : Nat → Nat) (base moved : Nat) :
    Function.update (cleared original base moved) (base + moved) 0 =
      cleared original base (moved + 1) := by
  funext address
  by_cases he : address = base + moved
  · subst address
    rw [Function.update_self]
    exact (cleared_zero original base (moved + 1) moved (by omega)).symm
  · rw [Function.update_of_ne he]
    simp only [cleared]
    by_cases hin : base ≤ address ∧ address < base + moved
    · rw [ite_eq_left hin, ite_eq_left (by omega : base ≤ address ∧ address < base + (moved + 1))]
    · rw [ite_eq_right hin, ite_eq_right (by omega : ¬ (base ≤ address ∧ address < base + (moved + 1)))]

def ClearInv (base : Nat) (original : Nat → Nat) (moved remaining address : Nat)
    (state : NatState) : Prop :=
  state.register .index = base + moved ∧ state.register .total = remaining ∧
    state.register .value = 0 ∧ state.register .fresh = 1 ∧ state.register .flag = 0 ∧
    state.register .address = address ∧ state.heap = cleared original base moved

theorem init_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ programAt left.length ++ right) 3 state = runOps rom initializeControls state := by
  have hh := natRun_of_straight_segment rom
    (left ++ initializeControls ++ (copyHead (5 * (left.length + 10)) ++ tail (5 * (left.length + 3)) ++ right))
    initializeControls left.length (by simp only [List.length_append]; omega)
    (segment_index left initializeControls _) (by simp [initializeControls, NoJump]) state hpc ha
  simpa only [programAt, List.append_assoc, initialize_length] using hh

theorem head_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 3)) (ha : state.halted = false) :
    natRun rom (left ++ programAt left.length ++ right) 2 state =
      runOps rom (copyHead (5 * (left.length + 10))) state := by
  have hp : (left ++ initializeControls).length = left.length + 3 := by simp only [List.length_append, initialize_length]
  have hh := branch_segment_run rom (left ++ initializeControls)
    [.base (.base (.constant .old (5 * (left.length + 10))))]
    (tail (5 * (left.length + 3)) ++ right) (.jumpIfZero .total .old)
    (by simp [NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [programAt, copyHead, List.append_assoc, List.length_singleton, List.singleton_append] using hh

theorem tail_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 5)) (ha : state.halted = false) :
    natRun rom (left ++ programAt left.length ++ right) 5 state =
      runOps rom (tail (5 * (left.length + 3))) state := by
  let lead := (tail (5 * (left.length + 3))).take 4
  have hp : (left ++ initializeControls ++ copyHead (5 * (left.length + 10))).length = left.length + 5 := by
    simp [initializeControls, copyHead]
  have hh := branch_segment_run rom (left ++ initializeControls ++ copyHead (5 * (left.length + 10)))
    lead right (.jumpIfZero .flag .old) (by simp [lead, tail, NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [programAt, tail, lead, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.length_cons, List.length_nil, List.cons_append, List.nil_append] using hh

theorem init_inv (rom : PhysicalROM) (base length : Nat) (state : NatState)
    (hb : state.register .index = base) (hn : state.register .total = length) :
    ClearInv base state.heap 0 length (state.register .address) (runOps rom initializeControls state) := by
  simp [ClearInv, initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute,
    hb, hn]
  funext point
  simp only [cleared, Nat.add_zero]
  rw [ite_eq_right (by omega : ¬ (base ≤ point ∧ point < base))]

theorem head_inv (rom : PhysicalROM) (exit base moved remaining address : Nat)
    (original : Nat → Nat) (state : NatState) (hi : ClearInv base original moved remaining address state) :
    ClearInv base original moved remaining address (runOps rom (copyHead exit) state) := by
  rcases hi with ⟨hindex, htotal, hvalue, hfresh, hflag, haddress, hheap⟩
  simpa [ClearInv, copyHead, runOps, natExecuteOp, Op.execute, Instruction.execute] using
    And.intro hindex (And.intro htotal (And.intro hvalue (And.intro hfresh (And.intro hflag (And.intro haddress hheap)))))

theorem tail_inv (rom : PhysicalROM) (entry base moved remaining address : Nat)
    (original : Nat → Nat) (state : NatState) (hi : ClearInv base original moved remaining address state)
    (_hr : 0 < remaining) :
    ClearInv base original (moved + 1) (remaining - 1) address (runOps rom (tail entry) state) ∧
      (runOps rom (tail entry) state).pc = entry ∧
      (runOps rom (tail entry) state).halted = state.halted := by
  rcases hi with ⟨hindex, htotal, hvalue, hfresh, hflag, haddress, hheap⟩
  simp +decide only [ClearInv, tail, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Function.update_apply, ↓reduceIte, hindex, htotal, hvalue, hfresh, hflag, haddress, hheap,
    Nat.add_assoc, cleared_update]

theorem clear_loop_run (rom : PhysicalROM) (left right : List PackingOp)
    (base moved remaining address : Nat) (original : Nat → Nat) (state : NatState)
    (hi : ClearInv base original moved remaining address state)
    (hpc : state.pc = 5 * (left.length + 3)) (ha : state.halted = false) :
    let fresh := natRun rom (left ++ programAt left.length ++ right) (7 * remaining + 2) state
    ClearInv base original (moved + remaining) 0 address fresh ∧
      fresh.pc = 5 * (left.length + 10) ∧ fresh.halted = false := by
  induction remaining generalizing moved state with
  | zero =>
    dsimp only
    rw [show 7 * 0 + 2 = 2 from rfl, head_run rom left right state hpc ha]
    have hn := hi.2.1
    refine ⟨by simpa only [Nat.add_zero] using head_inv rom _ _ _ _ _ _ state hi, ?_, ?_⟩
    · simp [copyHead, runOps, natExecuteOp, Op.execute, Instruction.execute, hn]
    · exact (runOps_halted rom _ state).trans ha
  | succ remaining ih =>
    let a := runOps rom (copyHead (5 * (left.length + 10))) state
    have hai : ClearInv base original moved (remaining + 1) address a := head_inv rom _ _ _ _ _ _ state hi
    have hap : a.pc = 5 * (left.length + 5) := by
      have hn := hi.2.1
      simp [a, copyHead, runOps, natExecuteOp, Op.execute, Instruction.execute, hn, hpc]
      omega
    have haa : a.halted = false := (runOps_halted rom _ state).trans ha
    let b := runOps rom (tail (5 * (left.length + 3))) a
    have hb := tail_inv rom (5 * (left.length + 3)) base moved (remaining + 1) address original a hai (by omega)
    have hr := ih (moved + 1) b (by simpa only [Nat.add_sub_cancel] using hb.1) hb.2.1 (hb.2.2.trans haa)
    dsimp only
    rw [show 7 * (remaining + 1) + 2 = 2 + (5 + (7 * remaining + 2)) by omega,
      natRun_add, head_run rom left right state hpc ha,
      natRun_add, tail_run rom left right a hap haa]
    have hmoved : moved + 1 + remaining = moved + (remaining + 1) := by omega
    simpa only [b, hmoved] using hr

/-- A real fixed program clears exactly the selected finite range, while
the hardware control-bank base and every outside heap cell are preserved. -/
theorem clear_run (rom : PhysicalROM) (left right : List PackingOp) (base length : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hb : state.register .index = base) (hn : state.register .total = length) :
    let fresh := natRun rom (left ++ programAt left.length ++ right) (7 * length + 5) state
    (∀ index < length, fresh.heap (base + index) = 0) ∧
      (∀ point, point < base ∨ base + length ≤ point → fresh.heap point = state.heap point) ∧
      fresh.register .address = state.register .address ∧
      fresh.pc = 5 * (left.length + 10) ∧ fresh.halted = false := by
  let a := runOps rom initializeControls state
  have hi := init_inv rom base length state hb hn
  have hp : a.pc = 5 * (left.length + 3) := by
    simp [a, initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute, hpc]
    omega
  have ha' : a.halted = false := (runOps_halted rom _ state).trans ha
  have hr := clear_loop_run rom left right base 0 length (state.register .address) state.heap a hi hp ha'
  dsimp only
  rw [show 7 * length + 5 = 3 + (7 * length + 2) by omega, natRun_add, init_run rom left right state hpc ha]
  dsimp only at hr
  simp only [Nat.zero_add] at hr
  refine ⟨?_, ?_, hr.1.2.2.2.2.2.1, hr.2.1, hr.2.2⟩
  · intro index hindex
    rw [hr.1.2.2.2.2.2.2]
    exact cleared_zero state.heap base length index hindex
  · intro point hpoint
    rw [hr.1.2.2.2.2.2.2]
    exact cleared_frame state.heap base length point hpoint

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (start length : Nat) (state : WordState bits) :
    (packingDynamicTrace rom (programAt start) (7 * length + 5) state).length ≤ 84 * length + 60 :=
  (packingDynamicTrace_length_le rom _ _ state).trans_eq (by omega)

/-- A separate fixed initializer for the seven real virtual-register bank
words. It does not assume any part of the incoming heap is zero. -/
def clearVirtual : List PackingOp :=
  [.base (.base (.constant .value 0))] ++
    ([32, 33, 34, 35, 36, 37, 38] : List Nat).flatMap (fun slot =>
      [.base (.base (.constant .index slot)),
       .base (.base (.add .index .address .index)),
       .base (.base (.storeHeap .index .value))])

theorem clearVirtual_length : clearVirtual.length = 22 := rfl

theorem clearVirtual_straight : StraightProgram clearVirtual := by
  simp [clearVirtual, StraightProgram, StraightOp]

theorem clearVirtual_base {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom clearVirtual state).register .address = state.register .address := rfl

theorem clearVirtual_zero {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (slot : Nat) (hlo : 32 ≤ slot) (hhi : slot < 39) :
    (executeOps rom clearVirtual state).heap (state.register .address + BitVec.ofNat bits slot) = 0 := by
  interval_cases slot <;>
    simp [clearVirtual, executeOps, packingExecuteOp, wordOp, wordInstruction,
      Function.update_apply]

theorem clearVirtual_frame {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (point : BitVec bits)
    (hout : ∀ slot ∈ ([32, 33, 34, 35, 36, 37, 38] : List Nat),
      point ≠ state.register .address + BitVec.ofNat bits slot) :
    (executeOps rom clearVirtual state).heap point = state.heap point := by
  simp only [List.mem_cons] at hout
  simp [clearVirtual, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hout 32 (by simp), hout 33 (by simp), hout 34 (by simp),
    hout 35 (by simp), hout 36 (by simp), hout 37 (by simp), hout 38 (by simp)]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025
