module

public import Structure.PA06_A19Prepare_ControlBank017
public import Structure.PA06_A19Prepare_ChildrenCache023_Data
public import Structure.PSTR_HD_StaticLayout_019
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private candidate: the actual fixed nine-op forward copy used by the
static metadata producer. Hardware.address remains the runtime control base.
index is the source, old is the target, total is the remaining word count.
The output lies BELOW the source cache; no input-dependent literal occurs. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety
open PA06A19PrepareControlBank017 (relocatedHeap relocatedHeap_target relocatedHeap_frame relocatedHeap_update)

def copyHead (exit : Nat) : List PackingOp :=
  [.base (.base (.constant .value exit)), .jumpIfZero .total .value]

def copyTail (entry : Nat) : List PackingOp :=
  [.base (.base (.loadHeap .value .index)), .base (.base (.storeHeap .old .value)),
   .base (.base (.add .index .index .fresh)), .base (.base (.add .old .old .fresh)),
   .base (.subtract .total .total .fresh), .base (.base (.constant .value entry)),
   .jumpIfZero .flag .value]

def copyProgramAt (start : Nat) : List PackingOp :=
  copyHead (5 * (start + 9)) ++ copyTail (5 * start)

theorem copyProgramAt_length (start : Nat) : (copyProgramAt start).length = 9 := rfl

theorem copy_head_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ copyProgramAt left.length ++ right) 2 state =
      runOps rom (copyHead (5 * (left.length + 9))) state := by
  have h := PA17UniformGenerator035g.branch_segment_run rom left
    [.base (.base (.constant .value (5 * (left.length + 9))))]
    (copyTail (5 * left.length) ++ right) (.jumpIfZero .total .value)
    (by simp [NoJump]) state hpc ha
  simpa only [copyProgramAt, copyHead, List.append_assoc, List.length_singleton,
    List.singleton_append] using h

theorem copy_tail_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 2)) (ha : state.halted = false) :
    natRun rom (left ++ copyProgramAt left.length ++ right) 7 state =
      runOps rom (copyTail (5 * left.length)) state := by
  let lead := (copyTail (5 * left.length)).take 6
  have hp : (left ++ copyHead (5 * (left.length + 9))).length = left.length + 2 := by
    simp [copyHead]
  have h := PA17UniformGenerator035g.branch_segment_run rom
    (left ++ copyHead (5 * (left.length + 9))) lead right (.jumpIfZero .flag .value)
    (by simp [lead, copyTail, NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [copyProgramAt, copyTail, lead, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append, List.length_cons, List.length_nil] using h

theorem copy_head_pc (rom : PhysicalROM) (exit : Nat) (state : NatState) :
    (runOps rom (copyHead exit) state).pc =
      if state.register .total = 0 then exit else state.pc + 10 := by
  simp [copyHead, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem copy_tail_pc (rom : PhysicalROM) (entry : Nat) (state : NatState)
    (hflag : state.register .flag = 0) : (runOps rom (copyTail entry) state).pc = entry := by
  simp [copyTail, runOps, natExecuteOp, Op.execute, Instruction.execute, hflag]

/-- The actual output is below the source bank, so a copied source word has
not been overwritten by any previous output store. -/
theorem relocatedHeap_source_below (original : Nat → Nat) (source target moved length : Nat)
    (hdisjoint : target + length ≤ source) (_hi : moved < length) :
    relocatedHeap original source target moved (source + moved) = original (source + moved) := by
  exact relocatedHeap_frame original source target moved _ (Or.inr (by omega))

def CopyInv (CB source target : Nat) (original : Nat → Nat) (moved remaining : Nat)
    (state : NatState) : Prop :=
  state.register .address = CB ∧ state.register .index = source + moved ∧
    state.register .old = target + moved ∧ state.register .total = remaining ∧
    state.register .fresh = 1 ∧ state.register .flag = 0 ∧
    state.heap = relocatedHeap original source target moved

theorem copy_head_inv (rom : PhysicalROM) (exit CB source target moved remaining : Nat)
    (original : Nat → Nat) (state : NatState)
    (hi : CopyInv CB source target original moved remaining state) :
    CopyInv CB source target original moved remaining (runOps rom (copyHead exit) state) := hi

theorem copy_tail_inv (rom : PhysicalROM) (entry CB source target moved remaining length : Nat)
    (original : Nat → Nat) (state : NatState)
    (hi : CopyInv CB source target original moved remaining state)
    (hd : target + length ≤ source) (hm : moved < length) :
    CopyInv CB source target original (moved + 1) (remaining - 1)
      (runOps rom (copyTail entry) state) := by
  rcases hi with ⟨hCB, hindex, hold, htotal, hfresh, hflag, hheap⟩
  refine ⟨hCB, ?_, ?_, ?_, hfresh, hflag, ?_⟩
  · change state.register .index + state.register .fresh = source + (moved + 1)
    rw [hindex, hfresh]
    omega
  · change state.register .old + state.register .fresh = target + (moved + 1)
    rw [hold, hfresh]
    omega
  · change state.register .total - state.register .fresh = remaining - 1
    rw [htotal, hfresh]
  · change Function.update state.heap (state.register .old) (state.heap (state.register .index)) = _
    rw [hheap, hold, hindex, relocatedHeap_source_below original source target moved length hd hm,
      relocatedHeap_update]

theorem copy_loop_run (rom : PhysicalROM) (left right : List PackingOp)
    (CB source target length : Nat) (original : Nat → Nat) (hd : target + length ≤ source)
    (remaining moved : Nat) (state : NatState) (hsum : moved + remaining = length)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hi : CopyInv CB source target original moved remaining state) :
    let after := natRun rom (left ++ copyProgramAt left.length ++ right) (9 * remaining + 2) state
    CopyInv CB source target original (moved + remaining) 0 after ∧
      after.pc = 5 * (left.length + 9) ∧ after.halted = false := by
  induction remaining generalizing moved state with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, copy_head_run rom left right state hpc ha]
    refine ⟨?_, ?_, (runOps_halted rom _ state).trans ha⟩
    · simpa only [Nat.add_zero] using
        copy_head_inv rom (5 * (left.length + 9)) CB source target moved 0 original state hi
    · rw [copy_head_pc, hi.2.2.2.1, ite_eq_left rfl]
  | succ remaining ih =>
    let tested := runOps rom (copyHead (5 * (left.length + 9))) state
    have ht := copy_head_inv rom (5 * (left.length + 9)) CB source target moved
      (remaining + 1) original state hi
    have htpc : tested.pc = 5 * (left.length + 2) := by
      rw [copy_head_pc, hi.2.2.2.1, ite_eq_right (by omega), hpc]
      omega
    have hta : tested.halted = false := (runOps_halted rom _ state).trans ha
    let next := runOps rom (copyTail (5 * left.length)) tested
    have hn : CopyInv CB source target original (moved + 1) remaining next := by
      simpa only [Nat.add_sub_cancel] using copy_tail_inv rom (5 * left.length) CB source target moved
        (remaining + 1) length original tested ht hd (by omega)
    have hnpc : next.pc = 5 * left.length := copy_tail_pc rom _ tested ht.2.2.2.2.2.1
    have hna : next.halted = false := (runOps_halted rom _ tested).trans hta
    have hr := ih (moved + 1) next (by omega) hnpc hna hn
    have htime : 9 * (remaining + 1) + 2 = (2 + 7) + (9 * remaining + 2) := by omega
    have hcycle : natRun rom (left ++ copyProgramAt left.length ++ right) (2 + 7) state = next := by
      rw [natRun_add, copy_head_run rom left right state hpc ha,
        copy_tail_run rom left right tested htpc hta]
    rw [htime, natRun_add, hcycle]
    have he : moved + (remaining + 1) = moved + 1 + remaining := by omega
    rw [he]
    exact hr

/-- Complete real Nat copy, ACTIVE at the fallthrough, with output data,
full heap frame, unchanged runtime CB and advanced target pointer. -/
theorem copy_run (rom : PhysicalROM) (left right : List PackingOp) (CB source target length : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hCB : state.register .address = CB) (hs : state.register .index = source)
    (ht : state.register .old = target) (hn : state.register .total = length)
    (hfresh : state.register .fresh = 1) (hflag : state.register .flag = 0)
    (hd : target + length ≤ source) :
    let after := natRun rom (left ++ copyProgramAt left.length ++ right) (9 * length + 2) state
    (∀ index < length, after.heap (target + index) = state.heap (source + index)) ∧
      (∀ address, address < target ∨ target + length ≤ address → after.heap address = state.heap address) ∧
      after.register .address = CB ∧ after.register .old = target + length ∧
      after.register .fresh = 1 ∧ after.register .flag = 0 ∧
      after.pc = 5 * (left.length + 9) ∧ after.halted = false := by
  have initial : CopyInv CB source target state.heap 0 length state := by
    refine ⟨hCB, by simpa using hs, by simpa using ht, hn, hfresh, hflag, ?_⟩
    funext address
    simp [relocatedHeap]
  have hr := copy_loop_run rom left right CB source target length state.heap hd length 0 state
    (by omega) hpc ha initial
  dsimp only at hr ⊢
  have hi : CopyInv CB source target state.heap length 0
      (natRun rom (left ++ copyProgramAt left.length ++ right) (9 * length + 2) state) := by
    simpa only [Nat.zero_add] using hr.1
  rcases hi with ⟨hCB', _hindex, hold', _htotal, hfresh', hflag', hheap'⟩
  refine ⟨?_, ?_, hCB', hold', hfresh', hflag', hr.2.1, hr.2.2⟩
  · intro index hi
    rw [hheap']
    exact relocatedHeap_target state.heap source target length index hi
  · intro address hout
    rw [hheap']
    exact relocatedHeap_frame state.heap source target length address hout

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
