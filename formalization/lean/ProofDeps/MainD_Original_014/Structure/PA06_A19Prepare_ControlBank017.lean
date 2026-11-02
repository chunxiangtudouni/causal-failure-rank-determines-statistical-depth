module

public import Structure.PA06_A19Prepare_ControlBank017_Geometry
public import PaperProofs.Structure.PA17_UniformGenerator_035aa
public import PaperProofs.Structure.PackingExecutionCost
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Private uncompiled runtime high-bank forward relocation.
The exact PA17 two-op copyHead and seven-op copyTail are reused. Only two
hardware control initializers are new: source, target, length are genuine
incoming register values. No dimension, source word, P, target or answer is
embedded in the fixed eleven-op code. Future caller code must actually
compute these three registers; no free setup or complete prepare is claimed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareControlBank017
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035j PA17UniformGenerator035m

abbrev head := PA17UniformGenerator035g.copyHead
abbrev tail := PA17UniformGenerator035g.copyTail

def initializeControls : List PackingOp :=
  [.base (.base (.constant .fresh 1)), .base (.base (.constant .flag 0))]

theorem initializeControls_length : initializeControls.length = 2 := rfl

def programAt (start : Nat) : List PackingOp :=
  initializeControls ++ head (5 * (start + 11)) ++ tail (5 * (start + 2))

theorem programAt_length (start : Nat) : (programAt start).length = 11 := rfl

theorem initializeControls_noJump : ∀ op ∈ initializeControls, NoJump op := by
  simp [initializeControls, NoJump]

theorem init_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ programAt left.length ++ right) 2 state =
      runOps rom initializeControls state := by
  have hrun := natRun_of_straight_segment rom
    (left ++ initializeControls ++ (head (5 * (left.length + 11)) ++ tail (5 * (left.length + 2)) ++ right))
    initializeControls left.length (by simp only [List.length_append]; change left.length + 2 ≤ left.length + 2 + (2 + 7 + right.length); omega)
    (PA17UniformGenerator035a.segment_index left initializeControls _)
    initializeControls_noJump state hpc ha
  simpa only [programAt, List.append_assoc, initializeControls_length] using hrun

theorem head_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 2)) (ha : state.halted = false) :
    natRun rom (left ++ programAt left.length ++ right) 2 state =
      runOps rom (head (5 * (left.length + 11))) state := by
  have hp : (left ++ initializeControls).length = left.length + 2 := by simp [initializeControls]
  have hrun := PA17UniformGenerator035g.branch_segment_run rom (left ++ initializeControls)
    [.base (.base (.constant .old (5 * (left.length + 11))))]
    (tail (5 * (left.length + 2)) ++ right) (.jumpIfZero .total .old)
    (by simp [NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [programAt, head, PA17UniformGenerator035g.copyHead, List.append_assoc,
    List.length_singleton, List.singleton_append] using hrun

theorem tail_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 4)) (ha : state.halted = false) :
    natRun rom (left ++ programAt left.length ++ right) 7 state =
      runOps rom (tail (5 * (left.length + 2))) state := by
  let lead := (tail (5 * (left.length + 2))).take 6
  have hp : (left ++ initializeControls ++ head (5 * (left.length + 11))).length = left.length + 4 := by
    simp [initializeControls, head, PA17UniformGenerator035g.copyHead]
  have hrun := PA17UniformGenerator035g.branch_segment_run rom
    (left ++ initializeControls ++ head (5 * (left.length + 11))) lead right (.jumpIfZero .flag .old)
    (by simp [lead, tail, PA17UniformGenerator035g.copyTail, NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [programAt, tail, PA17UniformGenerator035g.copyTail, lead, List.take_succ_cons,
    List.take_zero, List.append_assoc, List.cons_append, List.nil_append,
    List.length_cons, List.length_nil] using hrun

/-- Destination interval only is rewritten; every value is the ORIGINAL
source word. Forward disjointness will justify the next real source read. -/
def relocatedHeap (original : Nat → Nat) (source target moved : Nat) : Nat → Nat :=
  fun address => if target ≤ address ∧ address < target + moved then
    original (source + (address - target)) else original address

theorem relocatedHeap_target (original : Nat → Nat) (source target moved index : Nat)
    (hi : index < moved) :
    relocatedHeap original source target moved (target + index) = original (source + index) := by
  simp only [relocatedHeap, Nat.le_add_right, Nat.add_lt_add_iff_left, hi, and_self,
    ite_true, Nat.add_sub_cancel_left]

theorem relocatedHeap_frame (original : Nat → Nat) (source target moved address : Nat)
    (hout : address < target ∨ target + moved ≤ address) :
    relocatedHeap original source target moved address = original address := by
  simp only [relocatedHeap, ite_eq_right_iff]
  intro h
  omega

theorem relocatedHeap_source (original : Nat → Nat) (source target moved length : Nat)
    (hdisjoint : source + length ≤ target) (hi : moved < length) :
    relocatedHeap original source target moved (source + moved) = original (source + moved) := by
  exact relocatedHeap_frame original source target moved _ (Or.inl (by omega))

theorem relocatedHeap_update (original : Nat → Nat) (source target moved : Nat) :
    Function.update (relocatedHeap original source target moved) (target + moved)
      (original (source + moved)) = relocatedHeap original source target (moved + 1) := by
  funext address
  by_cases he : address = target + moved
  · subst address
    simp only [Function.update_self, relocatedHeap]
    rw [ite_eq_left (by omega), Nat.add_sub_cancel_left]
  · rw [Function.update_of_ne he]
    have hh : (target ≤ address ∧ address < target + (moved + 1)) ↔
        (target ≤ address ∧ address < target + moved) := by omega
    simp only [relocatedHeap, hh]

def CopyInv (source target : Nat) (original : Nat → Nat) (moved remaining : Nat) (state : NatState) : Prop :=
  state.register .index = target + moved ∧ state.register .address = source + moved ∧
    state.register .total = remaining ∧ state.register .fresh = 1 ∧ state.register .flag = 0 ∧
    state.heap = relocatedHeap original source target moved

theorem init_inv (rom : PhysicalROM) (source target length : Nat) (state : NatState)
    (hs : state.register .address = source) (ht : state.register .index = target)
    (hn : state.register .total = length) :
    CopyInv source target state.heap 0 length (runOps rom initializeControls state) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · simpa [initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute] using ht
  · simpa [initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute] using hs
  · exact hn
  · funext address
    simp [initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute, relocatedHeap]

theorem head_inv (rom : PhysicalROM) (exit source target moved remaining : Nat)
    (original : Nat → Nat) (state : NatState) (hi : CopyInv source target original moved remaining state) :
    CopyInv source target original moved remaining (runOps rom (head exit) state) := hi

theorem tail_inv (rom : PhysicalROM) (entry source target moved remaining length : Nat)
    (original : Nat → Nat) (state : NatState) (hi : CopyInv source target original moved remaining state)
    (hd : source + length ≤ target) (hm : moved < length) :
    CopyInv source target original (moved + 1) (remaining - 1) (runOps rom (tail entry) state) := by
  rcases hi with ⟨hindex, haddress, htotal, hfresh, hflag, hheap⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change state.register .index + state.register .fresh = target + (moved + 1)
    rw [hindex, hfresh]
    omega
  · change state.register .address + state.register .fresh = source + (moved + 1)
    rw [haddress, hfresh]
    omega
  · change state.register .total - state.register .fresh = remaining - 1
    rw [htotal, hfresh]
  · exact hfresh
  · exact hflag
  · change Function.update state.heap (state.register .index) (state.heap (state.register .address)) = _
    rw [hheap, hindex, haddress, relocatedHeap_source original source target moved length hd hm,
      relocatedHeap_update]

theorem copy_loop_run (rom : PhysicalROM) (left right : List PackingOp)
    (source target length : Nat) (original : Nat → Nat) (hd : source + length ≤ target)
    (remaining moved : Nat) (state : NatState) (hsum : moved + remaining = length)
    (hpc : state.pc = 5 * (left.length + 2)) (ha : state.halted = false)
    (hi : CopyInv source target original moved remaining state) :
    let fresh := natRun rom (left ++ programAt left.length ++ right) (9 * remaining + 2) state
    CopyInv source target original (moved + remaining) 0 fresh ∧
      fresh.pc = 5 * (left.length + 11) ∧ fresh.halted = false := by
  induction remaining generalizing moved state with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, head_run rom left right state hpc ha]
    refine ⟨?_, ?_, (runOps_halted rom _ state).trans ha⟩
    · simpa only [Nat.add_zero] using head_inv rom (5 * (left.length + 11)) source target moved 0 original state hi
    · rw [PA17UniformGenerator035g.copy_head_pc, hi.2.2.1, ite_eq_left rfl]
  | succ remaining ih =>
    let tested := runOps rom (head (5 * (left.length + 11))) state
    have htest := head_inv rom (5 * (left.length + 11)) source target moved (remaining + 1) original state hi
    have htpc : tested.pc = 5 * (left.length + 4) := by
      rw [PA17UniformGenerator035g.copy_head_pc, hi.2.2.1, ite_eq_right (by omega), hpc]
      omega
    have hta : tested.halted = false := (runOps_halted rom _ state).trans ha
    let movedState := runOps rom (tail (5 * (left.length + 2))) tested
    have hm : CopyInv source target original (moved + 1) remaining movedState := by
      simpa only [Nat.add_sub_cancel] using
        tail_inv rom (5 * (left.length + 2)) source target moved (remaining + 1) length original tested htest hd (by omega)
    have hmpc : movedState.pc = 5 * (left.length + 2) :=
      PA17UniformGenerator035g.copy_tail_pc rom _ tested htest.2.2.2.2.1
    have hma : movedState.halted = false := (runOps_halted rom _ tested).trans hta
    have hr := ih (moved + 1) movedState (by omega) hmpc hma hm
    have htime : 9 * (remaining + 1) + 2 = (2 + 7) + (9 * remaining + 2) := by omega
    have hcycle : natRun rom (left ++ programAt left.length ++ right) (2 + 7) state = movedState := by
      rw [natRun_add, head_run rom left right state hpc ha, tail_run rom left right tested htpc hta]
    rw [htime, natRun_add, hcycle]
    have hindex : moved + (remaining + 1) = moved + 1 + remaining := by omega
    rw [hindex]
    exact hr

theorem copy_run (rom : PhysicalROM) (left right : List PackingOp) (source target length : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hs : state.register .address = source) (ht : state.register .index = target)
    (hn : state.register .total = length) (hd : source + length ≤ target) :
    let fresh := natRun rom (left ++ programAt left.length ++ right) (9 * length + 4) state
    CopyInv source target state.heap length 0 fresh ∧ fresh.pc = 5 * (left.length + 11) ∧ fresh.halted = false := by
  let prepared := runOps rom initializeControls state
  have hp : prepared.pc = 5 * (left.length + 2) := by
    rw [runOps_pc rom _ state initializeControls_noJump, hpc]
    rfl
  have hh := copy_loop_run rom left right source target length state.heap hd length 0 prepared
    (by omega) hp ((runOps_halted rom _ state).trans ha) (init_inv rom source target length state hs ht hn)
  have htime : 9 * length + 4 = 2 + (9 * length + 2) := by omega
  rw [htime, natRun_add, init_run rom left right state hpc ha]
  simpa only [Nat.zero_add] using hh

/-- Real copied data at every offset, paired with a real heap frame.
The unchanged old base pointer value is not silently rebased. -/
theorem copy_values_frame (rom : PhysicalROM) (left right : List PackingOp) (source target length : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hs : state.register .address = source) (ht : state.register .index = target)
    (hn : state.register .total = length) (hd : source + length ≤ target) :
    let fresh := natRun rom (left ++ programAt left.length ++ right) (9 * length + 4) state
    (∀ index < length, fresh.heap (target + index) = state.heap (source + index)) ∧
      (∀ address, address < target ∨ target + length ≤ address → fresh.heap address = state.heap address) := by
  have hr := copy_run rom left right source target length state hpc ha hs ht hn hd
  constructor
  · intro index hi
    rw [hr.1.2.2.2.2.2]
    exact relocatedHeap_target state.heap source target length index hi
  · intro address hout
    rw [hr.1.2.2.2.2.2]
    exact relocatedHeap_frame state.heap source target length address hout

/-- Computed raw-cache contents are transported by actual physical stores.
Caller control registers still have to be established by an actual setup. -/
theorem compact_cache_copy (N q t P : Nat) (hq : 0 < q) (rom : PhysicalROM)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hs : state.register .address = 0) (ht : state.register .index = cacheBase N q t P)
    (hn : state.register .total = cacheLength N q) :
    let fresh := natRun rom (left ++ programAt left.length ++ right) (9 * cacheLength N q + 4) state
    (∀ address < cacheLength N q, fresh.heap (cacheBase N q t P + address) = state.heap address) ∧
      (∀ address < cacheBase N q t P, fresh.heap address = state.heap address) := by
  have h := copy_values_frame rom left right 0 (cacheBase N q t P) (cacheLength N q)
    state hpc ha hs ht hn (by simpa only [Nat.zero_add] using source_target_disjoint N q t P hq)
  refine ⟨?_, ?_⟩
  · simpa only [Nat.zero_add] using h.1
  · intro address had
    exact h.2 address (Or.inl had)

theorem real_trace_bound {bits : Nat} (rom : PhysicalROM) (start length : Nat) (state : WordState bits) :
    (packingDynamicTrace rom (programAt start) (9 * length + 4) state).length ≤ 108 * length + 48 := by
  exact (packingDynamicTrace_length_le rom (programAt start) (9 * length + 4) state).trans_eq (by omega)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareControlBank017
