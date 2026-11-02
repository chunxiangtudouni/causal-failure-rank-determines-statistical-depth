module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! All-clock safety of the real CB-preserving nine-op copy. The original
same-ISA branch/prefix engines are reused. Source values and room are local
cache facts, to be supplied by the actual metadata factory/entry data. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035l PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (RunFacts)

theorem copy_head_numeric (rom : PhysicalROM) (B H exit : Nat) (state : NatState)
    (hr : RegistersLE B state) (he : exit ≤ B) : NumericSafe B H rom (copyHead exit) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 2 at hc
    interval_cases count <;> cases reg <;> simp [copyHead, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 2 at hc
    interval_cases count <;> trivial

theorem copy_tail_numeric (rom : PhysicalROM) (B H entry : Nat) (state : NatState)
    (hr : RegistersLE B state) (he : entry ≤ B)
    (hv : state.heap (state.register .index) ≤ B)
    (hs : state.register .index < H) (ht : state.register .old < H)
    (hnextS : state.register .index + state.register .fresh ≤ B)
    (hnextT : state.register .old + state.register .fresh ≤ B) :
    NumericSafe B H rom (copyTail entry) state := by
  have hsub := (Nat.sub_le (state.register .total) (state.register .fresh)).trans (hr .total)
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 7 at hc
    interval_cases count <;> cases reg <;> simp [copyTail, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 7 at hc
    interval_cases count <;>
      simp [copyTail, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hs, ht]

theorem copy_head_safe (rom : PhysicalROM) (B H exitIndex : Nat) (left right : List PackingOp)
    (he : 5 * exitIndex ≤ B) (ht : exitIndex ≤ (left ++ copyHead (5 * exitIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state) :
    RunFacts B H rom (left ++ copyHead (5 * exitIndex) ++ right) 2 state := by
  let lead : List PackingOp := [.base (.base (.constant .value (5 * exitIndex)))]
  have split : copyHead (5 * exitIndex) = lead ++ [.jumpIfZero .total .value] := rfl
  have numeric := copy_head_numeric rom B H (5 * exitIndex) state hr he
  have safe : RunSafe B H rom (left ++ copyHead (5 * exitIndex) ++ right) 2 state := by
    rw [split]
    apply branch_segment_safe rom B H left lead right (.jumpIfZero .total .value)
      (by simp [lead, NoJump]) state hpc ha (by rw [← split]; exact numeric)
    rw [← split]
    by_cases hz : state.register .total = 0
    · exact ⟨exitIndex, ht, by rw [copy_head_pc, ite_eq_left hz]⟩
    · refine ⟨left.length + 2, by simp only [List.length_append]; change left.length + 2 ≤ left.length + 2 + right.length; omega, ?_⟩
      rw [copy_head_pc, ite_eq_right hz, hpc]
      omega
  refine ⟨safe, ?_⟩
  intro count hc
  rw [split]
  rw [branch_segment_prefix rom left lead right (.jumpIfZero .total .value)
    (by simp [lead, NoJump]) state hpc ha count (by change count ≤ 1 + 1; omega)]
  interval_cases count <;> rfl

theorem copy_tail_safe (rom : PhysicalROM) (B H entryIndex : Nat) (left right : List PackingOp)
    (he : 5 * entryIndex ≤ B) (ht : entryIndex ≤ (left ++ copyTail (5 * entryIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hz : state.register .flag = 0) (hv : state.heap (state.register .index) ≤ B)
    (hs : state.register .index < H) (htarget : state.register .old < H)
    (hnextS : state.register .index + state.register .fresh ≤ B)
    (hnextT : state.register .old + state.register .fresh ≤ B) :
    RunFacts B H rom (left ++ copyTail (5 * entryIndex) ++ right) 7 state := by
  let lead := (copyTail (5 * entryIndex)).take 6
  have split : copyTail (5 * entryIndex) = lead ++ [.jumpIfZero .flag .value] := rfl
  have numeric := copy_tail_numeric rom B H (5 * entryIndex) state hr he hv hs htarget hnextS hnextT
  have safe : RunSafe B H rom (left ++ copyTail (5 * entryIndex) ++ right) 7 state := by
    rw [split]
    apply branch_segment_safe rom B H left lead right (.jumpIfZero .flag .value)
      (by simp [lead, copyTail, NoJump]) state hpc ha (by rw [← split]; exact numeric)
    rw [← split]
    exact ⟨entryIndex, ht, copy_tail_pc rom _ state hz⟩
  refine ⟨safe, ?_⟩
  intro count hc
  rw [split]
  rw [branch_segment_prefix rom left lead right (.jumpIfZero .flag .value)
    (by simp [lead, copyTail, NoJump]) state hpc ha count (by change count ≤ 6 + 1; omega)]
  interval_cases count <;> rfl

/-- Complete actual copy loop, including all intermediate accesses and
hardwareCB values. End pointers may equalH; actual loads/stores are <H. -/
theorem copy_loop_safe (rom : PhysicalROM) (B H : Nat) (left right : List PackingOp)
    (CB source target length : Nat) (original : Nat → Nat) (hd : target + length ≤ source)
    (hsource : source + length ≤ H) (htarget : target + length ≤ H) (hH : H ≤ B)
    (hwords : ∀ position < length, original (source + position) ≤ B)
    (hpcB : 5 * (left ++ copyProgramAt left.length ++ right).length ≤ B)
    (remaining moved : Nat) (state : NatState) (hsum : moved + remaining = length)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE B state) (hi : CopyInv CB source target original moved remaining state) :
    RunFacts B H rom (left ++ copyProgramAt left.length ++ right) (9 * remaining + 2) state := by
  induction remaining generalizing moved state with
  | zero =>
    have safe := copy_head_safe rom B H (left.length + 9) left (copyTail (5 * left.length) ++ right)
      (by simp only [List.length_append, copyProgramAt_length] at hpcB; omega)
      (by simp only [List.length_append]; change left.length + 9 ≤ left.length + 2 + (7 + right.length); omega)
      state hpc ha hr
    simpa only [Nat.mul_zero, Nat.zero_add, copyProgramAt, List.append_assoc] using safe
  | succ remaining ih =>
    let code := left ++ copyProgramAt left.length ++ right
    let tested := runOps rom (copyHead (5 * (left.length + 9))) state
    have headSafe : RunFacts B H rom code 2 state := by
      have safe := copy_head_safe rom B H (left.length + 9) left (copyTail (5 * left.length) ++ right)
        (by simp only [List.length_append, copyProgramAt_length] at hpcB; omega)
        (by simp only [List.length_append]; change left.length + 9 ≤ left.length + 2 + (7 + right.length); omega)
        state hpc ha hr
      simpa only [code, copyProgramAt, List.append_assoc] using safe
    have headRun : natRun rom code 2 state = tested := copy_head_run rom left right state hpc ha
    have ht := copy_head_inv rom (5 * (left.length + 9)) CB source target moved (remaining + 1) original state hi
    have htPC : tested.pc = 5 * (left.length + 2) := by
      rw [copy_head_pc, hi.2.2.2.1, ite_eq_right (by omega), hpc]
      omega
    have htActive : tested.halted = false := (runOps_halted rom _ state).trans ha
    have htRegs : RegistersLE B tested := by
      have h := ((headSafe.1).final _ _ _ _ _).1
      rw [headRun] at h
      exact h
    have tailSafe : RunFacts B H rom code 7 tested := by
      let leading := left ++ copyHead (5 * (left.length + 9))
      have hp : leading.length = left.length + 2 := by simp [leading, copyHead]
      have safe := copy_tail_safe rom B H left.length leading right
        (by simp only [List.length_append, copyProgramAt_length] at hpcB; omega)
        (by simp only [List.length_append, hp]; change left.length ≤ left.length + 2 + 7 + right.length; omega)
        tested (by rw [hp]; exact htPC) htActive htRegs ht.2.2.2.2.2.1
        (by
          rw [ht.2.1, ht.2.2.2.2.2.2, relocatedHeap_source_below original source target moved length hd (by omega)]
          exact hwords moved (by omega))
        (by rw [ht.2.1]; omega) (by rw [ht.2.2.1]; omega)
        (by rw [ht.2.1, ht.2.2.2.2.1]; omega) (by rw [ht.2.2.1, ht.2.2.2.2.1]; omega)
      simpa only [code, copyProgramAt, leading, List.append_assoc] using safe
    let next := runOps rom (copyTail (5 * left.length)) tested
    have tailRun : natRun rom code 7 tested = next := copy_tail_run rom left right tested htPC htActive
    have hn : CopyInv CB source target original (moved + 1) remaining next := by
      simpa only [Nat.add_sub_cancel] using copy_tail_inv rom (5 * left.length) CB source target moved
        (remaining + 1) length original tested ht hd (by omega)
    have hnPC : next.pc = 5 * left.length := copy_tail_pc rom _ tested ht.2.2.2.2.2.1
    have hnActive : next.halted = false := (runOps_halted rom _ tested).trans htActive
    have hnRegs : RegistersLE B next := by
      have h := ((tailSafe.1).final _ _ _ _ _).1
      rw [tailRun] at h
      exact h
    have rest := ih (moved + 1) next (by omega) hnPC hnActive hnRegs hn
    have cycle : natRun rom code (2 + 7) state = next := by rw [natRun_add, headRun, tailRun]
    have first := PA06A19PrepareChildrenCache023.RunFacts.add B H rom code 2 7 state headSafe
      (by rw [headRun]; exact tailSafe)
    have all := PA06A19PrepareChildrenCache023.RunFacts.add B H rom code (2 + 7) (9 * remaining + 2) state first
      (by rw [cycle]; exact rest)
    rw [show 9 * (remaining + 1) + 2 = (2 + 7) + (9 * remaining + 2) by omega]
    exact all

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
