module

public import Structure.PA06_A19Prepare_FiniteClear025
public import Structure.PA06_A19Prepare_ControlBank017_Safety
public import Structure.PA06_A19Prepare_NodeBit015

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Word/access safety of025's actual ten-op finite zeroing loop. The
three-register initializer, unchanged PA17 two-op head and five-op store
tail are certified from ordinary runtime bounds. The original Nat clear
semantics and exact7*length+5 clock are reused. No caller RunSafe, source
value bound, infinite zero heap or width16 register restriction is assumed.
The runtime address/control-bank register is never used as the clear target.
Concrete setup of index/total remains026's separate actual-code obligation. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025Safety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035a PA17UniformGenerator035g
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareFiniteClear025

theorem initialize_numeric (rom : PhysicalROM) (B heapWords : Nat)
    (hone : 1 ≤ B) (state : NatState) (hr : RegistersLE B state) :
    NumericSafe B heapWords rom initializeControls state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 3 at hc
    interval_cases count <;> cases register <;>
      simp [initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 3 at hc
    interval_cases count <;> trivial

theorem tail_numeric (rom : PhysicalROM) (B heapWords entry : Nat) (he : entry ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (htarget : state.register .index < heapWords)
    (hnext : state.register .index + state.register .fresh ≤ B) :
    NumericSafe B heapWords rom (tail entry) state := by
  have hsub := (Nat.sub_le (state.register .total) (state.register .fresh)).trans (hr .total)
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 5 at hc
    interval_cases count <;> cases register <;>
      simp [tail, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 5 at hc
    interval_cases count <;>
      simp [tail, runOps, NatAccessFits, AccessFits, htarget]

theorem tail_safe (rom : PhysicalROM) (B heapWords entryIndex : Nat) (left right : List PackingOp)
    (he : 5 * entryIndex ≤ B) (ht : entryIndex ≤ (left ++ tail (5 * entryIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE B state) (hflag : state.register .flag = 0)
    (htarget : state.register .index < heapWords)
    (hnext : state.register .index + state.register .fresh ≤ B) :
    RunSafe B heapWords rom (left ++ tail (5 * entryIndex) ++ right) 5 state := by
  let lead := (tail (5 * entryIndex)).take 4
  have split : tail (5 * entryIndex) = lead ++ [.jumpIfZero .flag .old] := rfl
  rw [split]
  apply branch_segment_safe rom B heapWords left lead right (.jumpIfZero .flag .old)
    (by simp [lead, tail, NoJump]) state hpc ha
    (by rw [← split]; exact tail_numeric rom B heapWords _ he state hr htarget hnext)
  rw [← split]
  refine ⟨entryIndex, ht, ?_⟩
  simp [tail, runOps, natExecuteOp, Op.execute, Instruction.execute, hflag]

/-- Safety from a real in-loop invariant, with every transient index and
remaining counter bounded by the selected finite interval. -/
theorem clear_loop_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (base length : Nat) (original : Nat → Nat)
    (hendB : base + length ≤ B) (hendH : base + length ≤ heapWords)
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B)
    (remaining moved address : Nat) (state : NatState) (hsum : moved + remaining = length)
    (hpc : state.pc = 5 * (left.length + 3)) (ha : state.halted = false)
    (hr : RegistersLE B state) (hi : ClearInv base original moved remaining address state) :
    RunSafe B heapWords rom (left ++ programAt left.length ++ right) (7 * remaining + 2) state := by
  induction remaining generalizing moved state with
  | zero =>
    have hp : (left ++ initializeControls).length = left.length + 3 := by
      simp only [List.length_append, initialize_length]
    have hhead := PA17UniformGenerator035aa.copyHead_safe rom B heapWords (left.length + 10)
      (left ++ initializeControls) (tail (5 * (left.length + 3)) ++ right)
      (by simp only [List.length_append, programAt_length] at hpcB; omega)
      (by
        have lenHead : (copyHead (5 * (left.length + 10))).length = 2 := rfl
        simp only [List.length_append, hp, lenHead, tail_length]
        omega) state (by rw [hp]; exact hpc) ha hr
    simpa only [Nat.mul_zero, Nat.zero_add, programAt, List.append_assoc] using hhead
  | succ remaining ih =>
    let allCode := left ++ programAt left.length ++ right
    let tested := runOps rom (copyHead (5 * (left.length + 10))) state
    have hhead : RunSafe B heapWords rom allCode 2 state := by
      have hp : (left ++ initializeControls).length = left.length + 3 := by
        simp only [List.length_append, initialize_length]
      have headSafe := PA17UniformGenerator035aa.copyHead_safe rom B heapWords (left.length + 10)
        (left ++ initializeControls) (tail (5 * (left.length + 3)) ++ right)
        (by simp only [List.length_append, programAt_length] at hpcB; omega)
        (by
          have lenHead : (copyHead (5 * (left.length + 10))).length = 2 := rfl
          simp only [List.length_append, hp, lenHead, tail_length]
          omega) state (by rw [hp]; exact hpc) ha hr
      simpa only [allCode, programAt, List.append_assoc] using headSafe
    have hheadRun : natRun rom allCode 2 state = tested := head_run rom left right state hpc ha
    have testedInv := head_inv rom (5 * (left.length + 10)) base moved (remaining + 1) address original state hi
    have testedPC : tested.pc = 5 * (left.length + 5) := by
      rw [copy_head_pc, hi.2.1, ite_eq_right (by omega), hpc]
      omega
    have testedActive : tested.halted = false := (runOps_halted rom _ state).trans ha
    have testedRegs : RegistersLE B tested := by
      have final := hhead.final _ _ _ _ _
      rw [hheadRun] at final
      exact final.1
    have tailSafe : RunSafe B heapWords rom allCode 5 tested := by
      let codeFront := left ++ initializeControls ++ copyHead (5 * (left.length + 10))
      have hp : codeFront.length = left.length + 5 := by
        simp [codeFront, initializeControls, copyHead]
      have hs := tail_safe rom B heapWords (left.length + 3) codeFront right
        (by simp only [List.length_append, programAt_length] at hpcB; omega)
        (by simp only [List.length_append, hp, tail_length]; omega)
        tested (by rw [hp]; exact testedPC) testedActive testedRegs testedInv.2.2.2.2.1
        (by rw [testedInv.1]; omega)
        (by rw [testedInv.1, testedInv.2.2.2.1]; omega)
      simpa only [allCode, programAt, codeFront, List.append_assoc] using hs
    let movedState := runOps rom (tail (5 * (left.length + 3))) tested
    have tailRun : natRun rom allCode 5 tested = movedState := tail_run rom left right tested testedPC testedActive
    have movedInv := tail_inv rom (5 * (left.length + 3)) base moved (remaining + 1) address original tested testedInv (by omega)
    have movedPC : movedState.pc = 5 * (left.length + 3) := movedInv.2.1
    have movedActive : movedState.halted = false := movedInv.2.2.trans testedActive
    have movedRegs : RegistersLE B movedState := by
      have final := tailSafe.final _ _ _ _ _
      rw [tailRun] at final
      exact final.1
    have rest := ih (moved + 1) movedState (by omega) movedPC movedActive movedRegs
      (by simpa only [Nat.add_sub_cancel] using movedInv.1)
    have cycleRun : natRun rom allCode (2 + 5) state = movedState := by
      rw [natRun_add, hheadRun, tailRun]
    have cycleSafe := RunSafe.add _ _ _ allCode 2 5 state hhead (by rw [hheadRun]; exact tailSafe)
    have allSafe := RunSafe.add _ _ _ allCode (2 + 5) (7 * remaining + 2) state cycleSafe
      (by rw [cycleRun]; exact rest)
    have time : 7 * (remaining + 1) + 2 = (2 + 5) + (7 * remaining + 2) := by omega
    rw [time]
    exact allSafe

theorem clear_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (base length : Nat) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hone : 1 ≤ B) (hbase : state.register .index = base) (hlen : state.register .total = length)
    (hendB : base + length ≤ B) (hendH : base + length ≤ heapWords)
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B) :
    RunSafe B heapWords rom (left ++ programAt left.length ++ right) (7 * length + 5) state := by
  let allCode := left ++ programAt left.length ++ right
  let prepared := runOps rom initializeControls state
  have initSafe : RunSafe B heapWords rom allCode 3 state := by
    have hs := straight_segment_safe rom B heapWords left initializeControls
      (copyHead (5 * (left.length + 10)) ++ tail (5 * (left.length + 3)) ++ right)
      (by simp [initializeControls, NoJump]) state hpc ha (initialize_numeric rom B heapWords hone state hr)
    simpa only [allCode, programAt, List.append_assoc, initialize_length] using hs
  have initRun : natRun rom allCode 3 state = prepared := init_run rom left right state hpc ha
  have preparedPC : prepared.pc = 5 * (left.length + 3) := by
    simp [prepared, initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute, hpc]
    omega
  have preparedRegs : RegistersLE B prepared := by
    have final := initSafe.final _ _ _ _ _
    rw [initRun] at final
    exact final.1
  have rest := clear_loop_safe rom B heapWords left right base length state.heap hendB hendH hpcB length 0
    (state.register .address) prepared (by omega) preparedPC ((runOps_halted rom _ state).trans ha) preparedRegs
    (init_inv rom base length state hbase hlen)
  have time : 7 * length + 5 = 3 + (7 * length + 2) := by omega
  rw [time]
  exact RunSafe.add _ _ _ _ _ _ state initSafe (by rw [initRun]; exact rest)

/-- Full finite-word refinement and actual strict-prefix fetch/access.
RunSafe is constructed above, never supplied by the caller. -/
theorem clear_word_prefix {bits : Nat} (rom : PhysicalROM) (B heapWords : Nat)
    (left right : List PackingOp) (base length : Nat) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hone : 1 ≤ B) (hbase : state.register .index = base) (hlen : state.register .total = length)
    (hendB : base + length ≤ B) (hendH : base + length ≤ heapWords)
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B)
    (hB : Fits bits B) (hcode : WordsFit bits (packingCode (left ++ programAt left.length ++ right)))
    (count : Nat) (hc : count ≤ 7 * length + 5) :
    let code := left ++ programAt left.length ++ right
    let actual := packingRun rom code count (state.toWord bits)
    actual = (natRun rom code count state).toWord bits ∧ actual.halted = false ∧
      (count < 7 * length + 5 → ∃ index, ∃ hi : index < code.length,
        actual.pc.toNat = 5 * index ∧ PackingOp.decode (fetch code actual) = some code[index] ∧
          packingAccessFits rom heapWords actual code[index]) := by
  let code := left ++ programAt left.length ++ right
  have safe := clear_safe rom B heapWords left right base length state hpc ha hr hone hbase hlen hendB hendH hpcB
  have hprefix (k : Nat) (hk : k < count) :
      RegistersFit bits (natRun rom code k state) ∧ Fits bits (natRun rom code k state).pc := by
    obtain ⟨regs, _active, index, hi, pc⟩ := safe.1 k (by omega)
    constructor
    · intro reg
      exact (regs reg).trans_lt hB
    · rw [pc]
      exact ((Nat.mul_le_mul_left 5 hi).trans hpcB).trans_lt hB
  have word := natRun_toWord rom code state count hcode hprefix
  refine ⟨word, ?_, ?_⟩
  · rw [word]
    exact (safe.1 count hc).2.1
  · intro strict
    exact PA06A19PrepareControlBank017.safe_word_prefix rom B heapWords code (7 * length + 5) state
      safe hB hpcB hcode count strict

private theorem head_prefix_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 3)) (ha : state.halted = false) (count : Nat) (hc : count ≤ 2) :
    natRun rom (left ++ programAt left.length ++ right) count state =
      runOps rom ((copyHead (5 * (left.length + 10))).take count) state := by
  have hp : (left ++ initializeControls).length = left.length + 3 := by
    simp only [List.length_append, initialize_length]
  have hs := PA17UniformGenerator035l.branch_segment_prefix rom (left ++ initializeControls)
    [.base (.base (.constant .old (5 * (left.length + 10))))]
    (tail (5 * (left.length + 3)) ++ right) (.jumpIfZero .total .old)
    (by simp [NoJump]) state (by rw [hp]; exact hpc) ha count hc
  simpa only [programAt, copyHead, List.append_assoc, List.singleton_append] using hs

private theorem tail_prefix_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 5)) (ha : state.halted = false) (count : Nat) (hc : count ≤ 5) :
    natRun rom (left ++ programAt left.length ++ right) count state =
      runOps rom ((tail (5 * (left.length + 3))).take count) state := by
  let lead := (tail (5 * (left.length + 3))).take 4
  have hp : (left ++ initializeControls ++ copyHead (5 * (left.length + 10))).length = left.length + 5 := by
    simp [initializeControls, copyHead]
  have hs := PA17UniformGenerator035l.branch_segment_prefix rom
    (left ++ initializeControls ++ copyHead (5 * (left.length + 10))) lead right (.jumpIfZero .flag .old)
    (by simp [lead, tail, NoJump]) state (by rw [hp]; exact hpc) ha count hc
  simpa only [programAt, tail, lead, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append] using hs

private theorem init_prefix_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (count : Nat) (hc : count ≤ 3) :
    natRun rom (left ++ programAt left.length ++ right) count state =
      runOps rom (initializeControls.take count) state := by
  have hs := PA17UniformGenerator035l.straight_prefix_run rom left initializeControls
    (copyHead (5 * (left.length + 10)) ++ tail (5 * (left.length + 3)) ++ right)
    (by simp [initializeControls, NoJump]) state hpc ha count hc
  simpa only [programAt, List.append_assoc] using hs

private theorem init_address (rom : PhysicalROM) (state : NatState) (count : Nat) (hc : count ≤ 3) :
    (runOps rom (initializeControls.take count) state).register .address = state.register .address := by
  interval_cases count <;> rfl

private theorem head_address (rom : PhysicalROM) (exit : Nat) (state : NatState) (count : Nat) (hc : count ≤ 2) :
    (runOps rom ((copyHead exit).take count) state).register .address = state.register .address := by
  interval_cases count <;> rfl

private theorem tail_address (rom : PhysicalROM) (entry : Nat) (state : NatState) (count : Nat) (hc : count ≤ 5) :
    (runOps rom ((tail entry).take count) state).register .address = state.register .address := by
  interval_cases count <;> rfl

/-- The hardware address/control-bank register is preserved at EVERY
clock, including transient store/increment/subtraction and true jumps. -/
theorem clear_loop_address (rom : PhysicalROM) (left right : List PackingOp)
    (base moved remaining address : Nat) (original : Nat → Nat) (state : NatState)
    (hi : ClearInv base original moved remaining address state)
    (hpc : state.pc = 5 * (left.length + 3)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 7 * remaining + 2) :
    (natRun rom (left ++ programAt left.length ++ right) count state).register .address = address := by
  induction remaining generalizing moved state count with
  | zero =>
    rw [head_prefix_run rom left right state hpc ha count (by omega)]
    exact (head_address rom _ state count (by omega)).trans hi.2.2.2.2.2.1
  | succ remaining ih =>
    by_cases hfirst : count ≤ 2
    · rw [head_prefix_run rom left right state hpc ha count hfirst]
      exact (head_address rom _ state count hfirst).trans hi.2.2.2.2.2.1
    · let tested := runOps rom (copyHead (5 * (left.length + 10))) state
      have testedInv := head_inv rom (5 * (left.length + 10)) base moved (remaining + 1) address original state hi
      have testedPC : tested.pc = 5 * (left.length + 5) := by
        rw [copy_head_pc, hi.2.1, ite_eq_right (by omega), hpc]
        omega
      have testedActive : tested.halted = false := (runOps_halted rom _ state).trans ha
      by_cases hsecond : count - 2 ≤ 5
      · have clock : count = 2 + (count - 2) := by omega
        rw [clock, natRun_add, head_run rom left right state hpc ha,
          tail_prefix_run rom left right tested testedPC testedActive (count - 2) hsecond]
        exact (tail_address rom _ tested (count - 2) hsecond).trans testedInv.2.2.2.2.2.1
      · let nextState := runOps rom (tail (5 * (left.length + 3))) tested
        have nextInv := tail_inv rom (5 * (left.length + 3)) base moved (remaining + 1) address original tested testedInv (by omega)
        have rest := ih (moved + 1) nextState (by simpa only [Nat.add_sub_cancel] using nextInv.1)
          nextInv.2.1 (nextInv.2.2.trans testedActive) (count - 7) (by omega)
        have clock : count = 2 + (5 + (count - 7)) := by omega
        rw [clock, natRun_add, head_run rom left right state hpc ha,
          natRun_add, tail_run rom left right tested testedPC testedActive]
        exact rest

theorem clear_address (rom : PhysicalROM) (left right : List PackingOp) (base length : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hbase : state.register .index = base) (hlen : state.register .total = length)
    (count : Nat) (hc : count ≤ 7 * length + 5) :
    (natRun rom (left ++ programAt left.length ++ right) count state).register .address = state.register .address := by
  by_cases hfirst : count ≤ 3
  · rw [init_prefix_run rom left right state hpc ha count hfirst]
    exact init_address rom state count hfirst
  · let prepared := runOps rom initializeControls state
    have preparedInv := init_inv rom base length state hbase hlen
    have preparedPC : prepared.pc = 5 * (left.length + 3) := by
      simp [prepared, initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute, hpc]
      omega
    have preparedActive : prepared.halted = false := (runOps_halted rom _ state).trans ha
    have rest := clear_loop_address rom left right base 0 length (state.register .address) state.heap prepared
      preparedInv preparedPC preparedActive (count - 3) (by omega)
    have clock : count = 3 + (count - 3) := by omega
    rw [clock, natRun_add, init_run rom left right state hpc ha]
    exact rest

/-- Maximal physical word value: all incoming machine registers qualify.
There is no hidden fit16/small-register precondition. -/
def wordMax (bits : Nat) : Nat := 2 ^ bits - 1

theorem clear_word_fullwidth {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (left right : List PackingOp) (base length : Nat) (before : WordState bits)
    (hone : Fits bits 1) (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbase : (before.register .index).toNat = base) (hlen : (before.register .total).toNat = length)
    (hend : Fits bits (base + length)) (hroom : base + length ≤ heapWords)
    (hpcCode : Fits bits (5 * (left ++ programAt left.length ++ right).length))
    (hcode : WordsFit bits (packingCode (left ++ programAt left.length ++ right)))
    (count : Nat) (hc : count ≤ 7 * length + 5) :
    let code := left ++ programAt left.length ++ right
    let natural := PA06A19PrepareNodeBit015.wordView before
    let actual := packingRun rom code count before
    actual = (natRun rom code count natural).toWord bits ∧ actual.halted = false ∧
      actual.register .address = before.register .address ∧
      (count < 7 * length + 5 → ∃ index, ∃ hi : index < code.length,
        actual.pc.toNat = 5 * index ∧ PackingOp.decode (fetch code actual) = some code[index] ∧
          packingAccessFits rom heapWords actual code[index]) := by
  let B := wordMax bits
  let natural := PA06A19PrepareNodeBit015.wordView before
  have hp : 0 < 2 ^ bits := by positivity
  have hB : Fits bits B := by dsimp [B, wordMax, Fits]; omega
  have hOne : 1 ≤ B := by dsimp [B, wordMax]; dsimp [Fits] at hone; omega
  have endB : base + length ≤ B := by dsimp [B, wordMax]; dsimp [Fits] at hend; omega
  have pcB : 5 * (left ++ programAt left.length ++ right).length ≤ B := by
    dsimp [B, wordMax]
    dsimp [Fits] at hpcCode
    omega
  have registers : RegistersLE B natural := by
    intro reg
    have bound := (before.register reg).isLt
    change (before.register reg).toNat ≤ B
    dsimp [B, wordMax]
    omega
  have out := clear_word_prefix rom B heapWords left right base length natural hpc ha registers hOne hbase hlen
    endB hroom pcB hB hcode count hc
  rw [PA06A19PrepareNodeBit015.wordView_toWord before] at out
  dsimp only at out ⊢
  refine ⟨out.1, out.2.1, ?_, out.2.2⟩
  rw [out.1]
  change BitVec.ofNat bits ((natRun rom _ count natural).register .address) = before.register .address
  rw [clear_address rom left right base length natural hpc ha hbase hlen count hc]
  simp only [natural, PA06A19PrepareNodeBit015.wordView, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025Safety
