module

public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015a
public import Structure.PA17_A19QueryBridge_RuntimeTests_010m

/-! Actual outer control phases of the fixed355-op program. Each equality is
for the original containing run, including the genuine footer back jump. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_budgetTest_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 7))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 5) :
    packingRun rom containing count state =
      executeOps rom ((counterTest 8 (5 * (origin + 355))).take count) state := by
  exact actual_branch_phase_prefix em rom setup (counterLead 8 (5 * (origin + 355)))
    (budgetInit ++ counterTest 9 (5 * (origin + 196)) ++ nodeBody origin ++ afterNode origin)
    (.jumpIfZero .total .old) (by
      simpa only [beforeNodeTest, counterTest, List.append_assoc] using nodeTest_partition origin)
    (counterLead_straight _ _) state (by simpa only [setup_length] using hp) ha count
    (by simpa only [counterLead_length] using hc)

theorem actual_budgetTest {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header remaining : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 7))) (ha : state.halted = false)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hr : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits remaining)
    (hf : Fits bits remaining) :
    let after := packingRun rom containing 5 state
    after.register .total = BitVec.ofNat bits remaining ∧ after.register .address = BitVec.ofNat bits header ∧
      after.heap = state.heap ∧
      after.pc = BitVec.ofNat bits (5 * (origin + if remaining = 0 then 355 else 12)) ∧
      after.halted = false := by
  have hrun := actual_budgetTest_prefix em rom state hp ha 5 (by decide)
  rw [List.take_of_length_le (by rw [counterTest_length])] at hrun
  have ht := execute_counterTest rom 8 (5 * (origin + 355)) header remaining state hh hr hf
  dsimp only
  rw [hrun]
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, (executeOps_halted _ _ _).trans ha⟩
  rw [ht.2.2.2]
  by_cases hz : remaining = 0
  · simp only [hz, ite_true]
  · simp only [hz, ite_false, hp, BitVec.ofNat_add_ofNat]
    congr 1

theorem actual_setup_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 7) :
    packingRun rom containing count state = executeOps rom (setup.take count) state := by
  exact actual_straight_phase_prefix em rom [] setup
    (counterTest 8 (5 * (origin + 355)) ++ budgetInit ++ counterTest 9 (5 * (origin + 196)) ++
      nodeBody origin ++ afterNode origin)
    (by simpa only [List.nil_append, beforeNodeTest, List.append_assoc] using nodeTest_partition origin)
    setup_straight state (by simpa only [List.length_nil, Nat.add_zero] using hp) ha count
    (by simpa only [setup_length] using hc)

theorem actual_setup {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header q : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hq : (rom.words .input).getD 1 0 = q) (hf : Fits bits (q + 2)) :
    let after := packingRun rom containing 7 state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits (q + 2)) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 7)) ∧ after.halted = false := by
  have hrun := actual_setup_prefix em rom state hp ha 7 (by decide)
  rw [List.take_of_length_le (by rw [setup_length])] at hrun
  have hd := execute_setup rom header q state ((show 1 ≤ q + 2 by omega).trans_lt hf) hq hh
  dsimp only
  rw [hrun]
  refine ⟨hd.1, hd.2, ?_, (executeOps_halted _ _ _).trans ha⟩
  rw [executeOps_pc rom setup state setup_straight, hp, setup_length, BitVec.ofNat_add_ofNat]
  congr 1

def beforeBudgetInit (origin : Nat) : List PackingOp := setup ++ counterTest 8 (5 * (origin + 355))

theorem beforeBudgetInit_length (origin : Nat) : (beforeBudgetInit origin).length = 12 := by
  simp only [beforeBudgetInit, List.length_append, setup_length, counterTest_length]

theorem actual_budgetInit_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 12))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 86) :
    packingRun rom containing count state = executeOps rom (budgetInit.take count) state := by
  exact actual_straight_phase_prefix em rom (beforeBudgetInit origin) budgetInit
    (counterTest 9 (5 * (origin + 196)) ++ nodeBody origin ++ afterNode origin)
    (by simpa only [beforeNodeTest, beforeBudgetInit, List.append_assoc] using nodeTest_partition origin)
    budgetInit_straight state (by simpa only [beforeBudgetInit_length] using hp) ha count
    (by simpa only [budgetInit_length] using hc)

theorem actual_budgetInit_end {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 12))) (ha : state.halted = false) :
    let after := packingRun rom containing 86 state
    after = executeOps rom budgetInit state ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 98)) ∧ after.halted = false := by
  have hr := actual_budgetInit_prefix em rom state hp ha 86 (by decide)
  rw [List.take_of_length_le (by rw [budgetInit_length])] at hr
  dsimp only
  refine ⟨hr, ?_, ?_⟩
  · rw [hr, executeOps_pc rom budgetInit state budgetInit_straight, hp, budgetInit_length, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [hr, executeOps_halted]; exact ha

def beforeAcceptFinish (origin : Nat) : List PackingOp := beforeNode origin ++ nodeBody origin

theorem beforeAcceptFinish_length (origin : Nat) : (beforeAcceptFinish origin).length = 196 := by
  simp only [beforeAcceptFinish, List.length_append, beforeNode_length, nodeBody_length]

theorem actual_acceptFinish_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 196))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 26) :
    packingRun rom containing count state = executeOps rom (acceptFinish.take count) state := by
  exact actual_straight_phase_prefix em rom (beforeAcceptFinish origin) acceptFinish
    (counterTest 12 (5 * (origin + 339)) ++ ancestorBody origin ++ budgetFooter origin)
    (by simpa only [beforeAncestor, beforeAcceptFinish, List.append_assoc] using ancestor_partition origin)
    acceptFinish_straight state (by simpa only [beforeAcceptFinish_length] using hp) ha count
    (by simpa only [acceptFinish_length] using hc)

theorem actual_acceptFinish_end {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 196))) (ha : state.halted = false) :
    let after := packingRun rom containing 26 state
    after = executeOps rom acceptFinish state ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 222)) ∧ after.halted = false := by
  have hr := actual_acceptFinish_prefix em rom state hp ha 26 (by decide)
  rw [List.take_of_length_le (by rw [acceptFinish_length])] at hr
  dsimp only
  refine ⟨hr, ?_, ?_⟩
  · rw [hr, executeOps_pc rom acceptFinish state acceptFinish_straight, hp, acceptFinish_length, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [hr, executeOps_halted]; exact ha

theorem budgetFooter_as_finish (origin : Nat) :
    budgetFooter origin = budgetFinish ++ back (5 * (origin + 7)) := by
  simp only [budgetFooter, budgetFooterLead, back, List.append_assoc]

theorem actual_budgetFooter_end {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 339))) (ha : state.halted = false) :
    let after := packingRun rom containing 16 state
    after.heap = (executeOps rom budgetFinish state).heap ∧
      after.register .address = (executeOps rom budgetFinish state).register .address ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 7)) ∧ after.halted = false := by
  have hr := actual_footer_prefix em rom state hp ha 16 (by decide)
  rw [List.take_of_length_le (by rw [budgetFooter_length]), budgetFooter_as_finish, executeOps_append] at hr
  have hb := execute_back rom (5 * (origin + 7)) (executeOps rom budgetFinish state)
  dsimp only
  rw [hr]
  exact ⟨hb.2.1, hb.2.2, hb.1, (executeOps_halted _ _ _).trans ((executeOps_halted _ _ _).trans ha)⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
