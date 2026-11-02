module

public import Structure.PA17_A19QueryBridge_RuntimeTests_010h
public import Structure.PA17_A19QueryBridge_RuntimeTests_010l

/-! Actual reverse-loop control primitives. The budget and all-loop exit
theorems are not asserted in this component. No body-transition or caller
prefix-safety oracle is an assumption: literal fetches are certified below. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def beforeNodeTest (origin : Nat) : List PackingOp :=
  setup ++ counterTest 8 (5 * (origin + 355)) ++ budgetInit

theorem beforeNodeTest_length (origin : Nat) : (beforeNodeTest origin).length = 98 := by
  simp only [beforeNodeTest, List.length_append, setup_length, counterTest_length, budgetInit_length]

theorem nodeTest_partition (origin : Nat) : programAt origin = beforeNodeTest origin ++
    counterTest 9 (5 * (origin + 196)) ++ (nodeBody origin ++ afterNode origin) := by
  simpa only [beforeNode, beforeNodeTest, List.append_assoc] using node_partition origin

theorem actual_nodeTest_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 98))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 5) :
    packingRun rom containing count state =
      executeOps rom ((counterTest 9 (5 * (origin + 196))).take count) state := by
  exact actual_branch_phase_prefix em rom (beforeNodeTest origin)
    (counterLead 9 (5 * (origin + 196))) (nodeBody origin ++ afterNode origin)
    (.jumpIfZero .total .old) (nodeTest_partition origin) (counterLead_straight _ _) state
    (by simpa only [beforeNodeTest_length] using hp) ha count
    (by simpa only [counterLead_length] using hc)

theorem actual_nodeTest {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header remaining : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 98))) (ha : state.halted = false)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hr : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits remaining)
    (hf : Fits bits remaining) :
    let after := packingRun rom containing 5 state
    after.register .total = BitVec.ofNat bits remaining ∧ after.register .address = BitVec.ofNat bits header ∧
      after.heap = state.heap ∧
      after.pc = BitVec.ofNat bits (5 * (origin + if remaining = 0 then 196 else 103)) ∧
      after.halted = false := by
  have hrun := actual_nodeTest_prefix em rom state hp ha 5 (by decide)
  rw [List.take_of_length_le (by rw [counterTest_length])] at hrun
  have ht := execute_counterTest rom 9 (5 * (origin + 196)) header remaining state hh hr hf
  dsimp only
  rw [hrun]
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, (executeOps_halted _ _ _).trans ha⟩
  rw [ht.2.2.2]
  by_cases hz : remaining = 0
  · simp only [hz, ite_true]
  · simp only [hz, ite_false, hp, BitVec.ofNat_add_ofNat]
    congr 1

theorem nodeBody_as_kernel (origin : Nat) : nodeBody origin = nodeKernel ++ back (5 * (origin + 98)) := by
  simp only [nodeBody, nodeBodyLead, nodeKernel, back, List.append_assoc]

theorem actual_nodeBody_end {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 103))) (ha : state.halted = false) :
    let after := packingRun rom containing 93 state
    after.heap = (executeOps rom nodeKernel state).heap ∧
      after.register .address = (executeOps rom nodeKernel state).register .address ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 98)) ∧ after.halted = false := by
  have hrun := actual_node_prefix em rom state hp ha 93 (by decide)
  rw [List.take_of_length_le (by rw [nodeBody_length]), nodeBody_as_kernel, executeOps_append] at hrun
  have hb := execute_back rom (5 * (origin + 98)) (executeOps rom nodeKernel state)
  dsimp only
  rw [hrun]
  exact ⟨hb.2.1, hb.2.2, hb.1, (executeOps_halted _ _ _).trans ((executeOps_halted _ _ _).trans ha)⟩

def wordMask {bits : Nat} (test : Bool) (value : BitVec bits) : BitVec bits := if test then value else BitVec.ofNat bits 0

theorem wordMask_and {bits : Nat} (left right : Bool) (value : BitVec bits) :
    wordMask right (wordMask left value) = wordMask (left && right) value := by
  cases left <;> cases right <;> rfl

theorem wordMask_bit {bits : Nat} (left right : Bool) :
    wordMask right (BitVec.ofNat bits (bit left)) = BitVec.ofNat bits (bit (left && right)) := by
  cases left <;> cases right <;> rfl

theorem acceptPrefix_congr (old fresh : Nat → Nat) (entryBase countsBase remaining : Nat)
    (hf : ∀ node < remaining, fresh (countsBase + node) = old (countsBase + node) ∧
      fresh (entryBase + 1 + node) = old (entryBase + 1 + node)) :
    acceptPrefix fresh entryBase countsBase remaining = acceptPrefix old entryBase countsBase remaining := by
  apply Bool.eq_iff_iff.mpr
  simp only [acceptPrefix, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h node hn
    rw [← (hf node hn).1, ← (hf node hn).2]
    exact h node hn
  · intro h node hn
    rw [(hf node hn).1, (hf node hn).2]
    exact h node hn

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
