module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Safety_018a
public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015b
public import Structure.PA17_A19QueryBridge_RuntimeTests_Access_017f

/-! Actual fetch/decode/access for setup, counters and the flag-store phases.
The only access premises below are the bounds of the concrete allocated cells. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2200000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010
open PA17A19RuntimeTestsAccess017

theorem counter_phase_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (heapWords header slot target : Nat)
    (before after : List PackingOp)
    (heq : programAt origin = before ++ counterTest slot target ++ after)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + before.length)))
    (ha : state.halted = false) (halloc : header + slot < heapWords)
    (count : Nat) (hc : count < 5) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact branch_phase_safe em rom heapWords before (counterLead slot target) after
    (.jumpIfZero .total .old) heq (counterLead_straight slot target) state hp ha
    (counterTest_access rom slot target header heapWords state hh halloc) count hc

theorem nodeTest_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 98))) (ha : state.halted = false)
    (halloc : header + 9 < heapWords) (count : Nat) (hc : count < 5) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact counter_phase_safe em rom heapWords header 9 (5 * (origin + 196))
    (beforeNodeTest origin) (nodeBody origin ++ afterNode origin) (nodeTest_partition origin)
    state hh (by simpa only [beforeNodeTest_length] using hp) ha halloc count hc

theorem ancestorTest_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 222))) (ha : state.halted = false)
    (halloc : header + 12 < heapWords) (count : Nat) (hc : count < 5) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact counter_phase_safe em rom heapWords header 12 (5 * (origin + 339))
    (beforeAncestorTest origin) (ancestorBody origin ++ budgetFooter origin) (ancestorTest_partition origin)
    state hh (by simpa only [beforeAncestorTest_length] using hp) ha halloc count hc

theorem budgetTest_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 7))) (ha : state.halted = false)
    (halloc : header + 8 < heapWords) (count : Nat) (hc : count < 5) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact counter_phase_safe em rom heapWords header 8 (5 * (origin + 355)) setup
    (budgetInit ++ counterTest 9 (5 * (origin + 196)) ++ nodeBody origin ++ afterNode origin)
    (by simpa only [beforeNodeTest, List.append_assoc] using nodeTest_partition origin)
    state hh (by simpa only [setup_length] using hp) ha halloc count hc

theorem setup_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (halloc : header + 8 < heapWords) (hinput : 1 < rom.input.length)
    (count : Nat) (hc : count < 7) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact straight_phase_safe em rom heapWords [] setup
    (counterTest 8 (5 * (origin + 355)) ++ budgetInit ++ counterTest 9 (5 * (origin + 196)) ++
      nodeBody origin ++ afterNode origin)
    (by simpa only [List.nil_append, beforeNodeTest, List.append_assoc] using nodeTest_partition origin)
    setup_straight state (by simpa only [List.length_nil, Nat.add_zero] using hp) ha
    (setup_access rom header heapWords state hh halloc hinput) count hc

theorem acceptFinish_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header budget heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 196))) (ha : state.halted = false)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (halloc : header + 16 + budget < heapWords) (count : Nat) (hc : count < 26) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact straight_phase_safe em rom heapWords (beforeAcceptFinish origin) acceptFinish
    (counterTest 12 (5 * (origin + 339)) ++ ancestorBody origin ++ budgetFooter origin)
    (by simpa only [beforeAncestor, beforeAcceptFinish, List.append_assoc] using ancestor_partition origin)
    acceptFinish_straight state (by simpa only [beforeAcceptFinish_length] using hp) ha
    (acceptFinish_access rom header budget heapWords state hh hb halloc) count hc

theorem budgetFooter_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header q budget heapWords : Nat)
    (state : WordState bits) (h1 : Fits bits 1) (hinput : 1 < rom.input.length)
    (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 339))) (ha : state.halted = false)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (halloc : header + q + 18 + budget < heapWords) (count : Nat) (hc : count < 16) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact branch_phase_safe em rom heapWords (beforeFooter origin) (budgetFooterLead origin) []
    (.jumpIfZero .fresh .old) (footer_partition origin) (budgetFooterLead_straight origin) state
    (by simpa only [beforeFooter_length] using hp) ha
    (budgetFooter_access rom origin header q budget heapWords state h1 hinput hq hh hb halloc) count hc

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
