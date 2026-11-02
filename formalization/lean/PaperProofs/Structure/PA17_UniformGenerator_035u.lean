module

public import PaperProofs.Structure.PA17_UniformGenerator_035m
public import PaperProofs.Structure.PA17_UniformGenerator_035i

/-! Local actual-prefix numeric safety of the real divide/count prelude.
All three blocks touch only hardware registers. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035u

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035h PA17UniformGenerator035i
  PA17UniformGenerator035j PA17UniformGenerator035m

theorem logInit_numeric (rom : PhysicalROM) (B heapWords : Nat) (htwo : 2 ≤ B)
    (state : NatState) (hr : RegistersLE B state) : NumericSafe B heapWords rom logInit state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 4 at hn
    interval_cases count <;> cases register <;>
      simp [logInit, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 4 at hn
    interval_cases count <;> trivial

theorem logHead_numeric (rom : PhysicalROM) (B heapWords exit : Nat) (he : exit ≤ B)
    (state : NatState) (hr : RegistersLE B state) : NumericSafe B heapWords rom (logHead exit) state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 2 at hn
    interval_cases count <;> cases register <;>
      simp [logHead, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 2 at hn
    interval_cases count <;> trivial

theorem logTail_numeric (rom : PhysicalROM) (B heapWords entry : Nat) (he : entry ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (hadd : state.register .index + state.register .total ≤ B) :
    NumericSafe B heapWords rom (logTail entry) state := by
  have hdiv := (Nat.div_le_self (state.register .value) (state.register .fresh)).trans (hr .value)
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 4 at hn
    interval_cases count <;> cases register <;>
      simp [logTail, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 4 at hn
    interval_cases count <;> trivial

theorem storeLog_numeric (rom : PhysicalROM) (B heapWords target scale : Nat)
    (ht : target ≤ B) (hta : target < heapWords) (hs : scale ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hv : scale * state.register .index ≤ B) :
    NumericSafe B heapWords rom (storeLog target scale) state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 4 at hn
    interval_cases count <;> cases register <;>
      simp [storeLog, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 4 at hn
    interval_cases count <;>
      simp [storeLog, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hta]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035u
