module

public import Structure.PA06_A19Prepare_ChildrenCache023_Run
public import Structure.PA06_A19Prepare_ChildrenCache023_WordBounds
public import PaperProofs.Structure.PA17_UniformGenerator_035m

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled numeric/access safety of the actual144 children
producer. Each local proof consumes actual entry data and cell bounds,
not an externally supplied all-clock safety assertion. The full32 caller
register bound can be chosen as2^bits-1, so no Fit16 restriction is added. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m

theorem initialize_numeric (rom : PhysicalROM) (B H CB M t : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap (CB + 528) = M) (ht : state.heap (CB + (M * 4 + 532)) = t)
    (hsize : t ≤ M) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom initializeCache state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 32 at hc
    interval_cases count <;> cases reg <;>
      simp_all [initializeCache, loadRel, storeRel, setRel, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 32 at hc
    interval_cases count <;>
      simp_all [initializeCache, loadRel, storeRel, setRel, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem initializeRow_numeric (rom : PhysicalROM) (B H CB M : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom initializeRow state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 8 at hc
    interval_cases count <;> cases reg <;>
      simp_all [initializeRow, setRel, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 8 at hc
    interval_cases count <;>
      simp_all [initializeRow, setRel, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem boundedTest_numeric (rom : PhysicalROM) (B H CB M t count counter exit : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (ht : state.heap (CB + 70) = t) (hc : state.heap (CB + counter) = count)
    (hcounter : counter ≤ 70) (htM : t ≤ M) (hcM : count ≤ M)
    (hexit : 5 * exit ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (boundedTest counter exit) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 9 at hc
    interval_cases count <;> cases reg <;>
      simp_all [boundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 9 at hc
    interval_cases count <;>
      simp_all [boundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem matchTest_numeric (rom : PhysicalROM) (B H CB M parent child start : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap (CB + 528) = M) (hp : state.heap (CB + 64) = parent)
    (hc : state.heap (CB + 65) = child)
    (hparent : parent ≤ M) (hchild : child ≤ M)
    (hread : state.heap (CB + (533 + M * 4 + child)) ≤ M)
    (hj : 5 * (start + 84) ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (matchTest start) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 23 at hc
    interval_cases count <;> cases reg <;>
      simp_all [matchTest, matchLead, loadParent, loadRel, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 23 at hc
    interval_cases count <;>
      simp_all [matchTest, matchLead, loadParent, loadRel, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem skip_numeric (rom : PhysicalROM) (B H exit : Nat) (state : NatState)
    (hr : RegistersLE B state) (hexit : 5 * exit ≤ B) :
    NumericSafe B H rom (jumpTo exit) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 3 at hc
    interval_cases count <;> cases reg <;> simp_all [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · intro count hc
    change count < 3 at hc
    interval_cases count <;> trivial

theorem matched_numeric (rom : PhysicalROM) (B H CB M t child degree flat : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hp : state.heap (CB + 68) = childrenBase CB M t)
    (hc : state.heap (CB + 65) = child) (hd : state.heap (CB + 69) = degree)
    (hf : state.heap (CB + 66) = flat) (htM : t ≤ M)
    (hcM : child ≤ M) (hdM : degree ≤ M) (hfM : flat < t - 1)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom matched state := by
  have hstore69 : CB + 69 ≠ CB + 533 + 5 * M + t + flat := by omega
  have hstore66 : CB + 66 ≠ CB + 533 + 5 * M + t + flat := by omega
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 27 at hc
    interval_cases count <;> cases reg <;>
      simp_all [matched, writeChild, incrementRel, loadRel, storeRel, childrenBase, degreeBase, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 27 at hc
    interval_cases count <;>
      simp_all [matched, writeChild, incrementRel, loadRel, storeRel, childrenBase, degreeBase, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem innerTail_numeric (rom : PhysicalROM) (B H CB M child start : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hc : state.heap (CB + 65) = child) (hcM : child ≤ M)
    (hj : 5 * (start + 49) ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (innerTail start) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 11 at hc
    interval_cases count <;> cases reg <;>
      simp_all [innerTail, innerLead, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 11 at hc
    interval_cases count <;>
      simp_all [innerTail, innerLead, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem outerTail_numeric (rom : PhysicalROM) (B H CB M parent degree start : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hp : state.heap (CB + 64) = parent) (hd : state.heap (CB + 69) = degree)
    (hptr : state.heap (CB + 67) = degreeBase CB M) (hpM : parent ≤ M) (hdM : degree ≤ M)
    (hj : 5 * (start + 32) ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (outerTail start) state := by
  have hstore64 : CB + 64 ≠ parent + (CB + 533 + 5 * M) := by omega
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 22 at hc
    interval_cases count <;> cases reg <;>
      simp_all [outerTail, outerLead, writeDegree, incrementRel, loadRel, storeRel, degreeBase, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 22 at hc
    interval_cases count <;>
      simp_all [outerTail, outerLead, writeDegree, incrementRel, loadRel, storeRel, degreeBase, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
