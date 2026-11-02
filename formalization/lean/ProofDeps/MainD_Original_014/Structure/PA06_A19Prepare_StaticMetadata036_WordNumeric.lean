module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordQuery

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual ISA-prefix numeric/access proofs of shared metadata scalar
blocks. Full-width incoming register bounds are preserved. Layout/data
premises below are local numeric facts, later supplied by the real same8192
factory and loop invariants; no original-caller all-run oracle is introduced. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (preparedSize mass highCacheEnd)

def FieldIndex (N q t : Nat) : Field → Nat → Prop
  | .cardinality, index | .internal, index | .leaf, index => index < t
  | .stage, index => index < N
  | .tool, index => index < q

def storeFieldCount : Field → Nat
  | .tool => 17 | _ => 13

theorem storeField_count (field : Field) : (storeField field).length = storeFieldCount field := by cases field <;> rfl

theorem fieldAddress_lt_control (N q t P : Nat) (field : Field) (index : Nat) (hi : FieldIndex N q t field index) :
    fieldAddress P N t field index < 4 + P + 4096 * (N + q + 1 + t) := by
  cases field <;> simp only [FieldIndex, fieldAddress, fieldFactor, fieldExtra] at * <;> omega

/-- Real12/16-op pointer arithmetic and final ordinary store. All five
field classes use the actual permanent base/t/N reads from the same CB. -/
theorem storeField_numeric (rom : PhysicalROM) (B H CB P N q t index : Nat) (field : Field) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hbase : state.heap (CB + 6) = 4 + P) (ht : state.heap (CB + 2) = t)
    (hN : state.heap (CB + 0) = N) (hi : state.register .old = index)
    (hindex : FieldIndex N q t field index) (hlayout : CB = 4 + P + 4096 * (N + q + 1 + t))
    (hroom : CB + 6 < H) (hH : H ≤ B) : NumericSafe B H rom (storeField field) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    rw [storeField_count] at hc
    cases field <;> dsimp only [storeFieldCount] at hc <;> interval_cases count <;> cases reg <;>
      simp_all [storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, fieldFactor,
        FieldIndex, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    rw [storeField_count] at hc
    cases field <;> dsimp only [storeFieldCount] at hc <;> interval_cases count <;>
      simp_all [storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, fieldFactor,
        FieldIndex, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals omega

/-- Real14-op ord→card getter. Cached values and their range are local
facts from007/017/RawCardData, not precomputed metadata outputs. -/
theorem cardProgram_numeric (rom : PhysicalROM) (B H CB M node candidate value : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap (CB + 528) = M) (hn : state.register .old = node)
    (ho : state.heap (rawOrdAddress CB M node) = candidate) (hv : state.heap (rawCardAddress CB candidate) = value)
    (hnM : node ≤ M) (hcM : candidate ≤ M) (hvM : value ≤ M)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) : NumericSafe B H rom cardProgram state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 14 at hc
    interval_cases count <;> cases reg <;>
      simp_all [cardProgram, rawOrdAddress, rawCardAddress, runOps, natExecuteOp, natArithmetic,
        Op.execute, Instruction.execute, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 14 at hc
    interval_cases count <;>
      simp_all [cardProgram, rawOrdAddress, rawCardAddress, runOps, natExecuteOp, natArithmetic,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
    all_goals unfold highCacheEnd at hroom; omega

theorem internalFlag_numeric (rom : PhysicalROM) (B H : Nat) (state : NatState)
    (hr : RegistersLE B state) (hone : 1 ≤ B) : NumericSafe B H rom internalFlag state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 3 at hc
    interval_cases count <;> cases reg <;>
      simp_all [internalFlag, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 3 at hc
    interval_cases count <;> trivial

/-- Hardware CB is preserved at every true scalar-block prefix. -/
theorem storeField_prefix_address (rom : PhysicalROM) (field : Field) (state : NatState)
    (count : Nat) (hc : count ≤ storeFieldCount field) :
    (runOps rom ((storeField field).take count) state).register .address = state.register .address := by
  cases field <;> dsimp only [storeFieldCount] at hc <;> interval_cases count <;> rfl

theorem cardProgram_prefix_address (rom : PhysicalROM) (state : NatState) (count : Nat) (hc : count ≤ 14) :
    (runOps rom (cardProgram.take count) state).register .address = state.register .address := by
  interval_cases count <;> rfl

/-- Actual22-op ordinary-output initializer. The header write is belowCB;
the subsequent true rawM read atCB528 is therefore protected. -/
theorem initializeAdjacency_numeric (rom : PhysicalROM) (B H CB P M t : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap (CB + 528) = M) (ht : state.heap (CB + 2) = t)
    (hbase : state.heap (CB + 6) = 4 + P)
    (htM : t ≤ M) (hlayout : CB = 4 + P + 4096 * (M + t))
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) : NumericSafe B H rom initializeAdjacency state := by
  have hstore : CB + 528 ≠ 4 + P + 2 := by omega
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 22 at hc
    interval_cases count <;> cases reg <;>
      simp_all [initializeAdjacency, runOps, natExecuteOp, natArithmetic,
        Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 22 at hc
    interval_cases count <;>
      simp_all [initializeAdjacency, runOps, natExecuteOp,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

/-- Actual15-op second-copy setup reads dimensions from the same runtime
bank, never from an uncharged relocated pointer or embedded instance size. -/
theorem setupDegreeChildren_numeric (rom : PhysicalROM) (B H CB M t : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap (CB + 528) = M) (ht : state.heap (CB + 2) = t)
    (htM : t ≤ M) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom setupDegreeChildren state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 15 at hc
    interval_cases count <;> cases reg <;>
      simp_all [setupDegreeChildren, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 15 at hc
    interval_cases count <;>
      simp_all [setupDegreeChildren, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
