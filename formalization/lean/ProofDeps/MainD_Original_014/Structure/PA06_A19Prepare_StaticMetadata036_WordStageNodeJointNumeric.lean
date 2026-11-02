module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageInner
public import Structure.PA06_A19Prepare_StaticMetadata036_StageNode

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED short numeric chunks of the unchanged202 producer. These
lemmas consume only concrete loop cells, never a future stage-map answer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass highCacheEnd loadRel storeRel setRel incrementRel RunFacts)

theorem stageSetRel_numeric (rom : PhysicalROM) (B H CB M offset value : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hoffset : offset ≤ 24) (hvalue : value ≤ B)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (setRel offset value) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 4 at hc
    interval_cases count <;> cases reg <;>
      simp_all [setRel, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 4 at hc
    interval_cases count <;>
      simp_all [setRel, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem stageTail_numeric (rom : PhysicalROM) (B H CB M offset value exit : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hcell : state.heap (CB + offset) = value) (hoffset : offset ≤ 24)
    (hvalue : value + 1 ≤ M) (hjump : 5 * exit ≤ B)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (incrementRel offset ++ jumpTo exit) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 11 at hc
    interval_cases count <;> cases reg <;>
      simp_all [incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 11 at hc
    interval_cases count <;>
      simp_all [incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem stageNodeInitialize_numeric (rom : PhysicalROM) (B H CB M : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom stageNodeInitialize state := by
  have one : 1 ≤ B := by unfold highCacheEnd at hroom; omega
  have first := stageSetRel_numeric rom B H CB M 23 1 state hr hCB (by decide) one hroom hH
  let flagged := runOps rom (setRel 23 1) state
  have flaggedCB : flagged.register .address = CB := hCB
  have second := stageSetRel_numeric rom B H CB M 20 0 flagged
    (first.final _ _ _ _ _) flaggedCB (by decide) (by omega) hroom hH
  exact NumericSafe.append B H rom (setRel 23 1) (setRel 20 0) state first second

theorem stageNodeWriteTest_numeric (rom : PhysicalROM) (B H CB M flag skip : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hflag : state.heap (CB + 23) = flag) (hflagB : flag ≤ B) (hskip : 5 * skip ≤ B)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (stageNodeWriteTest skip) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 5 at hc
    interval_cases count <;> cases reg <;>
      simp_all [stageNodeWriteTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 5 at hc
    interval_cases count <;>
      simp_all [stageNodeWriteTest, loadRel, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

def stageRecordHead : List PackingOp := loadRel .old 22 ++ loadRel .value 19 ++
  [.base (.base (.constant .total 1)), .base (.base (.add .value .value .total))]

theorem stageRecord_numeric (q : Nat) (full : List (Finset (Fin q))) (B H CB P : Nat)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (state : NatState) (input : ScanInput q full CB P state)
    (hs : state.heap (CB + 22) = stage.val) (hn : state.heap (CB + 19) = node.val)
    (hr : RegistersLE B state)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B) :
    NumericSafe B H (rawIncidenceROM q full) stageRecord state := by
  let rom := rawIncidenceROM q full
  have hCB : state.register .address = CB := input.address
  have hstage := stage.isLt
  have hnode : node.val < preparedSize q full := node.isLt
  have htM : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  have hNM : full.length ≤ mass q full := by unfold mass; omega
  have hnB : node.val + 1 ≤ B := by unfold highCacheEnd at hroom; omega
  have headSafe : NumericSafe B H rom stageRecordHead state := by
    constructor
    · intro count hc reg
      have hreg := hr reg
      change count ≤ 8 at hc
      interval_cases count <;> cases reg <;>
        simp_all [stageRecordHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals unfold highCacheEnd at hroom; omega
    · intro count hc
      change count < 8 at hc
      interval_cases count <;>
        simp_all [stageRecordHead, loadRel, runOps, natExecuteOp, Op.execute,
          Instruction.execute, NatAccessFits, AccessFits]
      all_goals unfold highCacheEnd at hroom; omega
  let head := runOps rom stageRecordHead state
  have effect : head.register .address = CB ∧ head.register .old = stage.val ∧ head.heap = state.heap := by
    simp [head, stageRecordHead, loadRel, runOps, natExecuteOp, Op.execute,
      Instruction.execute, hCB, hs]
  have storeSafe := storeField_numeric rom B H CB P full.length q (preparedSize q full)
    stage.val .stage head (headSafe.final _ _ _ _ _) effect.1 input.base input.nodes input.stages
    effect.2.1 stage.isLt hlayout (by unfold highCacheEnd at hroom; omega) hH
  change NumericSafe B H rom (stageRecordHead ++ storeField .stage) state
  exact NumericSafe.append B H rom stageRecordHead (storeField .stage) state headSafe storeSafe

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
