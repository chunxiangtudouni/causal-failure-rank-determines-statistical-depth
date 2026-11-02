module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanChunks

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED actual38-op row initialization. Its real zero leaf store
preserves the raw cache, the real card getter supplies control21, and the
real tool initializer supplies control20. No pair card answer is given. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass highCacheEnd loadRel storeRel setRel RunFacts actualControlBase actualAllocation)

private def scanRowZeroHead : List PackingOp :=
  loadRel .old 19 ++ [.base (.base (.constant .value 0))]

private theorem scanRowInitialize_split : scanRowInitialize =
    (((scanRowZeroHead ++ storeField .leaf) ++ cardProgram) ++ storeRel .value 21) ++ setRel 20 0 := rfl

theorem scanRowInitialize_numeric (q : Nat) (full : List (Finset (Fin q))) (B H CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (state : NatState)
    (input : ScanInput q full CB P state) (hnode : state.heap (CB + 19) = node.val)
    (hr : RegistersLE B state)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B) :
    NumericSafe B H (rawIncidenceROM q full) scanRowInitialize state := by
  let rom := rawIncidenceROM q full
  have htM : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have hnB : node.val ≤ B := by unfold highCacheEnd at hroom; omega
  have hCB : state.register .address = CB := input.address
  have headSafe : NumericSafe B H rom scanRowZeroHead state := by
    constructor
    · intro count hc reg
      have hreg := hr reg
      change count ≤ 4 at hc
      interval_cases count <;> cases reg <;>
        simp_all [scanRowZeroHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals unfold highCacheEnd at hroom; omega
    · intro count hc
      change count < 4 at hc
      interval_cases count <;>
        simp_all [scanRowZeroHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
      all_goals unfold highCacheEnd at hroom; omega
  let head := runOps rom scanRowZeroHead state
  have headEffect : head.register .address = CB ∧ head.register .old = node.val ∧ head.heap = state.heap := by
    simp [head, scanRowZeroHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, input.address, hnode]
  have layout : CB = 4 + P + 4096 * (full.length + q + 1 + preparedSize q full) := hlayout
  have controlRoom : CB + 6 < H := by unfold highCacheEnd at hroom; omega
  have storeSafe := storeField_numeric rom B H CB P full.length q (preparedSize q full) node.val .leaf head
    (headSafe.final _ _ _ _ _) headEffect.1 input.base input.nodes input.stages headEffect.2.1
    node.isLt layout controlRoom hH
  let zeroed := runOps rom (storeField .leaf) head
  have zeroEffect := storeField_effect rom CB P full.length (preparedSize q full) node.val .leaf head
    headEffect.1 input.base input.nodes input.stages headEffect.2.1
  have zeroHeap : zeroed.heap = Function.update state.heap
      (fieldAddress P full.length (preparedSize q full) .leaf node.val) (head.register .value) := by
    rw [zeroEffect.2.2.2.2, headEffect.2.2]
  have leafBelow : fieldAddress P full.length (preparedSize q full) .leaf node.val < CB := by
    change 6 + P + 5 * preparedSize q full + node.val < CB
    unfold mass at hlayout
    omega
  have zeroData : RawCardData q full CB zeroed := RawCardData.of_below_write input.raw leafBelow zeroHeap
  obtain ⟨candidate, hord, hsupport⟩ := zeroData.ordered node
  have hcard : zeroed.heap (rawCardAddress CB candidate.val) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node := by
    rw [zeroData.cards candidate, metadata_cardinality]
    exact congrArg Finset.card hsupport
  have cardBound : (prepareNormalization q full).indexed.metadata.cardinalities.get node ≤ mass q full := by
    have small := metadata_cardinality_le_q q (prepareNormalization q full).indexed node
    unfold mass
    omega
  have cardSafe := cardProgram_numeric rom B H CB (mass q full) node.val candidate.val
    ((prepareNormalization q full).indexed.metadata.cardinalities.get node) zeroed
    (storeSafe.final _ _ _ _ _) zeroEffect.1 zeroData.mass_cell zeroEffect.2.1 hord hcard
    (by omega) candidate.isLt.le cardBound hroom hH
  let card := runOps rom cardProgram zeroed
  have cardEffect := cardProgram_original rom q full CB zeroed zeroData node zeroEffect.1 zeroEffect.2.1
  have cardCB : card.register .address = CB := cardEffect.2.1
  have cardRegs : RegistersLE B card := cardSafe.final _ _ _ _ _
  have saveSafe : NumericSafe B H rom (storeRel .value 21) card := by
    constructor
    · intro count hc reg
      have hreg := cardRegs reg
      change count ≤ 3 at hc
      interval_cases count <;> cases reg <;>
        simp_all [storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals unfold highCacheEnd at hroom; omega
    · intro count hc
      change count < 3 at hc
      interval_cases count <;>
        simp_all [storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
      all_goals unfold highCacheEnd at hroom; omega
  let saved := runOps rom (storeRel .value 21) card
  have savedCB : saved.register .address = CB := cardCB
  have savedRegs : RegistersLE B saved := saveSafe.final _ _ _ _ _
  have initializeSafe : NumericSafe B H rom (setRel 20 0) saved := by
    constructor
    · intro count hc reg
      have hreg := savedRegs reg
      change count ≤ 4 at hc
      interval_cases count <;> cases reg <;>
        simp_all [setRel, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals unfold highCacheEnd at hroom; omega
    · intro count hc
      change count < 4 at hc
      interval_cases count <;>
        simp_all [setRel, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
      all_goals unfold highCacheEnd at hroom; omega
  have first := NumericSafe.append B H rom scanRowZeroHead (storeField .leaf) state headSafe storeSafe
  have second := NumericSafe.append B H rom (scanRowZeroHead ++ storeField .leaf) cardProgram state first
    (by rw [runOps_append]; exact cardSafe)
  have third := NumericSafe.append B H rom ((scanRowZeroHead ++ storeField .leaf) ++ cardProgram)
    (storeRel .value 21) state second (by rw [runOps_append, runOps_append]; exact saveSafe)
  rw [scanRowInitialize_split]
  exact NumericSafe.append B H rom (((scanRowZeroHead ++ storeField .leaf) ++ cardProgram) ++ storeRel .value 21)
    (setRel 20 0) state third (by rw [runOps_append, runOps_append, runOps_append]; exact initializeSafe)

theorem scanRowInitialize_runFacts (q : Nat) (full : List (Finset (Fin q))) (B H CB P : Nat)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (node : (prepareNormalization q full).indexed.NodeId) (state : NatState)
    (input : ScanInput q full CB P state) (hnode : state.heap (CB + 19) = node.val)
    (hr : RegistersLE B state)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B)
    (hpc : state.pc = 5 * (start + 13)) (ha : state.halted = false) :
    RunFacts B H (rawIncidenceROM q full) containing 38 state := by
  exact scan_chunk_safe (rawIncidenceROM q full) B H containing start code .rowInitialize state hpc ha
    (scanRowInitialize_numeric q full B H CB P node state input hnode hr hlayout hroom hH)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
