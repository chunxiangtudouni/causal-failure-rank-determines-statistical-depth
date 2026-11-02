module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED numeric/access proofs for the actual84-op card/internal loop.
The loaded candidate and card bounds come from real RawCardData. No bound
on arbitrary incoming heap words or future metadata output is assumed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (preparedSize mass highCacheEnd loadRel storeRel setRel incrementRel)

theorem scalarProgram_numeric (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q)))
    (B H CB P : Nat) (scalar : NodeScalar) (state : NatState)
    (data : RawCardData q full CB state) (node : (prepareNormalization q full).indexed.NodeId)
    (hr : RegistersLE B state) (hCB : state.register .address = CB) (hn : state.register .old = node.val)
    (ht : state.heap (CB + 2) = preparedSize q full)
    (hbase : state.heap (CB + 6) = 4 + P) (hN : state.heap (CB + 0) = full.length)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B) :
    NumericSafe B H rom (scalarProgram scalar) state := by
  obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
  have hcard : state.heap (rawCardAddress CB candidate.val) = scalarValue q full node .cardinality := by
    change state.heap (rawCardAddress CB candidate.val) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node
    rw [data.cards candidate, metadata_cardinality]
    exact congrArg Finset.card hsupport
  have hvalue : scalarValue q full node .cardinality ≤ mass q full := by
    have hq := metadata_cardinality_le_q q (prepareNormalization q full).indexed node
    change (prepareNormalization q full).indexed.metadata.cardinalities.get node ≤ mass q full
    unfold mass
    omega
  have htM : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  have hnode : node.val < preparedSize q full := node.isLt
  have cardSafe := cardProgram_numeric rom B H CB (mass q full) node.val candidate.val
    (scalarValue q full node .cardinality) state hr hCB data.mass_cell hn hord hcard
    (by omega) candidate.isLt.le hvalue hroom hH
  let card := runOps rom cardProgram state
  have cardRegs : RegistersLE B card := cardSafe.final _ _ _ _ _
  have effect := cardProgram_original rom q full CB state data node hCB hn
  have cardT : card.heap (CB + 2) = preparedSize q full := by rw [effect.2.2.2.2.2]; exact ht
  have cardBase : card.heap (CB + 6) = 4 + P := by rw [effect.2.2.2.2.2]; exact hbase
  have cardN : card.heap (CB + 0) = full.length := by rw [effect.2.2.2.2.2]; exact hN
  have layout : CB = 4 + P + 4096 * (full.length + q + 1 + preparedSize q full) := hlayout
  have controlRoom : CB + 6 < H := by unfold highCacheEnd at hroom; omega
  cases scalar with
  | cardinality =>
    have stored := storeField_numeric rom B H CB P full.length q (preparedSize q full) node.val
      .cardinality card cardRegs effect.2.1 cardBase cardT cardN effect.2.2.1 node.isLt
      layout controlRoom hH
    simpa only [scalarProgram, scalarTransform, scalarField, List.append_nil] using
      NumericSafe.append B H rom cardProgram (storeField .cardinality) state cardSafe stored
  | internal =>
    have one : 1 ≤ B := by unfold highCacheEnd at hroom; omega
    have flagSafe := internalFlag_numeric rom B H card cardRegs one
    let flagged := runOps rom internalFlag card
    have flagRegs : RegistersLE B flagged := flagSafe.final _ _ _ _ _
    have stored := storeField_numeric rom B H CB P full.length q (preparedSize q full) node.val
      .internal flagged flagRegs effect.2.1 cardBase cardT cardN effect.2.2.1 node.isLt
      layout controlRoom hH
    have later := NumericSafe.append B H rom internalFlag (storeField .internal) card flagSafe stored
    simpa only [scalarProgram, scalarTransform, scalarField, List.append_assoc] using
      NumericSafe.append B H rom cardProgram (internalFlag ++ storeField .internal) state cardSafe later

theorem cardsLoadNode_numeric (rom : PhysicalROM) (B H CB M node : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hnode : state.heap (CB + 19) = node) (hn : node ≤ M)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (loadRel .old 19) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 3 at hc
    interval_cases count <;> cases reg <;>
      simp_all [loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 3 at hc
    interval_cases count <;>
      simp_all [loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem cardsBody_numeric (q : Nat) (full : List (Finset (Fin q))) (B H CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (state : NatState)
    (input : ScanInput q full CB P state) (hnode : state.heap (CB + 19) = node.val)
    (hr : RegistersLE B state)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B) :
    NumericSafe B H (rawIncidenceROM q full) cardsBody state := by
  let rom := rawIncidenceROM q full
  have htM : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have loadSafe := cardsLoadNode_numeric rom B H CB (mass q full) node.val state
    hr input.address hnode (by omega) hroom hH
  let loaded := runOps rom (loadRel .old 19) state
  have loadedOld : loaded.register .old = node.val := by
    simp [loaded, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, input.address, hnode]
  have loadRegs : RegistersLE B loaded := loadSafe.final _ _ _ _ _
  have loadedHeap : loaded.heap = state.heap := rfl
  have loadedRaw : RawCardData q full CB loaded :=
    RawCardData.of_children_frame input.raw (fun _ _ => rfl)
  have firstSafe := scalarProgram_numeric rom q full B H CB P .cardinality loaded loadedRaw node
    loadRegs input.address loadedOld input.nodes input.base input.stages hlayout hroom hH
  let first := runOps rom (scalarProgram .cardinality) loaded
  have firstEffect := scalarProgram_effect rom q full CB P .cardinality loaded loadedRaw node
    input.address loadedOld input.nodes input.base input.stages
  have below := cards_regions_below_control q full CB P hlayout
  have hcard : fieldAddress P full.length (preparedSize q full) .cardinality node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have firstHeap : first.heap = Function.update state.heap
      (fieldAddress P full.length (preparedSize q full) .cardinality node.val)
      ((prepareNormalization q full).indexed.metadata.cardinalities.get node) := by
    simpa only [scalarField, scalarValue, loadedHeap] using firstEffect.2.2.2
  have firstData : RawCardData q full CB first :=
    RawCardData.of_below_write input.raw hcard firstHeap
  have firstT : first.heap (CB + 2) = preparedSize q full := by
    rw [firstHeap, Function.update_of_ne (by omega)]; exact input.nodes
  have firstBase : first.heap (CB + 6) = 4 + P := by
    rw [firstHeap, Function.update_of_ne (by omega)]; exact input.base
  have firstN : first.heap (CB + 0) = full.length := by
    rw [firstHeap, Function.update_of_ne (by omega)]; exact input.stages
  have secondSafe := scalarProgram_numeric rom q full B H CB P .internal first firstData node
    (firstSafe.final _ _ _ _ _) firstEffect.1 firstEffect.2.1 firstT firstBase firstN hlayout hroom hH
  have later := NumericSafe.append B H rom (scalarProgram .cardinality) (scalarProgram .internal)
    loaded firstSafe secondSafe
  simpa only [cardsBody, List.append_assoc] using
    NumericSafe.append B H rom (loadRel .old 19)
      (scalarProgram .cardinality ++ scalarProgram .internal) state loadSafe later

theorem cardsInitialize_numeric (rom : PhysicalROM) (B H CB M : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (setRel 19 0) state := by
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

theorem cardsTest_numeric (rom : PhysicalROM) (B H CB M t node exit : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (ht : state.heap (CB + 2) = t) (hn : state.heap (CB + 19) = node)
    (htM : t ≤ M) (hnM : node ≤ M) (hexit : 5 * exit ≤ B)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (scanBoundedTest 2 19 exit) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 9 at hc
    interval_cases count <;> cases reg <;>
      simp_all [scanBoundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 9 at hc
    interval_cases count <;>
      simp_all [scanBoundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem cardsTail_numeric (rom : PhysicalROM) (B H CB M node start : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hn : state.heap (CB + 19) = node) (hnM : node + 1 ≤ M)
    (hjump : 5 * (start + 4) ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (cardsTail start) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 11 at hc
    interval_cases count <;> cases reg <;>
      simp_all [cardsTail, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 11 at hc
    interval_cases count <;>
      simp_all [cardsTail, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
