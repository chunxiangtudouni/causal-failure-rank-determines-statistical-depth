module

public import PaperProofs.Structure.PA17_CellLayout_003
public import PaperProofs.Structure.RawTreeSerialization
public import PaperProofs.Structure.PA17_QueryMetadata_010
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual two-row given-tree construction. Only the current and successor
row are allocated, plus one shared work slot/accumulator and one stage-node
word. A stage is matched from original incidences once before its row, never
read from an N-word stage map. Rank/finite-word/packing remain separate. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17Rolling018

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001

def slot (q stage budget : Nat) : Nat := (stage % 2) * (q + 2) + budget
def base (size slot : Nat) : Nat := slot * (size + 1)
def workBase (q size : Nat) : Nat := 2 * (q + 2) * (size + 1)
def accumulatorBase (q size : Nat) : Nat := workBase q size + size + 1
def capacityWords (q size : Nat) : Nat := workBase q size + 2 * (size + 1)
def metadataBase (q size : Nat) : Nat := capacityWords q size
def stageWord (q size : Nat) : Nat := metadataBase q size + 3 * size + 1
def indexWords (size : Nat) : Nat := 3 * size + 2

def saveValue (address : Nat) : List Op :=
  [.base (.constant .index address), .base (.storeHeap .index .value)]

def stageProgram (N q size stage : Nat) : List Op :=
  [.base (.constant .value 0)] ++
    (List.range size).flatMap (PA17StageMap001.nodeBlock N q stage) ++ saveValue (stageWord q size)

def freeSlot (q size slot : Nat) : List Op :=
  (IndexedCellRAM.copyWords (metadataBase q size) (base size slot + 1) size).map Op.base ++
    (IndexedCellRAM.constantBlock (base size slot) 1).map Op.base

def prepareProgram (N q size : Nat) : List Op :=
  UniformTreeMetadataRAM.program N q size (metadataBase q size) ++
    (List.range (2 * (q + 2))).flatMap (freeSlot q size)

def kernelProgram (q size goodSlot : Nat) : List Op :=
  PA17UniformCell002.kernelProgram size (workBase q size) (base size goodSlot)
    (accumulatorBase q size) (metadataBase q size + size) (stageWord q size)

def cellProgram (q size stage budget : Nat) : List Op :=
  toTagLast size (base size (slot q (stage + 1) (budget - 1))) (workBase q size) ++
    kernelProgram q size (slot q (stage + 1) budget) ++
    toTagFirst size (workBase q size) (base size (slot q stage budget))

def positiveBudgets (q : Nat) : List Nat := (List.range (q + 1)).map (fun index => index + 1)

def rowProgram (N q size stage : Nat) : List Op :=
  stageProgram N q size stage ++ (positiveBudgets q).flatMap (cellProgram q size stage)

def scheduleProgram (N q size count : Nat) : List Op :=
  (List.range count).reverse.flatMap (rowProgram N q size)

def buildProgram (N q size : Nat) : List Op :=
  prepareProgram N q size ++ scheduleProgram N q size N

theorem slot_lt (q stage budget : Nat) (hb : budget < q + 2) : slot q stage budget < 2 * (q + 2) := by
  have hm : stage % 2 < 2 := Nat.mod_lt _ (by decide)
  have hh := Nat.mul_le_mul_right (q + 2) (show stage % 2 + 1 ≤ 2 by omega)
  rw [Nat.add_mul, Nat.one_mul] at hh
  unfold slot
  omega

theorem slot_ne (q leftStage rightStage leftBudget rightBudget : Nat)
    (hl : leftBudget < q + 2) (hr : rightBudget < q + 2)
    (hne : leftStage % 2 ≠ rightStage % 2 ∨ leftBudget ≠ rightBudget) :
    slot q leftStage leftBudget ≠ slot q rightStage rightBudget := by
  unfold slot
  by_cases hs : leftStage % 2 = rightStage % 2
  · rw [hs]
    exact fun he => (hne.resolve_left (not_not.mpr hs)) (Nat.add_left_cancel he)
  · intro he
    have hlmul := Nat.mul_le_mul_right (q + 2)
      (show min (leftStage % 2) (rightStage % 2) + 1 ≤ max (leftStage % 2) (rightStage % 2) by omega)
    rcases lt_or_gt_of_ne hs with hs | hs
    · rw [min_eq_left hs.le, max_eq_right hs.le, Nat.add_mul, Nat.one_mul] at hlmul
      omega
    · rw [min_eq_right hs.le, max_eq_left hs.le, Nat.add_mul, Nat.one_mul] at hlmul
      omega

theorem next_parity_ne (stage : Nat) : (stage + 1) % 2 ≠ stage % 2 := by omega

theorem slot_word_lt_work (q size slot : Nat) (hs : slot < 2 * (q + 2))
    (index : Nat) (hi : index ≤ size) : base size slot + index < workBase q size := by
  have hh := Nat.mul_le_mul_right (size + 1) (show slot + 1 ≤ 2 * (q + 2) by omega)
  rw [Nat.add_mul, Nat.one_mul] at hh
  unfold base workBase
  omega

theorem work_slot_disjoint (q size slot : Nat) (hs : slot < 2 * (q + 2)) :
    DisjointSlots size (workBase q size) (base size slot) := by
  intro left _ right hr
  have hb := slot_word_lt_work q size slot hs right hr
  omega

theorem slots_disjoint (size left right : Nat) (hne : left ≠ right) :
    DisjointSlots size (base size left) (base size right) := by
  intro li hli ri hri
  rcases lt_or_gt_of_ne hne with h | h
  · have hm := Nat.mul_le_mul_right (size + 1) (show left + 1 ≤ right by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    unfold base
    omega
  · have hm := Nat.mul_le_mul_right (size + 1) (show right + 1 ≤ left by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    unfold base
    omega

theorem work_acc_disjoint (q size : Nat) :
    DisjointSlots size (workBase q size) (accumulatorBase q size) := by
  intro left hl right _
  unfold accumulatorBase
  omega

theorem slot_acc_disjoint (q size slot : Nat) (hs : slot < 2 * (q + 2)) :
    DisjointSlots size (base size slot) (accumulatorBase q size) := by
  intro left hl right _
  have hh := slot_word_lt_work q size slot hs left hl
  unfold accumulatorBase
  omega

theorem work_parent_disjoint (q size index : Nat) (hi : index < size)
    (encoded : Nat) (_he : encoded ≤ size) :
    workBase q size + index ≠ metadataBase q size + size + encoded := by
  unfold metadataBase capacityWords
  omega

def InternalOnly : Op → Prop
  | .base (.loadROM region _ _) => region = .internal
  | _ => True

theorem internalOnly_execute (left right : ROM)
    (hrom : ∀ address, left.read .internal address = right.read .internal address)
    (op : Op) (hi : InternalOnly op) (state : State) : op.execute left state = op.execute right state := by
  cases op with
  | subtract target l r => rfl
  | base instruction =>
    cases instruction with
    | loadROM region target pointer =>
      subst region
      simp only [Op.execute, Instruction.execute, hrom]
    | constant target value => rfl
    | add target l r => rfl
    | minimum target l r => rfl
    | select target condition yes no => rfl
    | loadHeap target pointer => rfl
    | storeHeap pointer source => rfl

theorem execute_same_internal (left right : ROM)
    (hrom : ∀ address, left.read .internal address = right.read .internal address)
    (code : List Op) (hi : ∀ op ∈ code, InternalOnly op) (state : State) :
    execute left code state = execute right code state := by
  induction code generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [IndexedClosureRAM.execute, IndexedClosureRAM.execute,
      internalOnly_execute left right hrom head (hi head List.mem_cons_self) state]
    exact ih (fun op ho => hi op (List.mem_cons_of_mem _ ho)) _

theorem kernel_internalOnly (q size goodSlot : Nat) :
    ∀ op ∈ kernelProgram q size goodSlot, InternalOnly op := by
  intro op ho
  cases op with
  | subtract target left right => trivial
  | base instruction =>
    cases instruction <;> try trivial
    rename_i region target pointer
    cases region <;> first
      | rfl
      | simp [kernelProgram, PA17UniformCell002.kernelProgram, PA17HeapAncestors001.extensionProgram,
          PA17HeapAncestors001.extensionInit, PA17HeapAncestors001.extensionTail,
          PA17HeapAncestors001.ancestorLoop, PA17HeapAncestors001.ancestorBlock,
          PA17UniformCell002.intersectionProgram, PA17UniformCell002.minimumPass, PA17UniformCell002.minimumBlock,
          UniformNormalizationRAM.program, UniformNormalizationRAM.clearWords, UniformNormalizationRAM.clearBlock,
          UniformNormalizationRAM.nodeBlock, UniformNormalizationRAM.updateNode, UniformNormalizationRAM.pushParent,
          PA17UniformCell002.tagTail] at ho

theorem saveValue_heap (rom : ROM) (address : Nat) (state : State) :
    (execute rom (saveValue address) state).heap = Function.update state.heap address (state.register .value) := rfl

theorem stageProgram_heap (rom : ROM) (N q size stage : Nat) (state : State) :
    (execute rom (stageProgram N q size stage) state).heap =
      Function.update state.heap (stageWord q size)
        ((execute rom ((List.range size).flatMap (PA17StageMap001.nodeBlock N q stage))
          (execute rom [.base (.constant .value 0)] state)).register .value) := by
  rw [stageProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    saveValue_heap, PA17StageMap001.nodes_heap]
  rfl

theorem queryROM_mismatch (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) :
    PA17StageMap001.mismatch (queryROM q full 0 used).semantic full.length q stage.val node.val =
      PA17StageMap001.mismatch (givenTreeROM q full).semantic full.length q stage.val node.val := by
  unfold PA17StageMap001.mismatch
  congr 1
  apply List.map_congr_left
  intro tool ht
  have htq := List.mem_range.mp ht
  unfold PA17StageMap001.difference
  rw [PA17QueryCounts008.queryROM_tree_input_read q full 0 used _ (by
      rw [PA17QueryCounts008.givenTreeROM_input_length]
      have hh := Nat.mul_le_mul_right q (Nat.succ_le_of_lt stage.isLt)
      rw [Nat.succ_mul] at hh
      omega),
    PA17QueryCounts008.queryROM_tree_input_read q full 0 used _ (by
      rw [PA17QueryCounts008.givenTreeROM_input_length]
      have hh := Nat.mul_le_mul_right q (Nat.succ_le_of_lt node.isLt)
      rw [Nat.succ_mul] at hh
      omega)]

theorem prepared_stageProgram (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (used : Finset (Fin q)) (stage : Fin full.length) (state : State) :
    let cache := (prepareNormalization q full).indexed
    (execute (queryROM q full 0 used).semantic
      (stageProgram full.length q cache.nodes.size stage.val) state).heap (stageWord q cache.nodes.size) =
        encodedNode cache (IndexedQuery.storedStageNode q full hq stage) := by
  intro cache
  rw [stageProgram_heap, Function.update_self]
  let start := execute (queryROM q full 0 used).semantic [.base (.constant .value 0)] state
  change (IndexedClosureRAM.execute _ _ start).register .value = _
  cases hs : IndexedQuery.storedStageNode q full hq stage with
  | none =>
    have hempty : full[stage.val] = ∅ :=
      (IndexedStaticMetadata.buildPositive_stage_none_iff q full hq stage).mp hs
    have hn : ∀ node ∈ List.range cache.nodes.size,
        PA17StageMap001.mismatch (queryROM q full 0 used).semantic full.length q stage.val node ≠ 0 := by
      intro node hm hz
      rw [queryROM_mismatch q full used stage ⟨node, List.mem_range.mp hm⟩] at hz
      have heq := (PA17StageMap001.prepared_mismatch_eq_zero_iff q full stage ⟨node, List.mem_range.mp hm⟩).mp hz
      let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
      have hne := nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full ⟨node, List.mem_range.mp hm⟩)
      rw [heq, hempty] at hne
      exact Finset.not_nonempty_empty hne
    rw [PA17StageMap001.nodes_value_none _ _ _ _ _ hn]
    rfl
  | some target =>
    have ht : cache.decode target = full[stage.val] :=
      ((IndexedStaticMetadata.buildPositive_stage_some_iff q full hq stage target).mp hs).2
    have hz := (PA17StageMap001.prepared_mismatch_eq_zero_iff q full stage target).mpr ht
    have hzq : PA17StageMap001.mismatch (queryROM q full 0 used).semantic full.length q stage.val target.val = 0 := by
      rw [queryROM_mismatch q full used stage target]
      exact hz
    rw [PA17StageMap001.nodes_value_some _ _ _ _ _ target.val (List.mem_range.mpr target.isLt) hzq (by
      intro node hm hn
      rw [queryROM_mismatch q full used stage ⟨node, List.mem_range.mp hm⟩] at hn
      have heq := (PA17StageMap001.prepared_mismatch_eq_zero_iff q full stage ⟨node, List.mem_range.mp hm⟩).mp hn
      exact congrArg Fin.val (prepared_indexed_decode_injective q full (heq.trans ht.symm)))]
    rfl

theorem tagFirst_transfer {Tool : Type*} (cache : IndexedNodeCache Tool) (old fresh : Nat → Nat)
    (address : Nat) (entry : IndexedEntry.FixedEntry cache) (hr : TagFirstRep cache old address entry)
    (hf : ∀ index ≤ cache.nodes.size, fresh (address + index) = old (address + index)) :
    TagFirstRep cache fresh address entry := by
  cases entry with
  | void =>
    change fresh address = 0
    rw [show fresh address = old address from by simpa only [Nat.add_zero] using hf 0 (Nat.zero_le _)]
    exact hr
  | vector capacity =>
    constructor
    · rw [show fresh address = old address from by simpa only [Nat.add_zero] using hf 0 (Nat.zero_le _)]
      exact hr.1
    · intro node
      rw [show fresh (address + 1 + node.val) = old (address + 1 + node.val) from by
        simpa only [Nat.add_assoc] using hf (1 + node.val) (by have := node.isLt; omega)]
      exact hr.2 node

theorem metadata_transfer (q : Nat) (full : List (Finset (Fin q))) (address : Nat)
    (old fresh : Nat → Nat) (hm : UniformTreeMetadataRAM.MetadataCorrect q full address old)
    (hf : ∀ index, address ≤ index → index < address + 3 * (prepareNormalization q full).indexed.nodes.size + 1 →
      fresh index = old index) :
    UniformTreeMetadataRAM.MetadataCorrect q full address fresh := by
  constructor
  · rw [hf _ (by unfold UniformTreeMetadataRAM.parentAddress; omega)
      (by unfold UniformTreeMetadataRAM.parentAddress; omega)]
    exact hm.1
  · intro node
    have hn := node.isLt
    rw [hf _ (by unfold UniformTreeMetadataRAM.cardAddress; omega)
        (by unfold UniformTreeMetadataRAM.cardAddress; omega),
      hf _ (by unfold UniformTreeMetadataRAM.parentAddress; omega)
        (by unfold UniformTreeMetadataRAM.parentAddress; omega),
      hf _ (by unfold UniformTreeMetadataRAM.internalAddress; omega)
        (by unfold UniformTreeMetadataRAM.internalAddress; omega)]
    exact hm.2 node

theorem kernel_queryROM_eq (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (size goodSlot : Nat) (state : State) :
    execute (queryROM q full 0 used).semantic (kernelProgram q size goodSlot) state =
      execute (givenTreeROM q full).semantic (kernelProgram q size goodSlot) state :=
  execute_same_internal (queryROM q full 0 used).semantic (givenTreeROM q full).semantic
    (fun _ => rfl) _ (kernel_internalOnly q size goodSlot) state

theorem kernel_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q))
    (goodSlot : Nat) (stage : Fin full.length) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hs : state.heap (stageWord q (prepareNormalization q full).indexed.nodes.size) =
      encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq stage))
    (address : Nat)
    (hw : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size,
      address ≠ workBase q (prepareNormalization q full).indexed.nodes.size + index)
    (ha : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size,
      address ≠ accumulatorBase q (prepareNormalization q full).indexed.nodes.size + index) :
    (execute (queryROM q full 0 used).semantic
      (kernelProgram q (prepareNormalization q full).indexed.nodes.size goodSlot) state).heap address = state.heap address := by
  rw [kernel_queryROM_eq q full used]
  exact PA17UniformCell002.prepared_kernelProgram_frame q full hq hlaminar _ _ _ _ _
    (work_parent_disjoint q _) stage state hm hs address hw ha

theorem cell_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length) (budget : Nat)
    (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hs : state.heap (stageWord q (prepareNormalization q full).indexed.nodes.size) =
      encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq stage))
    (address : Nat)
    (hout : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size,
      address ≠ base (prepareNormalization q full).indexed.nodes.size (slot q stage.val budget) + index)
    (hregion : address < workBase q (prepareNormalization q full).indexed.nodes.size ∨
      metadataBase q (prepareNormalization q full).indexed.nodes.size ≤ address) :
    (execute (queryROM q full 0 used).semantic
      (cellProgram q (prepareNormalization q full).indexed.nodes.size stage.val budget) state).heap address = state.heap address := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := (queryROM q full 0 used).semantic
  let copied := execute rom
    (toTagLast size (base size (slot q (stage.val + 1) (budget - 1))) (workBase q size)) state
  have hw (index : Nat) (hi : index ≤ size) : address ≠ workBase q size + index := by
    change address < workBase q size ∨ metadataBase q size ≤ address at hregion
    rcases hregion with h | h
    · omega
    · unfold metadataBase capacityWords at h
      omega
  have ha (index : Nat) (hi : index ≤ size) : address ≠ accumulatorBase q size + index := by
    change address < workBase q size ∨ metadataBase q size ≤ address at hregion
    rcases hregion with h | h
    · unfold accumulatorBase; omega
    · dsimp only [metadataBase, capacityWords, accumulatorBase] at h ⊢
      omega
  have hf (index : Nat) (hindex : metadataBase q size ≤ index) : copied.heap index = state.heap index := by
    apply toTagLast_frame
    intro offset ho
    unfold metadataBase capacityWords at hindex
    omega
  have hmc := metadata_transfer q full (metadataBase q size) state.heap copied.heap hm (fun index hi _ => hf index hi)
  have hsc : copied.heap (stageWord q size) = encodedNode (prepareNormalization q full).indexed
      (IndexedQuery.storedStageNode q full hq stage) := by
    rw [hf _ (by unfold stageWord; omega)]
    exact hs
  rw [cellProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    toTagFirst_frame _ _ _ _ _ address hout,
    kernel_frame q full hq hlaminar used _ stage copied hmc hsc address hw ha]
  exact toTagLast_frame rom _ _ _ state address hw

theorem cell_output (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (budget : Nat) (hbgt : budget < q + 2) (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hs : state.heap (stageWord q (prepareNormalization q full).indexed.nodes.size) =
      encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq stage))
    (hg : TagFirstRep (prepareNormalization q full).indexed state.heap
      (base (prepareNormalization q full).indexed.nodes.size (slot q (stage.val + 1) budget)) good)
    (hb : TagFirstRep (prepareNormalization q full).indexed state.heap
      (base (prepareNormalization q full).indexed.nodes.size (slot q (stage.val + 1) (budget - 1))) bad) :
    let cache := (prepareNormalization q full).indexed
    TagFirstRep cache (execute (queryROM q full 0 used).semantic
      (cellProgram q cache.nodes.size stage.val budget) state).heap
      (base cache.nodes.size (slot q stage.val budget)) (IndexedEntry.cell cache full[stage.val] good bad) := by
  intro cache
  let rom := (queryROM q full 0 used).semantic
  let copied := execute rom
    (toTagLast cache.nodes.size (base cache.nodes.size (slot q (stage.val + 1) (budget - 1))) (workBase q cache.nodes.size)) state
  have hgd := work_slot_disjoint q cache.nodes.size (slot q (stage.val + 1) budget) (slot_lt q _ budget hbgt)
  have hbd := work_slot_disjoint q cache.nodes.size (slot q (stage.val + 1) (budget - 1))
    (slot_lt q _ (budget - 1) (by omega))
  have hf (address : Nat) (ha : metadataBase q cache.nodes.size ≤ address) : copied.heap address = state.heap address := by
    apply toTagLast_frame
    intro index hi
    unfold metadataBase capacityWords at ha
    omega
  have hmc := metadata_transfer q full (metadataBase q cache.nodes.size) state.heap copied.heap hm (fun address ha _ => hf address ha)
  have hsc : copied.heap (stageWord q cache.nodes.size) = encodedNode cache (IndexedQuery.storedStageNode q full hq stage) := by
    rw [hf _ (by unfold stageWord; omega)]
    exact hs
  have hgc : TagFirstRep cache copied.heap (base cache.nodes.size (slot q (stage.val + 1) budget)) good := by
    apply tagFirst_transfer cache state.heap copied.heap _ good hg
    intro index hi
    exact toTagLast_frame rom _ _ _ state _ (by intro offset ho; exact (hgd offset ho index hi).symm)
  have hbc : IndexedCellRAM.SlotRep cache copied.heap (workBase q cache.nodes.size) bad :=
    toTagLast_rep cache rom _ _ (fun left hl right hr => (hbd right hr left hl).symm) state bad hb
  have hk := PA17UniformCell002.prepared_kernelProgram_result q full hq hlaminar
    (workBase q cache.nodes.size) (base cache.nodes.size (slot q (stage.val + 1) budget))
    (accumulatorBase q cache.nodes.size) (metadataBase q cache.nodes.size) (stageWord q cache.nodes.size)
    hgd (work_acc_disjoint q _) (slot_acc_disjoint q _ _ (slot_lt q _ budget hbgt))
    (work_parent_disjoint q _) stage good bad copied hmc hsc hgc hbc
  rw [cellProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  apply toTagFirst_rep cache rom _ _ (work_slot_disjoint q _ _ (slot_lt q _ budget hbgt))
  rw [kernel_queryROM_eq q full used]
  exact hk

theorem freeSlot_frame (rom : ROM) (q size slot : Nat) (state : State) (address : Nat)
    (hf : ∀ index ≤ size, address ≠ base size slot + index) :
    (execute rom (freeSlot q size slot) state).heap address = state.heap address := by
  rw [freeSlot, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap,
    Function.update_of_ne (by simpa only [Nat.add_zero] using hf 0 (Nat.zero_le _)),
    IndexedCellRAM.copyWords_frame rom (metadataBase q size) (base size slot + 1) size state address (by
      intro index hi
      simpa only [Nat.add_assoc] using hf (1 + index) (by omega))]

theorem freeSlot_metadata (q : Nat) (full : List (Finset (Fin q)))
    (slot : Nat) (hs : slot < 2 * (q + 2)) (rom : ROM) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size)
      (execute rom (freeSlot q (prepareNormalization q full).indexed.nodes.size slot) state).heap := by
  apply metadata_transfer q full _ state.heap _ hm
  intro address ha _
  apply freeSlot_frame
  intro index hi
  have hh := slot_word_lt_work q (prepareNormalization q full).indexed.nodes.size slot hs index hi
  unfold metadataBase capacityWords at ha
  omega

theorem freeSlot_rep {Tool : Type*} (q : Nat) (cache : IndexedNodeCache Tool) (slot : Nat)
    (hs : slot < 2 * (q + 2)) (rom : ROM) (state : State)
    (hcard : ∀ node : cache.NodeId, state.heap (metadataBase q cache.nodes.size + node.val) = (cache.decode node).card) :
    TagFirstRep cache (execute rom (freeSlot q cache.nodes.size slot) state).heap
      (base cache.nodes.size slot) (IndexedEntry.free cache) := by
  constructor
  · rw [freeSlot, IndexedClosureRAM.execute_append, execute_base,
      IndexedCellRAM.execute_constantBlock_heap, Function.update_self]
  · intro node
    rw [freeSlot, IndexedClosureRAM.execute_append, execute_base, execute_base,
      IndexedCellRAM.execute_constantBlock_heap, Function.update_of_ne (by omega)]
    rw [IndexedCellRAM.copyWords_value rom (metadataBase q cache.nodes.size)
      (base cache.nodes.size slot + 1) cache.nodes.size (by
        intro left hl right hr
        have hh := slot_word_lt_work q cache.nodes.size slot hs (1 + right) (by omega)
        unfold metadataBase capacityWords
        omega) state node.val node.isLt]
    rw [IndexedEntry.reifyCapacity_get]
    exact hcard node

theorem freeSlots_frame (rom : ROM) (q size : Nat) (slots : List Nat) (state : State) (address : Nat)
    (hf : ∀ slot ∈ slots, ∀ index ≤ size, address ≠ base size slot + index) :
    (execute rom (slots.flatMap (freeSlot q size)) state).heap address = state.heap address := by
  induction slots generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (fun slot hs => hf slot (List.mem_cons_of_mem _ hs)), freeSlot_frame rom q size head state address
        (hf head List.mem_cons_self)]

theorem freeSlots_metadata (q : Nat) (full : List (Finset (Fin q))) (slots : List Nat)
    (hs : ∀ slot ∈ slots, slot < 2 * (q + 2)) (rom : ROM) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size)
      (execute rom (slots.flatMap (freeSlot q (prepareNormalization q full).indexed.nodes.size)) state).heap := by
  apply metadata_transfer q full _ state.heap _ hm
  intro address ha _
  apply freeSlots_frame
  intro slot hslot index hi
  have hh := slot_word_lt_work q (prepareNormalization q full).indexed.nodes.size slot (hs slot hslot) index hi
  unfold metadataBase capacityWords at ha
  omega

theorem freeSlots_rep (q : Nat) (full : List (Finset (Fin q))) (slots : List Nat)
    (hslots : ∀ slot ∈ slots, slot < 2 * (q + 2)) (rom : ROM) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (slot : Nat) (hs : slot ∈ slots) :
    let cache := (prepareNormalization q full).indexed
    TagFirstRep cache (execute rom (slots.flatMap (freeSlot q cache.nodes.size)) state).heap
      (base cache.nodes.size slot) (IndexedEntry.free cache) := by
  intro cache
  induction slots generalizing state with
  | nil => cases hs
  | cons head later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    have hh := hslots head List.mem_cons_self
    have hnew := freeSlot_metadata q full head hh rom state hm
    by_cases ht : slot ∈ later
    · exact ih (fun other ho => hslots other (List.mem_cons_of_mem _ ho)) _ hnew ht
    · have heq : slot = head := (List.mem_cons.mp hs).resolve_right ht
      subst slot
      apply tagFirst_transfer cache _ _ _ _ (freeSlot_rep q cache head hh rom state (fun node => (hm.2 node).1))
      intro index hi
      apply freeSlots_frame
      intro other ho j hj
      apply slots_disjoint cache.nodes.size head other (by intro he; exact ht (he ▸ ho)) index hi j hj

theorem prepared_prepare (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (state : State) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (queryROM q full 0 used).semantic (prepareProgram full.length q cache.nodes.size) state
    UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q cache.nodes.size) result.heap ∧
      ∀ slot < 2 * (q + 2), TagFirstRep cache result.heap (base cache.nodes.size slot) (IndexedEntry.free cache) := by
  intro cache result
  let rom := (queryROM q full 0 used).semantic
  let afterMetadata := execute rom (UniformTreeMetadataRAM.program full.length q cache.nodes.size (metadataBase q cache.nodes.size)) state
  have hm := PA17QueryMetadata010.prepared_program_metadata q full hq hlaminar 0 used (metadataBase q cache.nodes.size) state
  have hrun : result = execute rom ((List.range (2 * (q + 2))).flatMap (freeSlot q cache.nodes.size)) afterMetadata := by
    dsimp only [result, prepareProgram, afterMetadata]
    rw [IndexedClosureRAM.execute_append]
  rw [hrun]
  constructor
  · exact freeSlots_metadata q full (List.range (2 * (q + 2))) (fun slot hs => List.mem_range.mp hs) rom afterMetadata hm
  · intro slot hs
    exact freeSlots_rep q full _ (fun other ho => List.mem_range.mp ho) rom afterMetadata hm slot (List.mem_range.mpr hs)

theorem rowsList_step {Tool : Type*} [DecidableEq Tool] (cache : IndexedNodeCache Tool) (maxBudget : Nat)
    (suffix : List (Finset Tool)) (stage : Nat) (hstage : stage < suffix.length) :
    (IndexedTable.rowsList cache maxBudget suffix)[stage]'(by rw [IndexedTable.rowsList_length]; omega) =
      IndexedTable.rowStep cache maxBudget suffix[stage]
        ((IndexedTable.rowsList cache maxBudget suffix)[stage + 1]'(by rw [IndexedTable.rowsList_length]; omega)) := by
  induction suffix generalizing stage with
  | nil => simp only [List.length_nil] at hstage; omega
  | cons eligible later ih =>
    cases stage with
    | zero => rfl
    | succ stage =>
      simpa only [IndexedTable.rowsList, IndexedTable.rows, List.getElem_cons_succ] using
        ih stage (by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hstage)

theorem rowsList_terminal {Tool : Type*} [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (maxBudget : Nat) (suffix : List (Finset Tool)) :
    (IndexedTable.rowsList cache maxBudget suffix)[suffix.length]'(by rw [IndexedTable.rowsList_length]; omega) =
      IndexedTable.terminalRow cache maxBudget := by
  induction suffix with
  | nil => rfl
  | cons eligible later ih =>
    simpa only [IndexedTable.rowsList, IndexedTable.rows, List.length_cons, List.getElem_cons_succ] using ih

theorem rowsList_zero {Tool : Type*} [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (maxBudget : Nat) (suffix : List (Finset Tool)) (stage : Nat) (hs : stage < suffix.length + 1) :
    ((IndexedTable.rowsList cache maxBudget suffix)[stage]'(by rw [IndexedTable.rowsList_length]; exact hs)).get
      ⟨0, by omega⟩ = IndexedEntry.free cache := by
  induction suffix generalizing stage with
  | nil =>
    simp only [List.length_nil] at hs
    have he : stage = 0 := by omega
    subst stage
    exact IndexedTable.terminalRow_get cache maxBudget ⟨0, by omega⟩
  | cons eligible later ih =>
    cases stage with
    | zero =>
      change (IndexedTable.rowStep cache maxBudget eligible (IndexedTable.rows cache maxBudget later).1).get ⟨0, by omega⟩ = _
      rw [IndexedTable.rowStep_get]
      rfl
    | succ stage =>
      simpa only [IndexedTable.rowsList, IndexedTable.rows, List.getElem_cons_succ] using
        ih stage (by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hs)

theorem storedRow_cell (q : Nat) (full : List (Finset (Fin q))) (stage : Fin full.length)
    (budget : Fin (q + 2)) (hb : 0 < budget.val) :
    (IndexedQuery.storedPositiveRow q full ⟨stage.val, by omega⟩).get budget =
      IndexedEntry.cell (prepareNormalization q full).indexed full[stage.val]
        ((IndexedQuery.storedPositiveRow q full ⟨stage.val + 1, by omega⟩).get budget)
        ((IndexedQuery.storedPositiveRow q full ⟨stage.val + 1, by omega⟩).get ⟨budget.val - 1, by omega⟩) := by
  have hh := rowsList_step (prepareNormalization q full).indexed (q + 1) full stage.val stage.isLt
  change IndexedQuery.storedPositiveRow q full ⟨stage.val, by omega⟩ =
    IndexedTable.rowStep (prepareNormalization q full).indexed (q + 1) full[stage.val]
      (IndexedQuery.storedPositiveRow q full ⟨stage.val + 1, by omega⟩) at hh
  rw [hh, IndexedTable.rowStep_get]
  simp only [IndexedEntry.budgetCell, show budget.val ≠ 0 by omega, ite_false]
  rfl

theorem storedRow_terminal (q : Nat) (full : List (Finset (Fin q))) (budget : Fin (q + 2)) :
    (IndexedQuery.storedPositiveRow q full ⟨full.length, by omega⟩).get budget =
      IndexedEntry.free (prepareNormalization q full).indexed := by
  have hh := rowsList_terminal (prepareNormalization q full).indexed (q + 1) full
  change IndexedQuery.storedPositiveRow q full ⟨full.length, by omega⟩ =
    IndexedTable.terminalRow (prepareNormalization q full).indexed (q + 1) at hh
  rw [hh, IndexedTable.terminalRow_get]

theorem storedRow_zero (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) :
    (IndexedQuery.storedPositiveRow q full stage).get ⟨0, by omega⟩ =
      IndexedEntry.free (prepareNormalization q full).indexed := by
  exact rowsList_zero (prepareNormalization q full).indexed (q + 1) full stage.val stage.isLt

def TagsBounded (q : Nat) (full : List (Finset (Fin q))) (state : State) : Prop :=
  ∀ slot < 2 * (q + 2), state.heap (base (prepareNormalization q full).indexed.nodes.size slot) ≤ 1

def ZeroReady (q : Nat) (full : List (Finset (Fin q))) (state : State) : Prop :=
  ∀ stage : Nat, TagFirstRep (prepareNormalization q full).indexed state.heap
    (base (prepareNormalization q full).indexed.nodes.size (slot q stage 0))
    (IndexedEntry.free (prepareNormalization q full).indexed)

def Invariant (q : Nat) (full : List (Finset (Fin q))) (state : State) : Prop :=
  UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap ∧
    TagsBounded q full state ∧ ZeroReady q full state

def StageReady (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin full.length) (state : State) : Prop :=
  state.heap (stageWord q (prepareNormalization q full).indexed.nodes.size) =
    encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq stage)

def CellReady (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1))
    (budget : Fin (q + 2)) (state : State) : Prop :=
  TagFirstRep (prepareNormalization q full).indexed state.heap
    (base (prepareNormalization q full).indexed.nodes.size (slot q stage.val budget.val))
    ((IndexedQuery.storedPositiveRow q full stage).get budget)

def RowReady (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) (state : State) : Prop :=
  ∀ budget : Fin (q + 2), CellReady q full stage budget state

theorem tag_le_one {Tool : Type*} (cache : IndexedNodeCache Tool) (heap : Nat → Nat) (address : Nat)
    (entry : IndexedEntry.FixedEntry cache) (hr : TagFirstRep cache heap address entry) : heap address ≤ 1 := by
  cases entry with
  | void => rw [hr]; exact Nat.zero_le _
  | vector capacity => rw [hr.1]

theorem stageProgram_frame (rom : ROM) (N q size stage : Nat) (state : State) (address : Nat)
    (hne : address ≠ stageWord q size) :
    (execute rom (stageProgram N q size stage) state).heap address = state.heap address := by
  rw [stageProgram_heap, Function.update_of_ne hne]

theorem stageProgram_preserves_invariant (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (stage : Nat) (state : State) (hi : Invariant q full state) :
    Invariant q full (execute (queryROM q full 0 used).semantic
      (stageProgram full.length q (prepareNormalization q full).indexed.nodes.size stage) state) := by
  let size := (prepareNormalization q full).indexed.nodes.size
  have hlow (address : Nat) (ha : address < workBase q size) :
      (execute (queryROM q full 0 used).semantic (stageProgram full.length q size stage) state).heap address = state.heap address := by
    apply stageProgram_frame
    unfold stageWord metadataBase capacityWords
    omega
  constructor
  · apply metadata_transfer q full _ state.heap _ hi.1
    intro address _ ha
    apply stageProgram_frame
    change address < stageWord q size at ha
    change address ≠ stageWord q size
    omega
  · constructor
    · intro index hs
      rw [hlow _ (by simpa only [Nat.add_zero] using slot_word_lt_work q size index hs 0 (Nat.zero_le _))]
      exact hi.2.1 index hs
    · intro other
      apply tagFirst_transfer _ state.heap _ _ _ (hi.2.2 other)
      intro index hs
      exact hlow _ (slot_word_lt_work q size _ (slot_lt q other 0 (by omega)) index hs)

theorem stageProgram_preserves_row (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (stage : Nat) (row : Fin (full.length + 1)) (state : State) (hr : RowReady q full row state) :
    RowReady q full row (execute (queryROM q full 0 used).semantic
      (stageProgram full.length q (prepareNormalization q full).indexed.nodes.size stage) state) := by
  intro budget
  apply tagFirst_transfer _ state.heap _ _ _ (hr budget)
  intro index hi
  apply stageProgram_frame
  have hh := slot_word_lt_work q (prepareNormalization q full).indexed.nodes.size
    (slot q row.val budget.val) (slot_lt q row.val budget.val budget.isLt) index hi
  unfold stageWord metadataBase capacityWords
  omega

theorem cell_preserves_invariant (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (budget : Fin (q + 2)) (hbgt : 0 < budget.val) (state : State)
    (hi : Invariant q full state) (hs : StageReady q full hq stage state)
    (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state) :
    let result := execute (queryROM q full 0 used).semantic (cellProgram q (prepareNormalization q full).indexed.nodes.size stage.val budget.val) state
    Invariant q full result ∧ StageReady q full hq stage result ∧
      RowReady q full ⟨stage.val + 1, by omega⟩ result ∧ CellReady q full ⟨stage.val, by omega⟩ budget result := by
  intro result
  let size := (prepareNormalization q full).indexed.nodes.size
  have hout := cell_output q full hq hlaminar used stage budget.val budget.isLt _ _ state hi.1 hs
    (hnext budget) (hnext ⟨budget.val - 1, by omega⟩)
  have hframe (address : Nat) (houtside : ∀ index ≤ size, address ≠ base size (slot q stage.val budget.val) + index)
      (hregion : address < workBase q size ∨ metadataBase q size ≤ address) : result.heap address = state.heap address :=
    cell_frame q full hq hlaminar used stage budget.val state hi.1 hs address houtside hregion
  have hmetadataFrame (address : Nat) (ha : metadataBase q size ≤ address) : result.heap address = state.heap address := by
    apply hframe address _ (Or.inr ha)
    intro index hi
    have hh := slot_word_lt_work q size _ (slot_lt q stage.val budget.val budget.isLt) index hi
    unfold metadataBase capacityWords at ha
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · exact metadata_transfer q full _ state.heap _ hi.1 (fun address ha _ => hmetadataFrame address ha)
    · constructor
      · intro other ho
        by_cases heq : other = slot q stage.val budget.val
        · subst other
          exact tag_le_one _ _ _ _ hout
        · rw [hframe _ (fun index hi =>
            by simpa only [Nat.add_zero] using slots_disjoint size other _ heq 0 (Nat.zero_le _) index hi)
            (Or.inl (by simpa only [Nat.add_zero] using slot_word_lt_work q size other ho 0 (Nat.zero_le _)))]
          exact hi.2.1 other ho
      · intro other
        apply tagFirst_transfer _ state.heap _ _ _ (hi.2.2 other)
        intro index hindex
        exact hframe _ (fun j hj => slots_disjoint size _ _
          (slot_ne q other stage.val 0 budget.val (by omega) budget.isLt (Or.inr (by omega))) index hindex j hj)
          (Or.inl (slot_word_lt_work q size _ (slot_lt q other 0 (by omega)) index hindex))
  · change result.heap (stageWord q size) = _
    rw [hmetadataFrame (stageWord q size) (by unfold stageWord; omega)]
    exact hs
  · intro otherBudget
    apply tagFirst_transfer _ state.heap _ _ _ (hnext otherBudget)
    intro index hindex
    exact hframe _ (fun j hj => slots_disjoint size _ _
      (slot_ne q (stage.val + 1) stage.val otherBudget.val budget.val otherBudget.isLt budget.isLt
        (Or.inl (next_parity_ne stage.val))) index hindex j hj)
      (Or.inl (slot_word_lt_work q size _ (slot_lt q (stage.val + 1) otherBudget.val otherBudget.isLt) index hindex))
  · unfold CellReady
    rw [storedRow_cell q full stage budget hbgt]
    exact hout

def PreservesCurrent (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1))
    (before after : State) : Prop := ∀ budget, CellReady q full stage budget before → CellReady q full stage budget after

theorem cell_preserves_current (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (budget : Fin (q + 2)) (hbgt : 0 < budget.val) (state : State)
    (hi : Invariant q full state) (hs : StageReady q full hq stage state)
    (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state) :
    PreservesCurrent q full ⟨stage.val, by omega⟩ state
      (execute (queryROM q full 0 used).semantic (cellProgram q (prepareNormalization q full).indexed.nodes.size stage.val budget.val) state) := by
  intro other hc
  by_cases he : other = budget
  · subst other
    exact (cell_preserves_invariant q full hq hlaminar used stage budget hbgt state hi hs hnext).2.2.2
  · apply tagFirst_transfer _ state.heap _ _ _ hc
    intro index hindex
    exact cell_frame q full hq hlaminar used stage budget.val state hi.1 hs _
      (fun j hj => slots_disjoint _ _ _
        (slot_ne q stage.val stage.val other.val budget.val other.isLt budget.isLt
          (Or.inr (fun hv => he (Fin.ext hv)))) index hindex j hj)
      (Or.inl (slot_word_lt_work q _ _ (slot_lt q stage.val other.val other.isLt) index hindex))

theorem positiveBudgets_mem (q budget : Nat) : budget ∈ positiveBudgets q ↔ 0 < budget ∧ budget < q + 2 := by
  constructor
  · intro hm
    obtain ⟨index, hi, rfl⟩ := List.mem_map.mp hm
    have := List.mem_range.mp hi
    omega
  · rintro ⟨hp, hb⟩
    exact List.mem_map.mpr ⟨budget - 1, List.mem_range.mpr (by omega), by omega⟩

theorem budgets_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (budgets : List Nat) (hbudgets : ∀ budget ∈ budgets, 0 < budget ∧ budget < q + 2)
    (state : State) (hi : Invariant q full state) (hs : StageReady q full hq stage state)
    (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state) :
    let result := execute (queryROM q full 0 used).semantic
      (budgets.flatMap (cellProgram q (prepareNormalization q full).indexed.nodes.size stage.val)) state
    Invariant q full result ∧ StageReady q full hq stage result ∧
      RowReady q full ⟨stage.val + 1, by omega⟩ result ∧
      PreservesCurrent q full ⟨stage.val, by omega⟩ state result ∧
      ∀ (budget : Nat) (hb : budget ∈ budgets),
        CellReady q full ⟨stage.val, by omega⟩ ⟨budget, (hbudgets budget hb).2⟩ result := by
  induction budgets generalizing state with
  | nil => exact ⟨hi, hs, hnext, fun _ h => h, by intro budget hb; cases hb⟩
  | cons head later ih =>
    have hb := hbudgets head List.mem_cons_self
    let after := execute (queryROM q full 0 used).semantic
      (cellProgram q (prepareNormalization q full).indexed.nodes.size stage.val head) state
    have hstep := cell_preserves_invariant q full hq hlaminar used stage ⟨head, hb.2⟩ hb.1 state hi hs hnext
    have hp := cell_preserves_current q full hq hlaminar used stage ⟨head, hb.2⟩ hb.1 state hi hs hnext
    have ht := ih (fun budget hm => hbudgets budget (List.mem_cons_of_mem _ hm)) after
      hstep.1 hstep.2.1 hstep.2.2.1
    dsimp only at ht ⊢
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    refine ⟨ht.1, ht.2.1, ht.2.2.1, fun other ho => ht.2.2.2.1 other (hp other ho), ?_⟩
    intro budget hm
    rcases List.mem_cons.mp hm with heq | hm
    · subst budget
      exact ht.2.2.2.1 _ hstep.2.2.2
    · exact ht.2.2.2.2 budget hm

theorem prepared_rowProgram (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (state : State) (hi : Invariant q full state) (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state) :
    let result := execute (queryROM q full 0 used).semantic
      (rowProgram full.length q (prepareNormalization q full).indexed.nodes.size stage.val) state
    Invariant q full result ∧ RowReady q full ⟨stage.val, by omega⟩ result := by
  intro result
  let afterStage := execute (queryROM q full 0 used).semantic
    (stageProgram full.length q (prepareNormalization q full).indexed.nodes.size stage.val) state
  have hs := prepared_stageProgram q full hq used stage state
  have ht := budgets_correct q full hq hlaminar used stage (positiveBudgets q)
    (fun budget hb => (positiveBudgets_mem q budget).mp hb) afterStage
    (stageProgram_preserves_invariant q full used stage.val state hi) hs
    (stageProgram_preserves_row q full used stage.val _ state hnext)
  have heq : result = execute (queryROM q full 0 used).semantic
      ((positiveBudgets q).flatMap (cellProgram q (prepareNormalization q full).indexed.nodes.size stage.val)) afterStage := by
    dsimp only [result, rowProgram, afterStage]
    rw [IndexedClosureRAM.execute_append]
  rw [heq]
  refine ⟨ht.1, ?_⟩
  intro budget
  by_cases hz : budget.val = 0
  · have hbe : budget = (⟨0, by omega⟩ : Fin (q + 2)) := Fin.ext hz
    rw [hbe]
    unfold CellReady
    rw [storedRow_zero]
    exact ht.1.2.2 stage.val
  · exact ht.2.2.2.2 budget.val ((positiveBudgets_mem q budget.val).mpr ⟨by omega, budget.isLt⟩)

theorem scheduleProgram_succ (N q size count : Nat) :
    scheduleProgram N q size (count + 1) = rowProgram N q size count ++ scheduleProgram N q size count := by
  simp only [scheduleProgram, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem prepared_schedule (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (count : Nat) (hc : count ≤ full.length)
    (state : State) (hi : Invariant q full state) (hrow : RowReady q full ⟨count, by omega⟩ state) :
    let result := execute (queryROM q full 0 used).semantic
      (scheduleProgram full.length q (prepareNormalization q full).indexed.nodes.size count) state
    Invariant q full result ∧ RowReady q full ⟨0, by omega⟩ result := by
  induction count generalizing state with
  | zero => exact ⟨hi, hrow⟩
  | succ count ih =>
    have hs : count < full.length := by omega
    have hr := prepared_rowProgram q full hq hlaminar used ⟨count, hs⟩ state hi hrow
    let after := execute (queryROM q full 0 used).semantic
      (rowProgram full.length q (prepareNormalization q full).indexed.nodes.size count) state
    have ht := ih (by omega) after hr.1 hr.2
    dsimp only at ht ⊢
    rw [scheduleProgram_succ, IndexedClosureRAM.execute_append]
    exact ht

/-- Actual two-row execution from the original raw query ROM and zero heap
ends with the original complete row zero in the first q+2 physical slots.
No full table, rank, stage map or local schedule correctness is an input. -/
theorem prepared_build_rowZero (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (queryROM q full 0 used).semantic (buildProgram full.length q cache.nodes.size) (initial (fun _ => 0))
    Invariant q full result ∧
      ∀ budget : Fin (q + 2), readEntry cache.nodes.size budget.val result.heap =
        (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget := by
  intro cache result
  let seed := execute (queryROM q full 0 used).semantic (prepareProgram full.length q cache.nodes.size) (initial (fun _ => 0))
  have hp := prepared_prepare q full hq hlaminar used (initial (fun _ => 0))
  have hi : Invariant q full seed := by
    refine ⟨hp.1, ?_, ?_⟩
    · intro index hs
      exact tag_le_one _ _ _ _ (hp.2 index hs)
    · intro stage
      exact hp.2 _ (slot_lt q stage 0 (by omega))
  have ht : RowReady q full ⟨full.length, by omega⟩ seed := by
    intro budget
    unfold CellReady
    rw [storedRow_terminal]
    exact hp.2 _ (slot_lt q full.length budget.val budget.isLt)
  have hs := prepared_schedule q full hq hlaminar used full.length le_rfl seed hi ht
  have heq : result = execute (queryROM q full 0 used).semantic
      (scheduleProgram full.length q cache.nodes.size full.length) seed := by
    dsimp only [result, buildProgram, seed]
    rw [IndexedClosureRAM.execute_append]
  rw [heq]
  refine ⟨hs.1, ?_⟩
  intro budget
  apply readEntry_eq_of_rep cache budget.val
  simpa only [CellReady, slot, Nat.zero_mod, Nat.zero_mul, Nat.zero_add, base] using hs.2 budget

theorem freeSlot_trace_length (q size slot : Nat) : (trace (freeSlot q size slot)).length = 38 * size + 27 := by
  rw [freeSlot, trace_append, List.length_append, trace_base_length, trace_base_length,
    IndexedCellRAM.copyWords_trace_length]
  rfl

theorem prepareProgram_trace_length (N q size : Nat) :
    (trace (prepareProgram N q size)).length =
      (30 * q + 131) * size + 27 + 2 * (q + 2) * (38 * size + 27) := by
  rw [prepareProgram, trace_append, List.length_append, UniformTreeMetadataRAM.program_trace_length,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [freeSlot_trace_length, List.map_const', List.length_range, List.sum_replicate, Nat.nsmul_eq_mul]

theorem stageProgram_trace_length (N q size stage : Nat) :
    (trace (stageProgram N q size stage)).length = (82 * q + 28) * size + 27 := by
  rw [stageProgram, trace_append, trace_append, List.length_append, List.length_append,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [PA17StageMap001.nodeBlock_trace_length, List.map_const', List.length_range,
    List.sum_replicate, Nat.nsmul_eq_mul]
  change 8 + size * (82 * q + 28) + 19 = _
  ring

theorem cellProgram_trace_length (q size stage budget : Nat) :
    (trace (cellProgram q size stage budget)).length = 462 * size + 248 := by
  rw [cellProgram, trace_append, trace_append, List.length_append, List.length_append,
    toTagLast_trace_length, toTagFirst_trace_length, kernelProgram, PA17UniformCell002.kernelProgram_trace_length]
  ring

theorem rowProgram_trace_length (N q size stage : Nat) :
    (trace (rowProgram N q size stage)).length =
      (82 * q + 28) * size + 27 + (q + 1) * (462 * size + 248) := by
  rw [rowProgram, trace_append, List.length_append, stageProgram_trace_length,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [cellProgram_trace_length, List.map_const', positiveBudgets, List.length_map,
    List.length_range, List.sum_replicate, Nat.nsmul_eq_mul]

theorem scheduleProgram_trace_length (N q size count : Nat) :
    (trace (scheduleProgram N q size count)).length =
      count * ((82 * q + 28) * size + 27 + (q + 1) * (462 * size + 248)) := by
  rw [scheduleProgram, UniformNormalizationRAM.trace_flatMap_length]
  simp only [rowProgram_trace_length, List.map_const', List.length_reverse, List.length_range,
    List.sum_replicate, Nat.nsmul_eq_mul]

theorem prepareProgram_trace_le (N q size : Nat) (hsize : 0 < size) :
    (trace (prepareProgram N q size)).length ≤ 450 * queryWork q size := by
  rw [prepareProgram_trace_length]
  unfold queryWork
  nlinarith

theorem rowProgram_trace_le (N q size stage : Nat) (hsize : 0 < size) :
    (trace (rowProgram N q size stage)).length ≤ 800 * queryWork q size := by
  rw [rowProgram_trace_length]
  unfold queryWork
  nlinarith

theorem buildProgram_trace_le (N q size : Nat) (hsize : 0 < size) :
    (trace (buildProgram N q size)).length ≤ 1250 * work N q size := by
  have hp := prepareProgram_trace_le N q size hsize
  have hr := rowProgram_trace_le N q size 0 hsize
  have hs : (trace (scheduleProgram N q size N)).length ≤ N * (800 * queryWork q size) := by
    rw [scheduleProgram_trace_length]
    rw [rowProgram_trace_length] at hr
    exact Nat.mul_le_mul_left N hr
  rw [buildProgram, trace_append, List.length_append]
  dsimp only [work, queryWork] at hp hs ⊢
  nlinarith [hp, hs]

theorem capacityWords_lower (q size : Nat) : 2 * (q + 2) * (size + 1) ≤ capacityWords q size := by
  unfold capacityWords workBase
  omega

theorem capacityWords_le (q size : Nat) (hsize : 0 < size) : capacityWords q size ≤ 12 * queryWork q size := by
  unfold capacityWords workBase queryWork
  nlinarith

theorem capacity_bits_le (q size : Nat) (hsize : 0 < size) :
    capacityWords q size * CapacityBits.width q ≤ 12 * queryWork q size * Nat.clog 2 (q + 2) := by
  exact Nat.mul_le_mul (capacityWords_le q size hsize) (Nat.clog_mono_right 2 (by omega))

theorem indexWords_le (q size : Nat) : indexWords size ≤ 5 * (q + size + 1) := by
  unfold indexWords
  omega

theorem heapWords_le (q size : Nat) (hsize : 0 < size) :
    capacityWords q size + indexWords size ≤ 17 * queryWork q size := by
  have hc := capacityWords_le q size hsize
  unfold indexWords queryWork at hc ⊢
  nlinarith

theorem dimension_le_work (N q size : Nat) (hsize : 0 < size) :
    N + q + 1 ≤ work N q size ∧ size ≤ work N q size ∧ 1 ≤ work N q size := by
  have hb : N + q + 1 ≤ (N + 1) * (q + 1) := by nlinarith
  have hp : 1 ≤ (N + 1) * (q + 1) := by nlinarith
  have ht := Nat.mul_le_mul_left ((N + 1) * (q + 1)) hsize
  have hs := Nat.mul_le_mul_right size hp
  simp only [Nat.mul_one, Nat.one_mul] at ht hs
  exact ⟨hb.trans ht, hs, hp.trans ht⟩

theorem queryROM_size_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    (queryROM q full 0 used).size ≤ 9 * work full.length q (prepareNormalization q full).indexed.nodes.size := by
  let N := full.length
  let size := (prepareNormalization q full).indexed.nodes.size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hd := dimension_le_work N q size hsize
  have hnq : N * q ≤ work N q size := by
    have hb : N * q ≤ (N + 1) * (q + 1) := by nlinarith
    exact hb.trans (Nat.le_mul_of_pos_right _ hsize)
  have hqt : q * size ≤ work N q size := by
    have hb : q ≤ (N + 1) * (q + 1) := by nlinarith
    exact Nat.mul_le_mul_right size hb
  have hr : (givenTreeROM q full).size ≤ 8 * work N q size := by
    rw [PhysicalROM.size, RawTreeSerialization.givenTreeROM_input_length,
      RawTreeSerialization.givenTreeROM_internal_length,
      RawTreeSerialization.givenTreeROM_children_length q full hq hlaminar]
    change 3 + N * q + size * q + 2 * size + (size - 1) ≤ _
    rw [Nat.mul_comm size q]
    omega
  have heq : (queryROM q full 0 used).size = (givenTreeROM q full).size + (q + 1) := by
    simp only [PhysicalROM.size, queryROM, List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_finRange]
    omega
  rw [heq]
  change (givenTreeROM q full).size + (q + 1) ≤ 9 * work N q size
  omega

theorem program_length_le_trace (code : List Op) : code.length ≤ (trace code).length := by
  have ho (op : Op) : 1 ≤ op.trace.length := by
    cases op with
    | subtract target left right => exact Nat.zero_lt_succ _
    | base instruction => cases instruction <;> exact Nat.zero_lt_succ _
  induction code with
  | nil => exact Nat.zero_le _
  | cons op later ih =>
    rw [List.length_cons, trace, List.flatMap_cons, List.length_append]
    have hh := ho op
    change later.length + 1 ≤ op.trace.length + (trace later).length
    omega

theorem prepared_build_totalCost (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    totalBuildCost (queryROM q full 0 used) (buildProgram full.length q size)
      (capacityWords q size + indexWords size) ≤ 8000 * work full.length q size := by
  intro size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have htrace := buildProgram_trace_le full.length q size hsize
  have hlen := program_length_le_trace (buildProgram full.length q size)
  have hrom := queryROM_size_le q full hq hlaminar used
  have hheap := heapWords_le q size hsize
  have hqwork : queryWork q size ≤ work full.length q size := by
    have hm := Nat.le_mul_of_pos_left ((q + 1) * size) (show 0 < full.length + 1 from by omega)
    simpa only [queryWork, work, Nat.mul_assoc] using hm
  have hpositive := (dimension_le_work full.length q size hsize).2.2
  rw [totalBuildCost, haltingWords_length, List.length_append, haltTrace_length]
  change (queryROM q full 0 used).size ≤ 9 * work full.length q size at hrom
  nlinarith [htrace, hlen, hrom, hheap, hqwork, hpositive]

theorem prepared_build_halting (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    HaltingRuns (queryROM q full 0 used).semantic (buildProgram full.length q size) (initial (fun _ => 0))
      (execute (queryROM q full 0 used).semantic (buildProgram full.length q size) (initial (fun _ => 0)))
      (trace (buildProgram full.length q size) ++ haltTrace) := by
  intro size
  exact execute_halts _ _ _ rfl

end PaperProofs.Structure.LaminarTree.PA17Rolling018
