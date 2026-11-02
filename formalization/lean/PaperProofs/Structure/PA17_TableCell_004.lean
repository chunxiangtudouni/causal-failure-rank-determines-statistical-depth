module

public import PaperProofs.Structure.PA17_CellLayout_003
public import PaperProofs.Structure.PA17_MetadataAssembly_003

/-! A17 batch 004: a full tag-first persistent-table cell. Actual RAM copies
put the bad entry into the tag-last work area, the dimension-only kernel
computes the original cell there, and an actual copy writes its tagged output.
Metadata and stage mapping persist. No tree/cache is compiled into the code. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17TableCell004

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001

def tableBase (size slot : Nat) : Nat := slot * (size + 1)

def program (N q size goodSlot badSlot outputSlot stage : Nat) : List Op :=
  toTagLast size (tableBase size badSlot) (PA17CellLayout003.workBase N q size) ++
    PA17CellLayout003.kernelProgram N q size goodSlot stage ++
    toTagFirst size (PA17CellLayout003.workBase N q size) (tableBase size outputSlot)

def Persistent (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (heap : Nat → Nat) : Prop :=
  let size := (prepareNormalization q full).indexed.nodes.size
  UniformTreeMetadataRAM.MetadataCorrect q full (PA17CellLayout003.metadataBase full.length q size) heap ∧
    PA17StageMap001.StageMapCorrect q full hq (PA17CellLayout003.stageBase full.length q size) heap

theorem persistent_transfer (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (old fresh : Nat → Nat) (hp : Persistent q full hq old)
    (hframe : ∀ address, PA17CellLayout003.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size ≤ address → fresh address = old address) :
    Persistent q full hq fresh := by
  let size := (prepareNormalization q full).indexed.nodes.size
  constructor
  · constructor
    · rw [hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress, PA17CellLayout003.metadataBase]; omega)]
      exact hp.1.1
    · intro node
      rw [hframe _ (by dsimp [UniformTreeMetadataRAM.cardAddress, PA17CellLayout003.metadataBase]; omega),
        hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress, PA17CellLayout003.metadataBase]; omega),
        hframe _ (by dsimp [UniformTreeMetadataRAM.internalAddress, PA17CellLayout003.metadataBase]; omega)]
      exact hp.1.2 node
  · intro stage
    rw [hframe _ (by dsimp [PA17CellLayout003.stageBase, PA17CellLayout003.metadataBase]; omega)]
    exact hp.2 stage

theorem tagFirstRep_transfer {Tool : Type*} (cache : IndexedNodeCache Tool) (old fresh : Nat → Nat)
    (base : Nat) (entry : IndexedEntry.FixedEntry cache) (hrep : TagFirstRep cache old base entry)
    (hframe : ∀ index ≤ cache.nodes.size, fresh (base + index) = old (base + index)) :
    TagFirstRep cache fresh base entry := by
  cases entry with
  | void =>
    change fresh base = 0
    rw [show fresh base = old base from by simpa only [Nat.add_zero] using hframe 0 (Nat.zero_le _)]
    exact hrep
  | vector capacity =>
    constructor
    · rw [show fresh base = old base from by simpa only [Nat.add_zero] using hframe 0 (Nat.zero_le _)]
      exact hrep.1
    · intro node
      rw [show fresh (base + 1 + node.val) = old (base + 1 + node.val) from by
        simpa only [Nat.add_assoc] using hframe (1 + node.val) (by have := node.isLt; omega)]
      exact hrep.2 node

theorem tableSlots_disjoint (size left right : Nat) (hne : left ≠ right) :
    DisjointSlots size (tableBase size left) (tableBase size right) := by
  intro li hli ri hri
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := Nat.mul_le_mul_right (size + 1) (show left + 1 ≤ right from by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    dsimp [tableBase]
    omega
  · have hh := Nat.mul_le_mul_right (size + 1) (show right + 1 ≤ left from by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    dsimp [tableBase]
    omega

theorem toWork_frame (rom : ROM) (N q size badSlot : Nat) (state : State) (address : Nat)
    (ha : address < tableWords N q size ∨ PA17CellLayout003.capacityWords N q size ≤ address) :
    (execute rom (toTagLast size (tableBase size badSlot) (PA17CellLayout003.workBase N q size)) state).heap address =
      state.heap address := by
  apply toTagLast_frame
  intro index hi
  have hb := (PA17CellLayout003.capacity_slots_before_indices N q size index hi).1
  dsimp [PA17CellLayout003.metadataBase] at hb
  rcases ha with ha | ha
  · dsimp [PA17CellLayout003.workBase]
    omega
  · omega

theorem toWork_persistent (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (badSlot : Nat) (state : State) (hp : Persistent q full hq state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    Persistent q full hq
      (execute (givenTreeROM q full).semantic
        (toTagLast size (tableBase size badSlot) (PA17CellLayout003.workBase full.length q size)) state).heap := by
  apply persistent_transfer q full hq state.heap _ hp
  intro address ha
  exact toWork_frame _ _ _ _ _ _ address (Or.inr ha)

theorem prepared_program_output (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodSlot badSlot outputSlot : Nat)
    (hgood : goodSlot < cells full.length q) (hbad : badSlot < cells full.length q)
    (hout : outputSlot < cells full.length q) (stage : Fin full.length)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (state : State)
    (hp : Persistent q full hq state.heap)
    (hg : TagFirstRep (prepareNormalization q full).indexed state.heap
      (tableBase (prepareNormalization q full).indexed.nodes.size goodSlot) good)
    (hb : TagFirstRep (prepareNormalization q full).indexed state.heap
      (tableBase (prepareNormalization q full).indexed.nodes.size badSlot) bad) :
    let cache := (prepareNormalization q full).indexed
    TagFirstRep cache (execute (givenTreeROM q full).semantic
      (program full.length q cache.nodes.size goodSlot badSlot outputSlot stage.val) state).heap
      (tableBase cache.nodes.size outputSlot) (IndexedEntry.cell cache full[stage.val] good bad) := by
  intro cache
  let rom := (givenTreeROM q full).semantic
  let copied := execute rom (toTagLast cache.nodes.size (tableBase cache.nodes.size badSlot)
    (PA17CellLayout003.workBase full.length q cache.nodes.size)) state
  have hcopyp := toWork_persistent q full hq badSlot state hp
  have hcopyg : TagFirstRep cache copied.heap (tableBase cache.nodes.size goodSlot) good := by
    apply tagFirstRep_transfer cache state.heap copied.heap _ good hg
    intro index hi
    exact toWork_frame rom full.length q cache.nodes.size badSlot state _ (Or.inl
      (PA17CellLayout003.table_slot_bound _ _ _ _ hgood index hi))
  have hcopyb : IndexedCellRAM.SlotRep cache copied.heap
      (PA17CellLayout003.workBase full.length q cache.nodes.size) bad :=
    toTagLast_rep cache rom _ _ (by
      intro left hl right hr
      exact (PA17CellLayout003.work_good_disjoint _ _ _ _ hbad right hr left hl).symm) state bad hb
  have hk := PA17CellLayout003.prepared_kernelProgram_result q full hq hlaminar goodSlot hgood stage
    good bad copied hcopyp.1 (hcopyp.2 stage) hcopyg hcopyb
  rw [program, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  exact toTagFirst_rep cache rom _ _ (PA17CellLayout003.work_good_disjoint _ _ _ _ hout) _ _ hk

theorem prepared_program_readEntry (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodSlot badSlot outputSlot : Nat)
    (hgood : goodSlot < cells full.length q) (hbad : badSlot < cells full.length q)
    (hout : outputSlot < cells full.length q) (stage : Fin full.length)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (state : State)
    (hp : Persistent q full hq state.heap)
    (hg : TagFirstRep (prepareNormalization q full).indexed state.heap
      (tableBase (prepareNormalization q full).indexed.nodes.size goodSlot) good)
    (hb : TagFirstRep (prepareNormalization q full).indexed state.heap
      (tableBase (prepareNormalization q full).indexed.nodes.size badSlot) bad) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size outputSlot
      (execute (givenTreeROM q full).semantic
        (program full.length q cache.nodes.size goodSlot badSlot outputSlot stage.val) state).heap =
      IndexedEntry.cell cache full[stage.val] good bad :=
  readEntry_eq_of_rep _ outputSlot _ _
    (prepared_program_output q full hq hlaminar goodSlot badSlot outputSlot hgood hbad hout stage good bad state hp hg hb)

theorem prepared_program_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodSlot badSlot outputSlot : Nat)
    (stage : Fin full.length) (state : State)
    (hp : Persistent q full hq state.heap) (address : Nat)
    (ha : address < tableWords full.length q (prepareNormalization q full).indexed.nodes.size ∨
      PA17CellLayout003.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size ≤ address)
    (ho : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size,
      address ≠ tableBase (prepareNormalization q full).indexed.nodes.size outputSlot + index) :
    (execute (givenTreeROM q full).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size goodSlot badSlot outputSlot stage.val) state).heap address =
      state.heap address := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := (givenTreeROM q full).semantic
  let copied := execute rom (toTagLast size (tableBase size badSlot) (PA17CellLayout003.workBase full.length q size)) state
  have hcopyp := toWork_persistent q full hq badSlot state hp
  rw [program, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    toTagFirst_frame _ _ _ _ _ address ho,
    PA17CellLayout003.prepared_kernelProgram_frame q full hq hlaminar goodSlot stage copied hcopyp.1
      (hcopyp.2 stage) address ha, toWork_frame _ _ _ _ _ state address ha]

theorem prepared_program_persistent (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodSlot badSlot outputSlot : Nat)
    (hout : outputSlot < cells full.length q) (stage : Fin full.length) (state : State)
    (hp : Persistent q full hq state.heap) :
    Persistent q full hq (execute (givenTreeROM q full).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size goodSlot badSlot outputSlot stage.val) state).heap := by
  apply persistent_transfer q full hq state.heap _ hp
  intro address ha
  apply prepared_program_frame q full hq hlaminar goodSlot badSlot outputSlot stage state hp address (Or.inr ha)
  intro index hi
  have hb := PA17CellLayout003.table_slot_bound full.length q
    (prepareNormalization q full).indexed.nodes.size outputSlot hout index hi
  have hc := PA17CellLayout003.table_le_capacityWords full.length q (prepareNormalization q full).indexed.nodes.size
  dsimp [tableBase]
  omega

theorem prepared_program_preserves_slot (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodSlot badSlot outputSlot : Nat)
    (stage : Fin full.length) (state : State)
    (hp : Persistent q full hq state.heap) (slot : Nat) (hs : slot < cells full.length q)
    (hne : slot ≠ outputSlot) (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hrep : TagFirstRep (prepareNormalization q full).indexed state.heap
      (tableBase (prepareNormalization q full).indexed.nodes.size slot) entry) :
    TagFirstRep (prepareNormalization q full).indexed (execute (givenTreeROM q full).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size goodSlot badSlot outputSlot stage.val) state).heap
      (tableBase (prepareNormalization q full).indexed.nodes.size slot) entry := by
  apply tagFirstRep_transfer _ state.heap _ _ entry hrep
  intro index hi
  exact prepared_program_frame q full hq hlaminar goodSlot badSlot outputSlot stage state hp _
    (Or.inl (PA17CellLayout003.table_slot_bound _ _ _ _ hs index hi))
    (fun other ho => tableSlots_disjoint _ slot outputSlot hne index hi other ho)

theorem readEntry_congr (size slot : Nat) (old fresh : Nat → Nat)
    (hframe : ∀ index ≤ size, fresh (tableBase size slot + index) = old (tableBase size slot + index)) :
    readEntry size slot fresh = readEntry size slot old := by
  have htag : fresh (slot * (size + 1)) = old (slot * (size + 1)) := by
    simpa only [tableBase, Nat.add_zero] using hframe 0 (Nat.zero_le _)
  simp only [readEntry, htag]
  split_ifs
  · rfl
  · apply congrArg CapacityBits.Entry.vector
    apply Vector.ext
    intro index hi
    change (Vector.ofFn _).get ⟨index, hi⟩ = (Vector.ofFn _).get ⟨index, hi⟩
    rw [cache_get_ofFn, cache_get_ofFn]
    simpa only [tableBase, Nat.add_assoc] using hframe (1 + index) (by omega)

theorem prepared_program_readEntry_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodSlot badSlot outputSlot : Nat)
    (stage : Fin full.length) (state : State) (hp : Persistent q full hq state.heap)
    (slot : Nat) (hs : slot < cells full.length q) (hne : slot ≠ outputSlot) :
    let size := (prepareNormalization q full).indexed.nodes.size
    readEntry size slot (execute (givenTreeROM q full).semantic
      (program full.length q size goodSlot badSlot outputSlot stage.val) state).heap = readEntry size slot state.heap := by
  intro size
  apply readEntry_congr
  intro index hi
  exact prepared_program_frame q full hq hlaminar goodSlot badSlot outputSlot stage state hp _
    (Or.inl (PA17CellLayout003.table_slot_bound _ _ _ _ hs index hi))
    (fun other ho => tableSlots_disjoint _ slot outputSlot hne index hi other ho)

theorem prepared_assembly_persistent (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) :
    let size := (prepareNormalization q full).indexed.nodes.size
    Persistent q full hq (execute (givenTreeROM q full).semantic
      (PA17MetadataAssembly003.concreteProgram full.length q size) state).heap :=
  PA17MetadataAssembly003.prepared_program_correct q full hq hlaminar _ state

theorem program_length (N q size goodSlot badSlot outputSlot stage : Nat) :
    (program N q size goodSlot badSlot outputSlot stage).length = 46 * size + 26 := by
  rw [program, List.length_append, List.length_append, toTagLast_length, toTagFirst_length,
    PA17CellLayout003.kernelProgram, PA17UniformCell002.kernelProgram_length]
  omega

theorem program_trace_length (N q size goodSlot badSlot outputSlot stage : Nat) :
    (trace (program N q size goodSlot badSlot outputSlot stage)).length = 462 * size + 248 := by
  rw [program, trace_append, trace_append, List.length_append, List.length_append,
    toTagLast_trace_length, toTagFirst_trace_length,
    PA17CellLayout003.kernelProgram, PA17UniformCell002.kernelProgram_trace_length]
  omega

theorem program_codeWords_length (N q size goodSlot badSlot outputSlot stage : Nat) :
    (haltingWords (program N q size goodSlot badSlot outputSlot stage)).length = 230 * size + 135 := by
  rw [haltingWords_length, program_length]
  omega

theorem program_halting (rom : ROM) (N q size goodSlot badSlot outputSlot stage : Nat)
    (hsize : 0 < size) (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (program N q size goodSlot badSlot outputSlot stage) state
      (execute rom (program N q size goodSlot badSlot outputSlot stage) state)
      (trace (program N q size goodSlot badSlot outputSlot stage) ++ haltTrace) ∧
    (trace (program N q size goodSlot badSlot outputSlot stage) ++ haltTrace).length ≤ 716 * size := by
  refine ⟨IndexedClosureRAM.execute_halts _ _ state hpc, ?_⟩
  rw [List.length_append, program_trace_length, haltTrace_length]
  omega

end PaperProofs.Structure.LaminarTree.PA17TableCell004
