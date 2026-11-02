module

public import PaperProofs.Structure.PA17_StageMap_001
public import PaperProofs.Structure.UniformFreeTableSafety

/-! A17 batch 003: metadata is after the entire leading capacity allocation,
including the table and two capacity work areas. The pass computes both
metadata and stage mapping itself from the original given-tree ROM. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17MetadataAssembly003

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open UniformFreeTableSafety

def stageBase (size base : Nat) : Nat := base + 3 * size + 1
def workspaceBase (N size base : Nat) : Nat := stageBase size base + N
def indexWords (N size : Nat) : Nat := 3 * size + 1 + N

def program (N q size base : Nat) : List Op :=
  UniformTreeMetadataRAM.program N q size base ++
    PA17StageMap001.program N q size (stageBase size base)

theorem workspaceBase_eq (N size base : Nat) :
    workspaceBase N size base = base + indexWords N size := by
  dsimp [workspaceBase, stageBase, indexWords]
  omega

theorem indexWords_le (N q size : Nat) : indexWords N size ≤ 3 * (N + q + size + 1) := by
  dsimp [indexWords]
  omega

theorem stage_program_preserves_metadata (q : Nat) (full : List (Finset (Fin q)))
    (base : Nat) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full base state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    UniformTreeMetadataRAM.MetadataCorrect q full base
      (IndexedClosureRAM.execute (givenTreeROM q full).semantic
        (PA17StageMap001.program full.length q size (stageBase size base)) state).heap := by
  intro size
  constructor
  · rw [PA17StageMap001.program_frame _ _ _ _ _ state _ (Or.inl (by
      dsimp [UniformTreeMetadataRAM.parentAddress, stageBase]
      omega))]
    exact hm.1
  · intro node
    rw [PA17StageMap001.program_frame _ _ _ _ _ state _ (Or.inl (by
      dsimp [UniformTreeMetadataRAM.cardAddress, stageBase]
      have hn := node.isLt
      omega)), PA17StageMap001.program_frame _ _ _ _ _ state _ (Or.inl (by
      dsimp [UniformTreeMetadataRAM.parentAddress, stageBase]
      have hn := node.isLt
      omega)), PA17StageMap001.program_frame _ _ _ _ _ state _ (Or.inl (by
      dsimp [UniformTreeMetadataRAM.internalAddress, stageBase]
      have hn := node.isLt
      omega))]
    exact hm.2 node

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (base : Nat) (state : State) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := IndexedClosureRAM.execute (givenTreeROM q full).semantic (program N q size base) state
    UniformTreeMetadataRAM.MetadataCorrect q full base result.heap ∧
      PA17StageMap001.StageMapCorrect q full hq (stageBase size base) result.heap := by
  intro N size result
  dsimp only [result, program]
  rw [IndexedClosureRAM.execute_append]
  constructor
  · exact stage_program_preserves_metadata q full base _
      (UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar base state)
  · exact PA17StageMap001.prepared_program_correct q full hq _ _

theorem leading_prefixFrame (rom : ROM) (N q size base address : Nat) (ha : address < base) :
    PrefixFrame rom (program N q size base) address := by
  rw [program]
  apply PrefixFrame.append rom _ _ address
  · exact metadataProgram_prefixFrame rom N q size base address ha
  · intro state count _
    exact PA17StageMap001.program_take_frame rom N q size (stageBase size base) count state address
      (Or.inl (by dsimp [stageBase]; omega))

theorem leading_take_frame (rom : ROM) (N q size base count : Nat) (state : State)
    (address : Nat) (ha : address < base) :
    (IndexedClosureRAM.execute rom ((program N q size base).take count) state).heap address = state.heap address := by
  by_cases hc : count ≤ (program N q size base).length
  · exact leading_prefixFrame rom N q size base address ha state count hc
  · rw [List.take_of_length_le (by omega)]
    simpa only [List.take_length] using
      leading_prefixFrame rom N q size base address ha state (program N q size base).length le_rfl

theorem leading_capacityThroughout (rom : PhysicalROM) (N q size base : Nat) (state : State)
    (hcap : CapacityPrefixBounded q base state.heap) :
    CapacityThroughout q base rom (program N q size base) state := by
  intro count _ address ha
  rw [leading_take_frame rom.semantic N q size base count state address ha]
  exact hcap address ha

theorem workspace_frame (rom : ROM) (N q size base : Nat) (state : State)
    (address : Nat) (ha : workspaceBase N size base ≤ address) :
    (IndexedClosureRAM.execute rom (program N q size base) state).heap address = state.heap address := by
  rw [program, IndexedClosureRAM.execute_append,
    PA17StageMap001.program_frame rom N q size _ _ address (Or.inr ha),
    UniformTreeMetadataRAM.program_frame rom N q size base state address (Or.inr (by
      dsimp [workspaceBase, stageBase] at ha
      omega))]

theorem program_length (N q size base : Nat) :
    (program N q size base).length = (3 * q + 14) * size + 3 + N * ((8 * q + 3) * size + 3) := by
  rw [program, List.length_append, UniformTreeMetadataRAM.program_length, PA17StageMap001.program_length]

theorem program_trace_length (N q size base : Nat) :
    (trace (program N q size base)).length = (30 * q + 131) * size + 27 + N * ((82 * q + 28) * size + 27) := by
  rw [program, trace_append, List.length_append, UniformTreeMetadataRAM.program_trace_length,
    PA17StageMap001.program_trace_length]

theorem program_codeWords_length (N q size base : Nat) :
    (haltingWords (program N q size base)).length =
      5 * ((3 * q + 14) * size + 3 + N * ((8 * q + 3) * size + 3)) + 5 := by
  rw [haltingWords, List.length_append, IndexedClosureRAM.programWords_length, program_length]
  rfl

theorem program_trace_le (N q size base : Nat) (hsize : 0 < size) :
    (trace (program N q size base) ++ haltTrace).length ≤ 200 * work N q size := by
  rw [List.length_append, program_trace_length, haltTrace_length]
  have hmeta : (30 * q + 131) * size + 33 ≤ 200 * (q + 1) * size := by nlinarith
  have hstage : (82 * q + 28) * size + 27 ≤ 137 * (q + 1) * size := by nlinarith
  have hmul := Nat.mul_le_mul_left N hstage
  dsimp [work]
  nlinarith

theorem program_code_le (N q size base : Nat) (hsize : 0 < size) :
    (haltingWords (program N q size base)).length ≤ 100 * work N q size := by
  rw [program_codeWords_length]
  have hmeta : 5 * ((3 * q + 14) * size + 3) + 5 ≤ 100 * (q + 1) * size := by nlinarith
  have hstage : 5 * ((8 * q + 3) * size + 3) ≤ 55 * (q + 1) * size := by nlinarith
  have hmul := Nat.mul_le_mul_left N hstage
  dsimp [work]
  nlinarith

theorem prepared_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (base : Nat) (state : State) (hpc : state.pc = 0) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (program N q size base) state final operations ∧
      UniformTreeMetadataRAM.MetadataCorrect q full base final.heap ∧
      PA17StageMap001.StageMapCorrect q full hq (stageBase size base) final.heap ∧
      (∀ address < base, final.heap address = state.heap address) ∧
      operations.length ≤ 200 * work N q size := by
  intro N size
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hm := prepared_program_correct q full hq hlaminar base state
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc, hm.1, hm.2, ?_, program_trace_le _ _ _ _ hsize⟩
  intro address ha
  simpa only [List.take_length] using leading_take_frame (givenTreeROM q full).semantic N q size base
    (program N q size base).length state address ha

/- Concrete table + two capacity-area layout requested by the coordinator. -/
def workBase (N q size : Nat) : Nat := tableWords N q size
def accumulatorBase (N q size : Nat) : Nat := workBase N q size + (size + 1)
def capacityWords (N q size : Nat) : Nat := tableWords N q size + 2 * (size + 1)

theorem tableWords_le_capacityWords (N q size : Nat) : tableWords N q size ≤ capacityWords N q size := by
  dsimp [capacityWords]
  omega

theorem workArea_lt_capacityWords (N q size slot : Nat) (hs : slot ≤ size) :
    workBase N q size + slot < capacityWords N q size := by
  dsimp [workBase, capacityWords]
  omega

theorem accumulatorArea_lt_capacityWords (N q size slot : Nat) (hs : slot ≤ size) :
    accumulatorBase N q size + slot < capacityWords N q size := by
  dsimp [accumulatorBase, workBase, capacityWords]
  omega

theorem capacityAreas_disjoint (N q size left right : Nat) (hl : left ≤ size) :
    workBase N q size + left ≠ accumulatorBase N q size + right := by
  dsimp [accumulatorBase]
  omega

theorem table_before_workAreas (N q size address : Nat) (ha : address < tableWords N q size) (slot : Nat) :
    address ≠ workBase N q size + slot ∧ address ≠ accumulatorBase N q size + slot := by
  dsimp [workBase, accumulatorBase]
  omega

theorem capacityWords_le (N q size : Nat) (hsize : 0 < size) :
    capacityWords N q size ≤ 8 * work N q size := by
  have ht : size + 1 ≤ 2 * size := by omega
  have hq : q + 2 ≤ 2 * (q + 1) := by omega
  have hm := Nat.mul_le_mul_left (N + 1) (Nat.mul_le_mul hq ht)
  have hwork : size ≤ (N + 1) * (q + 1) * size := by
    exact Nat.le_mul_of_pos_left size (Nat.mul_pos (by omega) (by omega))
  dsimp [capacityWords, tableWords, cells, work]
  nlinarith

def concreteProgram (N q size : Nat) : List Op := program N q size (capacityWords N q size)

theorem concrete_capacityThroughout (rom : PhysicalROM) (N q size : Nat) (state : State)
    (hcap : CapacityPrefixBounded q (capacityWords N q size) state.heap) :
    CapacityThroughout q (capacityWords N q size) rom (concreteProgram N q size) state :=
  leading_capacityThroughout rom N q size _ state hcap

end PaperProofs.Structure.LaminarTree.PA17MetadataAssembly003
