module

public import Structure.PA17_A19QueryBridge_RuntimeHeader_011d

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRStaticLayout PSTRStaticHeap PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def prelude : List PackingOp := readStage ++ PSTRStaticFields.program ⟨7, by decide⟩ ++ prepareRow ++ locate

theorem prelude_length : prelude.length = 72 := rfl
theorem program_split : program = prelude ++ writeHeader := rfl

theorem prelude_noStore : ∀ op ∈ prelude, HeapPreservingOp op := by
  simp [prelude, readStage, PSTRStaticFields.program, prepareRow, locate,
    PSTRCountWorkspace.program, PA17A19RuntimeRead007.headerFinish, HeapPreservingOp]

theorem prelude_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (prelude.take count) state).heap = state.heap :=
  executeOps_heap_of_no_store rom _ state (by
    intro op ho
    exact prelude_noStore op (List.mem_of_mem_take ho))

theorem execute_prelude_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom prelude state).heap = state.heap := by
  simpa only [List.take_length] using prelude_prefix_heap rom state prelude.length

theorem prelude_address {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) :
    (executeOps (callInput q full command) prelude state).register .address = BitVec.ofNat bits (head full capWords bits) := by
  let readOnlyPart := readStage ++ PSTRStaticFields.program ⟨7, by decide⟩ ++ prepareRow
  have hh : (executeOps (callInput q full command) readOnlyPart state).heap = state.heap :=
    executeOps_heap_of_no_store _ _ state (by
      intro op ho
      exact prelude_noStore op (List.mem_append_left locate ho))
  have hr : HeapRepresents q full capWords configuration (executeOps (callInput q full command) readOnlyPart state).heap := by
    rw [hh]; exact rep
  rw [prelude, executeOps_append]
  exact (execute_locate full command configuration capWords _ hb hq hr).1

theorem prefix_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hf : Fits bits (head full capWords bits + 3)) (address count : Nat)
    (ha : address < head full capWords bits) :
    (executeOps (callInput q full command) (program.take count) state).heap (BitVec.ofNat bits address) =
      state.heap (BitVec.ofNat bits address) := by
  rw [program_split]
  by_cases hc : count ≤ prelude.length
  · rw [List.take_append_of_le_length hc, prelude_prefix_heap]
  · rw [List.take_append, List.take_of_length_le (by omega), executeOps_append]
    rw [writeHeader_prefix_frame _ _ _ (prelude_address full command configuration capWords state hb hq rep) hf address _ ha,
      execute_prelude_heap]

theorem access_prefix {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hs : configuration.stage ≤ full.length)
    (hroom : head full capWords bits + 3 < heapWords) :
    ∀ count (hc : count < program.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (program.take count) state) program[count] := by
  let rom := callInput q full command
  let s1 := executeOps rom readStage state
  let s2 := executeOps rom (PSTRStaticFields.program ⟨7, by decide⟩) s1
  let s3 := executeOps rom prepareRow s2
  let s4 := executeOps rom locate s3
  have hworkspace : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords := by
    unfold head PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase at hroom
    omega
  have hmeta : metadataAddress q capWords bits (offset q full 7 + configuration.stage) < heapWords := by
    have hin := stage_address_in_bounds full hq configuration.stage hs
    simp only [PSTRQueryLayout.physicalWorkspace, metadataAddress] at hworkspace ⊢
    omega
  have hread := execute_readStage full command configuration capWords state hq rep
  have hrep1 : HeapRepresents q full capWords configuration s1.heap := by rw [hread.2]; exact rep
  have hgetter := execute_stage_address full command configuration capWords s1 configuration.stage hb hq hrep1 hread.1
  have hheap2 : s2.heap = state.heap := hgetter.2.2.trans hread.2
  have hrep2 : HeapRepresents q full capWords configuration s2.heap := by rw [hheap2]; exact rep
  have hheap3 : s3.heap = state.heap := by
    have hp : ∀ op ∈ prepareRow, HeapPreservingOp op := by simp [prepareRow, HeapPreservingOp]
    exact (executeOps_heap_of_no_store rom prepareRow s2 hp).trans hheap2
  have hrep3 : HeapRepresents q full capWords configuration s3.heap := by rw [hheap3]; exact rep
  have hl := execute_locate full command configuration capWords s3 hb hq hrep3
  have ha := PA17A19RuntimeRead007.access_append rom heapWords
    (readStage ++ PSTRStaticFields.program ⟨7, by decide⟩ ++ prepareRow) locate state
    (PA17A19RuntimeRead007.access_append rom heapWords
      (readStage ++ PSTRStaticFields.program ⟨7, by decide⟩) prepareRow state
      (PA17A19RuntimeRead007.access_append rom heapWords readStage _ state
        (readStage_access full command configuration capWords heapWords state rep (by
          unfold PSTRQueryLayout.physicalWorkspace metadataAddress at hworkspace; omega))
        (stageGetter_access full command configuration capWords heapWords s1 configuration.stage hb hq hrep1 hread.1 hmeta))
      (prepareRow_access full command heapWords s2 hb (by omega)))
    (locate_access full command configuration capWords heapWords s3 hb hq hrep3 hworkspace)
  exact PA17A19RuntimeRead007.access_append rom heapWords _ writeHeader state ha
    (writeHeader_access rom (head full capWords bits) heapWords s4 hl.1 hroom)

theorem actual_header {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (stage : Fin (full.length + 1)) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hstage : configuration.stage = stage.val)
    (hN : Fits bits full.length) (hqr : Fits bits (q + 2))
    (htr : Fits bits (treeSize q full + 1))
    (hrr : Fits bits ((stage.val + 1) * (q + 2)))
    (hhead : Fits bits (head full capWords bits + 3))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) containing 82 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 82)) ∧
    after.register .address = BitVec.ofNat bits (head full capWords bits) ∧
    after.heap = storedHeap state.heap (head full capWords bits)
      (BitVec.ofNat bits (row full stage)) (BitVec.ofNat bits (nodeWord full hq stage))
      (BitVec.ofNat bits (PA17QueryHeader009.active full.length stage.val))
      (BitVec.ofNat bits stage.val) := by
  have hr := execute_result full command configuration capWords state stage hb hq rep hstage hN hqr htr hrr hhead
  have run := straight_segment (callInput q full command) containing program origin
    em.bound em.code program_straight em.words em.pcfit state hp ha
  rw [program_length] at run
  dsimp only
  rw [run]
  refine ⟨(executeOps_halted _ _ _).trans ha, ?_, hr⟩
  rw [executeOps_pc _ _ state program_straight, hp, program_length, BitVec.ofNat_add_ofNat]
  congr 1

theorem actual_prefix_decoded {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hs : configuration.stage ≤ full.length)
    (hroom : head full capWords bits + 3 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count < 82) :
    let before := packingRun (callInput q full command) containing count state
    before.halted = false ∧ Fits bits (before.pc.toNat + 4) ∧
      before.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (physicalFetch bits (packingCode containing) before.pc.toNat) = some op ∧
        packingAccessFits (callInput q full command) heapWords before op := by
  have hcount : count < program.length := by simpa only [program_length] using hc
  have hindex : origin + count < containing.length := by have := em.bound; omega
  let rom := callInput q full command
  have hr := actual_prefix em rom state hp ha count hcount.le
  have hpc : (packingRun rom containing count state).pc.toNat = 5 * (origin + count) := by
    rw [hr, executeOps_pc _ _ state (by
      intro op ho
      exact program_straight op (List.mem_of_mem_take ho)), hp,
      List.length_take_of_le hcount.le, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    have he : 5 * origin + 5 * count = 5 * (origin + count) := by omega
    rw [he]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hindex.le).trans_lt em.pcfit)
  have hfetch : physicalFetch bits (packingCode containing)
      (packingRun rom containing count state).pc.toNat = program[count].encode := by
    rw [hpc, physicalFetch_eq bits _ _ em.words]
    change natFetch containing (5 * (origin + count)) = _
    rw [natFetch_body containing (origin + count) hindex, em.code count hcount]
  have hsmall : (packingRun rom containing count state).pc.toNat + 4 < 5 * containing.length := by
    rw [hpc]
    omega
  refine ⟨?_, hsmall.trans em.pcfit, ?_, program[count], ?_, ?_⟩
  · rw [hr, executeOps_halted, ha]
  · rw [packingCode_length]
    exact hsmall.trans_le (Nat.le_add_right _ _)
  · rw [hfetch, decode_encode]
  · rw [hr]
    exact access_prefix full command configuration capWords heapWords state hb hq rep hs hroom count hcount

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011
