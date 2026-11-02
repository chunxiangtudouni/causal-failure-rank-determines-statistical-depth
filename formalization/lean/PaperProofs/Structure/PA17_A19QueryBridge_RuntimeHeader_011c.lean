module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeHeader_011b
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRead_007b

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRStaticLayout PSTRStaticHeap PSTRWordSegments

def head {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat) : Nat :=
  PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)

def row {q : Nat} (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) : Nat :=
  PA17QueryBudget015.rowBase q (treeSize q full) (PA17QueryBudget015.rowIndex full stage).val

def nodeWord {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin (full.length + 1)) : Nat :=
  encodedNode (prepareNormalization q full).indexed (PA17QueryBudget015.node full hq stage)

theorem execute_result {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (stage : Fin (full.length + 1)) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hstage : configuration.stage = stage.val)
    (hN : Fits bits full.length) (hqr : Fits bits (q + 2))
    (htr : Fits bits (treeSize q full + 1))
    (hrr : Fits bits ((stage.val + 1) * (q + 2)))
    (hhead : Fits bits (head full capWords bits + 3)) :
    let after := executeOps (callInput q full command) program state
    after.register .address = BitVec.ofNat bits (head full capWords bits) ∧
    after.heap = storedHeap state.heap (head full capWords bits)
      (BitVec.ofNat bits (row full stage)) (BitVec.ofNat bits (nodeWord full hq stage))
      (BitVec.ofNat bits (PA17QueryHeader009.active full.length stage.val))
      (BitVec.ofNat bits stage.val) := by
  let rom := callInput q full command
  let s1 := executeOps rom readStage state
  let s2 := executeOps rom (PSTRStaticFields.program ⟨7, by decide⟩) s1
  let s3 := executeOps rom prepareRow s2
  let s4 := executeOps rom locate s3
  have h1 := execute_readStage full command configuration capWords state hq rep
  have hrep1 : HeapRepresents q full capWords configuration s1.heap := by rw [h1.2]; exact rep
  have hi1 : s1.register .index = BitVec.ofNat bits stage.val := by rw [h1.1, hstage]
  have h2 := execute_stage_address full command configuration capWords s1 stage.val hb hq hrep1 hi1
  have hheap2 : s2.heap = state.heap := h2.2.2.trans h1.2
  have hrep2 : HeapRepresents q full capWords configuration s2.heap := by rw [hheap2]; exact rep
  have hi2 : s2.register .index = BitVec.ofNat bits stage.val := h2.2.1.trans hi1
  have h3 := execute_prepareRow rom full.length q (treeSize q full) stage.val s2 hb hN
    (by have := stage.isLt; omega) hqr htr hrr rfl rfl (by rw [hheap2]; exact rep.1) hi2
  have hheap3 : s3.heap = state.heap := h3.2.2.2.2.trans hheap2
  have hrep3 : HeapRepresents q full capWords configuration s3.heap := by rw [hheap3]; exact rep
  have h4 := execute_locate full command configuration capWords s3 hb hq hrep3
  have hn := execute_node full command configuration capWords s1 stage hb hq hrep1 hN hi1
  have hrow : s4.register .old = BitVec.ofNat bits (row full stage) := by
    rw [h4.2.1, h3.1, PA17QueryBudget015.header_rowPointer]
    rfl
  have hnode : s4.register .value = BitVec.ofNat bits (nodeWord full hq stage) :=
    h4.2.2.2.1.trans (h3.2.2.1.trans hn)
  have hactive : s4.register .fresh = BitVec.ofNat bits (PA17QueryHeader009.active full.length stage.val) :=
    h4.2.2.1.trans h3.2.1
  have hindex : s4.register .index = BitVec.ofNat bits stage.val :=
    h4.2.2.2.2.1.trans (h3.2.2.2.1.trans hi2)
  have hheap4 : s4.heap = state.heap := h4.2.2.2.2.2.trans hheap3
  have h5 := execute_writeHeader rom (head full capWords bits) s4 hb hhead h4.1
  dsimp only
  simp only [program, executeOps_append]
  change (executeOps rom writeHeader s4).register .address = _ ∧ _
  refine ⟨h5.1, ?_⟩
  rw [h5.2, hrow, hnode, hactive, hindex, hheap4]

/-- Exact lower-region prefix frame, including table/used/metadata, W0..15,
counts and the full sentinel-parent array. -/
theorem writeHeader_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (ha : state.register .address = BitVec.ofNat bits header)
    (hf : Fits bits (header + 3)) (address count : Nat) (haddress : address < header) :
    (executeOps rom (writeHeader.take count) state).heap (BitVec.ofNat bits address) =
      state.heap (BitVec.ofNat bits address) := by
  have hbound : header + 3 < 2 ^ bits := hf
  have hne (i : Nat) (hi : i ≤ 3) : BitVec.ofNat bits address ≠ BitVec.ofNat bits (header + i) := by
    intro he
    have hv := congrArg BitVec.toNat he
    rw [show (BitVec.ofNat bits address).toNat = address from Nat.mod_eq_of_lt (by omega),
      show (BitVec.ofNat bits (header + i)).toNat = header + i from Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hzero : BitVec.ofNat bits address ≠ BitVec.ofNat bits header := by
    simpa only [Nat.add_zero] using hne 0 (by omega)
  by_cases hc : count < writeHeader.length
  · change count < 10 at hc
    interval_cases count <;>
      simp +decide [writeHeader, executeOps, packingExecuteOp, wordOp, wordInstruction,
        ha, BitVec.ofNat_add_ofNat, Nat.add_assoc, hne, hzero]
  · rw [List.take_of_length_le (by omega)]
    simp +decide [writeHeader, executeOps, packingExecuteOp, wordOp, wordInstruction,
      ha, BitVec.ofNat_add_ofNat, Nat.add_assoc, hne, hzero]

structure Embedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + program.length ≤ containing.length
  code : ∀ i (hi : i < program.length), containing[origin + i]'(by omega) = program[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem actual_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ program.length) :
    packingRun rom containing count state = executeOps rom (program.take count) state := by
  have hl : (program.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply straight_segment rom containing (program.take count) origin (by have := em.bound; omega)
    ?_ ?_ em.words em.pcfit state hp ha
  · intro i hi
    have hi' : i < program.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using em.code i hi'
  · intro op ho
    exact program_straight op (List.mem_of_mem_take ho)

theorem inline_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (state : WordState bits) :
    (packingDynamicTrace rom containing 82 state).length ≤ 984 :=
  packingDynamicTrace_length_le rom containing 82 state

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011
