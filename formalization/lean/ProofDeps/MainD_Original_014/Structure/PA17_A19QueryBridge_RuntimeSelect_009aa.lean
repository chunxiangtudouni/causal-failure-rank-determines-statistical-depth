module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009z
public import Structure.PSTR_HD_StaticLeaf_024

/-! Fixed48op original-leaf-label reader for descent. This reuses the frozen
PSTR metadata reader, workspace locator and007 header restoration. It does
not read used bits or materialize counts; the entire heap is unchanged. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def leafReadProgram : List PackingOp :=
  PSTRStaticFields.program ⟨6, by decide⟩ ++ PSTRCountWorkspace.program ++ PA17A19RuntimeRead007.headerFinish

theorem leafReadProgram_length : leafReadProgram.length = 48 := rfl

theorem leafReadProgram_straight : StraightProgram leafReadProgram := by
  intro op ho
  simp only [leafReadProgram, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · exact PSTRStaticFields.program_straight _ op ho
  · exact PSTRCountWorkspace.program_straight op ho
  · exact PA17A19RuntimeRead007.headerFinish_straight op ho

theorem leafReadProgram_noStore : ∀ op ∈ leafReadProgram, HeapPreservingOp op := by
  simp [leafReadProgram, PSTRStaticFields.program, PSTRCountWorkspace.program, PA17A19RuntimeRead007.headerFinish, HeapPreservingOp]

theorem leafReadProgram_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (clock : Nat) :
    (executeOps rom (leafReadProgram.take clock) state).heap = state.heap :=
  executeOps_heap_of_no_store rom _ state (by intro op ho; exact leafReadProgram_noStore op (List.mem_of_mem_take ho))

theorem leafRead_header_index {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom PA17A19RuntimeRead007.headerFinish state).register .index = state.register .index := rfl

theorem execute_leafRead {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val) :
    let after := executeOps (callInput q full command) leafReadProgram state
    after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) ∧
      after.register .value = BitVec.ofNat bits
        (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
          | none => 0 | some tool => tool.val + 1) ∧
      after.register .index = state.register .index ∧ after.heap = state.heap ∧ after.halted = state.halted := by
  let rom := callInput q full command
  let labeled := executeOps rom (PSTRStaticFields.program ⟨6, by decide⟩) state
  let located := executeOps rom PSTRCountWorkspace.program labeled
  have hl := PSTRStaticFields.execute_leaf full command configuration capWords state node hb hq rep hN hi
  have hrep : HeapRepresents q full capWords configuration labeled.heap := by rw [hl.2.2]; exact rep
  have hloc := PSTRCountWorkspace.execute_base full command configuration capWords labeled hb hq hrep
  rcases hloc with ⟨haddr, hvalue, hindex, _, _, hheap, _⟩
  have haddr' : located.register .address = BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits) := by
    rw [PSTRCountWorkspace.base_metadata_end q full hq] at haddr
    exact haddr
  have hh : (located.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by
    rw [hheap, hl.2.2]
    exact rep.1
  have hfinish := PA17A19RuntimeRead007.headerFinish_address rom (PSTRQueryLayout.physicalWorkspace full capWords bits)
    (treeSize q full) located hb hh haddr'
  dsimp only
  rw [leafReadProgram, executeOps_append, executeOps_append]
  refine ⟨hfinish, ?_, ?_, ?_, ?_⟩
  · exact (PA17A19RuntimeRead007.headerFinish_value rom located).trans (hvalue.trans hl.1)
  · exact (leafRead_header_index rom located).trans (hindex.trans hl.2.1)
  · exact executeOps_heap_of_no_store rom leafReadProgram state leafReadProgram_noStore
  · exact executeOps_halted rom leafReadProgram state

theorem leafRead_actual {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + leafReadProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < leafReadProgram.length), containing[origin + i]'(by omega) = leafReadProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    packingRun rom containing 48 state = executeOps rom leafReadProgram state := by
  simpa only [leafReadProgram_length] using straight_segment rom containing leafReadProgram origin hbound hcode
    leafReadProgram_straight hw hpc state hp ha

theorem leafRead_trace {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom containing 48 state).length ≤ 576 := packingDynamicTrace_length_le rom containing 48 state

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
