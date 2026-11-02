module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009aa

/-! The fixed leaf-label reader's real prefix access and fetch safety.
N's finite-word bound follows from the original serialized metadata layout;
no extra original input eligibility or leaf/used oracle is introduced. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem ReverseLayout.lengthFits {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size) :
    Fits bits full.length := by
  have hn : full.length ≤ (staticMetadata q full).length := by
    rw [PSTRStaticLayout.metadata_length q full layout.positive]
    omega
  have hm := layout.metadata_le
  exact (show full.length ≤ header + 8 by omega).trans_lt (layout.headerFits 8 (by decide))

theorem leafReadProgram_access {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hi : state.register .index = BitVec.ofNat bits node.val) :
    ∀ clock (hc : clock < leafReadProgram.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (leafReadProgram.take clock) state) leafReadProgram[clock] := by
  let rom := callInput q full command
  let labeled := executeOps rom (PSTRStaticFields.program ⟨6, by decide⟩) state
  have hchunks : 6 < (PSTRStaticLayout.chunks q full layout.positive).length := by simp [PSTRStaticLayout.chunks]
  have hposition : node.val < (PSTRStaticLayout.chunks q full layout.positive)[6].length := by
    simpa only [PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero, List.length_map, List.length_finRange] using node.isLt
  have hbound := PSTRStaticLayout.chunk_in_bounds q full layout.positive 6 node.val (by decide) hposition
  have hmeta := layout.metadata_le
  have hhead := layout.headerAllocated
  have hfieldRoom : PSTRStaticHeap.metadataAddress q capWords bits (PSTRStaticLayout.offset q full 6 + node.val) < heapWords := by
    unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
    omega
  have hworkRoom : PSTRCountWorkspace.base q full capWords bits < heapWords := by
    rw [PSTRCountWorkspace.base_metadata_end q full layout.positive]
    unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
    omega
  have hl := PSTRStaticFields.execute_leaf full command configuration capWords state node layout.bits8 layout.positive rep layout.lengthFits hi
  have hlrep : HeapRepresents q full capWords configuration labeled.heap := by rw [hl.2.2]; exact rep
  have hfield := PSTRStaticFields.prefix_access full command configuration capWords heapWords state ⟨6, by decide⟩ node.val
    layout.bits8 layout.positive rep layout.lengthFits hposition hi hfieldRoom
  have hwork := PSTRCountWorkspace.prefix_access full command configuration capWords heapWords labeled hlrep hworkRoom layout.bits8
  have hleft := PA17A19RuntimeRead007.access_append rom heapWords (PSTRStaticFields.program ⟨6, by decide⟩) PSTRCountWorkspace.program state hfield hwork
  have hall := PA17A19RuntimeRead007.access_append rom heapWords
    (PSTRStaticFields.program ⟨6, by decide⟩ ++ PSTRCountWorkspace.program) PA17A19RuntimeRead007.headerFinish state hleft
    (PA17A19RuntimeRead007.headerFinish_access rom heapWords _ (by omega))
  simpa only [leafReadProgram] using hall

theorem leafRead_actual_prefix_heap {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + leafReadProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < leafReadProgram.length), containing[origin + i]'(by omega) = leafReadProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ 48) : (packingRun rom containing clock state).heap = state.heap := by
  rw [PA17A19RuntimeRanks008.straight_prefix rom containing leafReadProgram origin hbound hcode leafReadProgram_straight hw hpc state hp ha clock
    (by simpa only [leafReadProgram_length] using hc)]
  exact leafReadProgram_prefix_heap rom state clock

theorem leafRead_actual_decoded {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (containing : List PackingOp) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (hbound : origin + leafReadProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < leafReadProgram.length), containing[origin + i]'(by omega) = leafReadProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 48) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
  have hcl : clock < leafReadProgram.length := by rwa [leafReadProgram_length]
  exact decoded_of_phase (callInput q full command) containing leafReadProgram origin heapWords hbound hcode hw hpc state ha clock hcl
    (PA17A19RuntimeRanks008.straight_prefix _ containing leafReadProgram origin hbound hcode leafReadProgram_straight hw hpc state hp ha clock hcl.le)
    (PA17A19RuntimeRanks008.prefix_pc _ leafReadProgram origin leafReadProgram_straight state hp clock hcl.le)
    (leafReadProgram_access layout command configuration state node rep hi clock hcl)

theorem leafRead_active_exit {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + leafReadProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < leafReadProgram.length), containing[origin + i]'(by omega) = leafReadProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    (packingRun rom containing 48 state).halted = false ∧
      (packingRun rom containing 48 state).pc = BitVec.ofNat bits (5 * (origin + 48)) := by
  rw [leafRead_actual rom containing origin hbound hcode hw hpc state hp ha]
  refine ⟨by rw [executeOps_halted, ha], ?_⟩
  rw [executeOps_pc rom leafReadProgram state leafReadProgram_straight, hp, leafReadProgram_length, BitVec.ofNat_add_ofNat]
  congr 1

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
