module

public import PaperProofs.Structure.PSTR_RuntimePackedReadSafety_010
public import PaperProofs.Structure.PSTR_HD_CountWorkspace_025
public import PaperProofs.Structure.PSTR_QueryLayout_041

/-! A fixed 43-op packed-table reader with a real query-header return.
Width/mask are the computed per-call cache values in ordinary entry registers;
the block does not rerun the width loop per table word. The original cached
metadata locator restores the header after the packed reader clobbers scratch.
No input dimension or word width appears as a code-generation parameter. -/

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def headerFinish : List PackingOp :=
  [.base (.base (.constant .total 0)), .base (.base (.loadHeap .flag .total)),
   .base (.base (.constant .total 2)), .arithmetic .multiply .flag .flag .total,
   .base (.base (.constant .total 17)), .base (.base (.add .flag .flag .total)),
   .base (.base (.add .address .address .flag))]

def program : List PackingOp :=
  PSTRRuntimePackedRead.program ++ PSTRCountWorkspace.program ++ headerFinish

theorem headerFinish_length : headerFinish.length = 7 := rfl
theorem program_length : program.length = 43 := rfl

theorem headerFinish_straight : StraightProgram headerFinish := by
  simp [headerFinish, StraightProgram, StraightOp]

theorem program_straight : StraightProgram program := by
  intro op ho
  simp only [program, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · exact PSTRRuntimePackedRead.program_straight op ho
  · exact PSTRCountWorkspace.program_straight op ho
  · exact headerFinish_straight op ho

theorem program_noStore : ∀ op ∈ program, HeapPreservingOp op := by
  simp [program, PSTRRuntimePackedRead.program, PSTRCountWorkspace.program,
    headerFinish, HeapPreservingOp]

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (program.take count) state).heap = state.heap :=
  executeOps_heap_of_no_store rom _ state (by
    intro op ho
    exact program_noStore op (List.mem_of_mem_take ho))

theorem execute_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom program state).heap = state.heap := by
  simpa only [List.take_length] using prefix_heap rom state program.length

theorem headerFinish_value {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom headerFinish state).register .value = state.register .value := rfl

theorem headerFinish_address {bits : Nat} (rom : PhysicalROM) (workspace size : Nat)
    (state : WordState bits) (hb : 8 ≤ bits)
    (hh : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hw : state.register .address = BitVec.ofNat bits workspace) :
    (executeOps rom headerFinish state).register .address =
      BitVec.ofNat bits (PSTRQueryLayout.header workspace size) := by
  have htwo : 2 < 2 ^ bits := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    omega
  simp +decide only [headerFinish, executeOps, packingExecuteOp, wordOp,
    wordInstruction, packingArithmetic, Function.update_apply, ↓reduceIte,
    hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htwo, hh, BitVec.ofNat_add_ofNat]
  congr 1
  unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
  omega

/-- Scalar and lookahead bounds follow from the original packed region and
the actual allocated endpoint; no prefix-access certificate is assumed. -/
theorem read_room {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords heapWords scalar : Nat) (hb : 0 < bits)
    (ha : scalar < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits heapWords)
    (hw : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords) :
    Fits bits (scalar * CapacityBits.width q) ∧
      Fits bits (4 + scalar * CapacityBits.width q / bits + 1) ∧
      4 + scalar * CapacityBits.width q / bits + 1 < heapWords := by
  have hp : scalar * CapacityBits.width q ≤ capWords * CapacityBits.width q :=
    Nat.mul_le_mul_right _ ha.le
  have hstart : Fits bits (scalar * CapacityBits.width q) :=
    (hp.trans (Nat.le_add_left _ 4)).trans_lt hs
  have hdiv : scalar * CapacityBits.width q / bits ≤ packedCapacityWords q capWords bits := by
    have hc := packedCapacityWords_mul_bits q capWords hb
    have hm : scalar * CapacityBits.width q <
        (packedCapacityWords q capWords bits + 1) * bits := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hd := (Nat.div_lt_iff_lt_mul hb).mpr hm
    omega
  have hlook : 4 + scalar * CapacityBits.width q / bits + 1 < heapWords := by
    unfold PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress physicalHeaderWords at hw
    omega
  exact ⟨hstart, hlook.trans hf, hlook⟩

theorem execute_result {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .address).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q)) :
    let after := executeOps (callInput q full command) program state
    after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) ∧
    (after.register .value).toNat = logicalHeap q capWords state.heap (state.register .address).toNat ∧
    after.heap = state.heap ∧ after.halted = state.halted := by
  let rom := callInput q full command
  let read := executeOps rom PSTRRuntimePackedRead.program state
  let located := executeOps rom PSTRCountWorkspace.program read
  have hbounds := read_room full capWords heapWords (state.register .address).toNat
    (by omega) hscalar hs hf halloc
  have hread := PSTRRuntimePackedRead.execute_capacity rom state hq (by omega) hw
    hwidth hmask rep.2.2.2.1 capWords hscalar hbounds.1 hbounds.2.1
  have hreadHeap : read.heap = state.heap := PSTRRuntimePackedRead.execute_heap rom state
  have hreadRep : HeapRepresents q full capWords configuration read.heap := by
    rw [hreadHeap]
    exact rep
  have hl := PSTRCountWorkspace.execute_base full command configuration capWords read hb hq hreadRep
  have hlHeap : located.heap = state.heap := hl.2.2.2.2.2.1.trans hreadHeap
  have hbase : PSTRCountWorkspace.base q full capWords bits =
      PSTRQueryLayout.physicalWorkspace full capWords bits :=
    PSTRCountWorkspace.base_metadata_end q full hq capWords bits
  have hfinish := headerFinish_address rom
    (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) located hb
    (by rw [hlHeap]; exact rep.1) (hl.1.trans (congrArg (BitVec.ofNat bits) hbase))
  dsimp only
  refine ⟨?_, ?_, execute_heap rom state, executeOps_halted rom program state⟩
  · simpa only [program, executeOps_append, located, read, rom] using hfinish
  · change ((executeOps rom headerFinish located).register .value).toNat = _
    rw [headerFinish_value, hl.2.1]
    exact hread

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007
