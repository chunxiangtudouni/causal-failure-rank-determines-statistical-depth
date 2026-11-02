module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRead_007a

/-! Actual containing-program fetch, access, full-prefix heap frame and ACTIVE
exit for the fixed table reader. Each scalar bound is derived from the
original packed capacity region and the allocated workspace. -/

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRWordSegments

theorem access_append {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (left right : List PackingOp) (state : WordState bits)
    (hl : ∀ count (hc : count < left.length),
      packingAccessFits rom heapWords (executeOps rom (left.take count) state) left[count])
    (hr : ∀ count (hc : count < right.length), packingAccessFits rom heapWords
      (executeOps rom (right.take count) (executeOps rom left state)) right[count]) :
    ∀ count (hc : count < (left ++ right).length),
      packingAccessFits rom heapWords (executeOps rom ((left ++ right).take count) state)
        (left ++ right)[count] := by
  intro count hc
  by_cases hleft : count < left.length
  · rw [List.take_append_of_le_length hleft.le, List.getElem_append_left hleft]
    exact hl count hleft
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
    have he : extra < right.length := by rw [List.length_append] at hc; omega
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      executeOps_append, List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using hr extra he

theorem headerFinish_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (state : WordState bits) (hh : 0 < heapWords) :
    ∀ count (hc : count < headerFinish.length), packingAccessFits rom heapWords
      (executeOps rom (headerFinish.take count) state) headerFinish[count] := by
  intro count hc
  change count < 7 at hc
  interval_cases count <;>
    simp [headerFinish, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, hh]

theorem access_prefix {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .address).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q)) :
    ∀ count (hc : count < program.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (program.take count) state) program[count] := by
  let rom := callInput q full command
  have hbounds := read_room full capWords heapWords (state.register .address).toNat
    (by omega) hscalar hs hf halloc
  have hl := PSTRRuntimePackedReadSafety.access_prefix rom state heapWords hb hw
    hwidth rep.2.2.2.1 hbounds.1 hbounds.2.1 hbounds.2.2
  let middle := executeOps rom PSTRRuntimePackedRead.program state
  have hheap : middle.heap = state.heap := PSTRRuntimePackedRead.execute_heap rom state
  have hrep : HeapRepresents q full capWords configuration middle.heap := by rw [hheap]; exact rep
  have hbase : PSTRCountWorkspace.base q full capWords bits =
      PSTRQueryLayout.physicalWorkspace full capWords bits :=
    PSTRCountWorkspace.base_metadata_end q full hq capWords bits
  have hm := PSTRCountWorkspace.prefix_access full command configuration capWords heapWords
    middle hrep (by rw [hbase]; exact halloc) hb
  have hpositive : 0 < heapWords := by
    unfold PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress physicalHeaderWords at halloc
    omega
  exact access_append rom heapWords _ _ state (access_append rom heapWords _ _ state hl hm)
    (headerFinish_access rom heapWords _ hpositive)

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

theorem actual_prefix_heap {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 43) :
    (packingRun rom containing count state).heap = state.heap := by
  rw [actual_prefix em rom state hp ha count (by simpa only [program_length] using hc)]
  exact prefix_heap rom state count

theorem actual_read {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .address).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) containing 43 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 43)) ∧
    after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) ∧
    (after.register .value).toNat = logicalHeap q capWords state.heap (state.register .address).toNat ∧
    after.heap = state.heap := by
  have hr := execute_result full command configuration capWords heapWords state hb hq hw rep
    hscalar hs hf halloc hwidth hmask
  have run := straight_segment (callInput q full command) containing program origin
    em.bound em.code program_straight em.words em.pcfit state hp ha
  rw [program_length] at run
  dsimp only
  rw [run]
  refine ⟨(executeOps_halted _ _ _).trans ha, ?_, hr.1, hr.2.1, hr.2.2.1⟩
  rw [executeOps_pc _ _ state program_straight, hp, program_length, BitVec.ofNat_add_ofNat]
  congr 1

theorem actual_prefix_decoded {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .address).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count < 43) :
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
    exact access_prefix full command configuration capWords heapWords state hb hq hw rep
      hscalar hs hf halloc hwidth count hcount

theorem inline_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (state : WordState bits) :
    (packingDynamicTrace rom containing 43 state).length ≤ 516 :=
  packingDynamicTrace_length_le rom containing 43 state

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007
