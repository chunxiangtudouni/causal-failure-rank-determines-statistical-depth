module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRead_007c

/-! Complete fetched-prefix safety and ACTIVE return for the fixed58op
cached table reader. Width/mask are actual heap cache words, reloaded by
the program; no initial width/mask register or all-prefix safety is assumed. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRWordSegments

theorem cacheLoad_access {bits : Nat} (rom : PhysicalROM) (workspace size heapWords : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hf : Fits bits heapWords)
    (hheader : PSTRQueryLayout.header workspace size < heapWords)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size)) :
    ∀ count (hc : count < cacheLoad.length), packingAccessFits rom heapWords
      (executeOps rom (cacheLoad.take count) state) cacheLoad[count] := by
  have hsmall : 2 < 2 ^ bits := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    omega
  have hroom : Fits bits (PSTRQueryLayout.header workspace size) := hheader.trans hf
  have hmul : Fits bits (size * 2 + 17) := by
    apply (show size * 2 + 17 ≤ PSTRQueryLayout.header workspace size from ?_).trans_lt hroom
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hdiff : PSTRQueryLayout.header workspace size - (size * 2 + 17) = workspace := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have h12 : workspace + 12 < heapWords := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase at hheader
    omega
  have h13 : workspace + 13 < heapWords := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase at hheader
    omega
  have he : workspace + 12 + 1 = workspace + 13 := by omega
  intro count hc
  change count < 15 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [cacheLoad, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingExecuteOp,
    wordOp, wordInstruction, packingArithmetic, Function.update_apply, ↓reduceIte,
    packingAccessFits, AccessFits, hsize, hh, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hsmall, Nat.zero_mod, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hroom,
    Nat.mod_eq_of_lt hmul, hdiff, he, Nat.mod_eq_of_lt (h12.trans hf),
    Nat.mod_eq_of_lt (h13.trans hf)]
  all_goals omega

theorem cached_access_prefix {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .value).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hheader : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) :
    ∀ count (hc : count < cachedProgram.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (cachedProgram.take count) state) cachedProgram[count] := by
  let rom := callInput q full command
  let loaded := executeOps rom cacheLoad state
  have hl := cacheLoad_result rom (PSTRQueryLayout.physicalWorkspace full capWords bits)
    (treeSize q full) state hb (hheader.trans hf) rep.1 hh
  have hrep : HeapRepresents q full capWords configuration loaded.heap := by rw [hl.2.2.2.2]; exact rep
  have halloc : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase at hheader
    omega
  apply access_append rom heapWords cacheLoad program state
    (cacheLoad_access rom _ _ heapWords state hb hf hheader rep.1 hh)
  exact access_prefix full command configuration capWords heapWords loaded hb hq hw hrep
    (by rw [hl.1]; exact hscalar) hs hf halloc (hl.2.2.1.trans hwidth)

structure CachedEmbedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + cachedProgram.length ≤ containing.length
  code : ∀ i (hi : i < cachedProgram.length), containing[origin + i]'(by omega) = cachedProgram[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem cached_actual_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : CachedEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ cachedProgram.length) :
    packingRun rom containing count state = executeOps rom (cachedProgram.take count) state := by
  have hl : (cachedProgram.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply straight_segment rom containing (cachedProgram.take count) origin (by have := em.bound; omega)
    ?_ ?_ em.words em.pcfit state hp ha
  · intro i hi
    have hi' : i < cachedProgram.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using em.code i hi'
  · intro op ho
    exact cachedProgram_straight op (List.mem_of_mem_take ho)

theorem cached_actual_prefix_heap {bits origin : Nat} {containing : List PackingOp}
    (em : CachedEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 58) :
    (packingRun rom containing count state).heap = state.heap := by
  rw [cached_actual_prefix em rom state hp ha count (by simpa only [cachedProgram_length] using hc)]
  exact executeOps_heap_of_no_store rom _ state (by
    intro op ho
    exact cachedProgram_noStore op (List.mem_of_mem_take ho))

theorem actual_cached_read {bits q origin : Nat} {containing : List PackingOp}
    (em : CachedEmbedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .value).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hheader : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) containing 58 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 58)) ∧
    after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) ∧
    (after.register .value).toNat = logicalHeap q capWords state.heap (state.register .value).toNat ∧
    after.heap = state.heap := by
  have hr := execute_cached full command configuration capWords heapWords state hb hq hw rep
    hscalar hs hf hheader hwidth hmask hh
  have run := straight_segment (callInput q full command) containing cachedProgram origin
    em.bound em.code cachedProgram_straight em.words em.pcfit state hp ha
  rw [cachedProgram_length] at run
  dsimp only
  rw [run]
  refine ⟨(executeOps_halted _ _ _).trans ha, ?_, hr.1, hr.2.1, hr.2.2.1⟩
  rw [executeOps_pc _ _ state cachedProgram_straight, hp, cachedProgram_length, BitVec.ofNat_add_ofNat]
  congr 1

theorem cached_inline_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (state : WordState bits) :
    (packingDynamicTrace rom containing 58 state).length ≤ 696 :=
  packingDynamicTrace_length_le rom containing 58 state

theorem cached_actual_prefix_decoded {bits q origin : Nat} {containing : List PackingOp}
    (em : CachedEmbedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .value).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hheader : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count < 58) :
    let before := packingRun (callInput q full command) containing count state
    before.halted = false ∧ Fits bits (before.pc.toNat + 4) ∧
      before.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (physicalFetch bits (packingCode containing) before.pc.toNat) = some op ∧
        packingAccessFits (callInput q full command) heapWords before op := by
  have hcount : count < cachedProgram.length := by simpa only [cachedProgram_length] using hc
  have hindex : origin + count < containing.length := by have := em.bound; omega
  let rom := callInput q full command
  have hr := cached_actual_prefix em rom state hp ha count hcount.le
  have hpc : (packingRun rom containing count state).pc.toNat = 5 * (origin + count) := by
    rw [hr, executeOps_pc _ _ state (by
      intro op ho
      exact cachedProgram_straight op (List.mem_of_mem_take ho)), hp,
      List.length_take_of_le hcount.le, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    have he : 5 * origin + 5 * count = 5 * (origin + count) := by omega
    rw [he]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hindex.le).trans_lt em.pcfit)
  have hfetch : physicalFetch bits (packingCode containing)
      (packingRun rom containing count state).pc.toNat = cachedProgram[count].encode := by
    rw [hpc, physicalFetch_eq bits _ _ em.words]
    change natFetch containing (5 * (origin + count)) = _
    rw [natFetch_body containing (origin + count) hindex, em.code count hcount]
  have hsmall : (packingRun rom containing count state).pc.toNat + 4 < 5 * containing.length := by
    rw [hpc]
    omega
  refine ⟨?_, hsmall.trans em.pcfit, ?_, cachedProgram[count], ?_, ?_⟩
  · rw [hr, executeOps_halted, ha]
  · rw [packingCode_length]
    exact hsmall.trans_le (Nat.le_add_right _ _)
  · rw [hfetch, decode_encode]
  · rw [hr]
    exact cached_access_prefix full command configuration capWords heapWords state hb hq hw rep
      hscalar hs hf hheader hwidth hh count hcount

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007
