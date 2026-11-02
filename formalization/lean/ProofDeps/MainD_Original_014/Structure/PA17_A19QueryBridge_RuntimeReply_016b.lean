module

public import Structure.PA17_A19QueryBridge_RuntimeReply_016a

/-! The literal reply footer in the same containing Word run. All loads are
checked against actual allocation; all prefix heaps are exactly unchanged. -/

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReply016

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRWordSegments

theorem access_prefix {bits : Nat} (rom : PhysicalROM)
    (workspace size q heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (PSTRQueryLayout.endpoint workspace size q))
    (halloc : PSTRQueryLayout.endpoint workspace size q ≤ heapWords)
    (hinput : 1 < rom.input.length)
    (hq : (rom.words .input).getD 1 0 = q)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size)) :
    ∀ count (hc : count < program.length), packingAccessFits rom heapWords
      (executeOps rom (program.take count) state) program[count] := by
  have h1 : Fits bits 1 := by
    apply (show 1 < PSTRQueryLayout.endpoint workspace size q from ?_).trans hroom
    unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags
      PSTRQueryLayout.goodFlags
    omega
  have ht : PSTRQueryLayout.header workspace size + (q + (2 + (q + (2 + (size + 18))))) =
      PSTRQueryLayout.childBase workspace size q + (size + 2) := by
    unfold PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega
  have htNat : (BitVec.ofNat bits (PSTRQueryLayout.childBase workspace size q + (size + 2))).toNat =
      PSTRQueryLayout.childBase workspace size q + (size + 2) := by
    apply Nat.mod_eq_of_lt
    apply (show PSTRQueryLayout.childBase workspace size q + (size + 2) <
      PSTRQueryLayout.endpoint workspace size q from ?_).trans hroom
    unfold PSTRQueryLayout.endpoint
    omega
  have hsizeWord : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) hsize
  intro count hc
  change count < 32 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [program, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingExecuteOp,
    wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    packingAccessFits, AccessFits, hh, hsizeWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h1, Nat.zero_mod, hq, BitVec.ofNat_add_ofNat,
    Nat.add_assoc, ht, htNat]
  all_goals try exact hinput
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals simp only [PSTRQueryLayout.endpoint, PSTRQueryLayout.childBase,
    PSTRQueryLayout.badFlags, PSTRQueryLayout.goodFlags] at halloc ⊢
  all_goals omega

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
    (count : Nat) (hc : count ≤ 32) :
    (packingRun rom containing count state).heap = state.heap := by
  rw [actual_prefix em rom state hp ha count (by simpa only [program_length] using hc)]
  exact prefix_heap rom state count

theorem actual_reply {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM)
    (workspace size q good bad : Nat) (state : WordState bits)
    (hroom : Fits bits (PSTRQueryLayout.endpoint workspace size q))
    (hq : (rom.words .input).getD 1 0 = q)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hgood : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 4)) =
      BitVec.ofNat bits good)
    (hbad : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 5)) =
      BitVec.ofNat bits bad)
    (hg : good ≤ q + 2) (hb : bad ≤ q + 2)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let header := PSTRQueryLayout.header workspace size
    let active := (state.heap (BitVec.ofNat bits (header + 2))).toNat
    let enabled := (state.heap (BitVec.ofNat bits (header + 7))).toNat
    let after := packingRun rom containing 32 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 32)) ∧
    after.register .address = BitVec.ofNat bits header ∧
    after.register .old = BitVec.ofNat bits (if active = 0 then q + 2 else good) ∧
    after.register .fresh = BitVec.ofNat bits (if active = 0 then 0 else bad) ∧
    after.register .value = BitVec.ofNat bits
      (if active = 0 then q + 2 else min good (bad + 1)) ∧
    after.register .index = (if enabled = 0 then BitVec.ofNat bits 0 else
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase workspace size q + size + 2))) ∧
    after.heap = state.heap := by
  have run := straight_segment rom containing program origin em.bound em.code program_straight
    em.words em.pcfit state hp ha
  rw [program_length] at run
  have result := execute_result rom workspace size q good bad state hroom hq hsize hh hgood hbad hg hb
  dsimp only at result ⊢
  rw [run]
  refine ⟨(executeOps_halted _ _ _).trans ha, ?_, result.1, result.2.1,
    result.2.2.1, result.2.2.2.1, result.2.2.2.2.1, result.2.2.2.2.2.1⟩
  rw [executeOps_pc _ _ state program_straight, hp, program_length, BitVec.ofNat_add_ofNat]
  congr 1

theorem actual_prefix_decoded {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM)
    (workspace size q heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (PSTRQueryLayout.endpoint workspace size q))
    (halloc : PSTRQueryLayout.endpoint workspace size q ≤ heapWords)
    (hinput : 1 < rom.input.length) (hq : (rom.words .input).getD 1 0 = q)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count < 32) :
    let before := packingRun rom containing count state
    before.halted = false ∧ Fits bits (before.pc.toNat + 4) ∧
      before.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (physicalFetch bits (packingCode containing) before.pc.toNat) = some op ∧
        packingAccessFits rom heapWords before op := by
  have hcount : count < program.length := by simpa only [program_length] using hc
  have hindex : origin + count < containing.length := by have := em.bound; omega
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
    exact access_prefix rom workspace size q heapWords state hroom halloc hinput hq hsize hh count hcount

theorem original_prefix_represents {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 32) :
    HeapRepresents q full capWords configuration
      (packingRun (callInput q full command) containing count state).heap := by
  rw [actual_prefix_heap em _ state hp ha count hc]
  exact rep

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReply016
