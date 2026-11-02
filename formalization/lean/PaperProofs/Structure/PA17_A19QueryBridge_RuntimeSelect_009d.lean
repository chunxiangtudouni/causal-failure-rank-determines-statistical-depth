module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009c

/-! Every fetched clear-phase instruction has actual ROM/heap access bounds.
The complete heap frame excludes exactly the candidate cells being cleared. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def ClearProtected {bits : Nat} (base count : Nat) (address : BitVec bits) : Prop :=
  ∀ i < count, address ≠ BitVec.ofNat bits (base + i)

def ClearPoint {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (heapWords base count : Nat)
    (state : WordState bits) : Prop :=
  state.halted = false ∧ ∃ index : Nat, ∃ hi : index < containing.length,
    state.pc.toNat = 5 * index ∧
    physicalFetch bits (packingCode containing) state.pc.toNat = containing[index].encode ∧
    packingAccessFits rom heapWords state containing[index] ∧
    ∀ address, ClearProtected base count address →
      (packingExecuteOp rom containing[index] state).heap address = state.heap address

theorem clearSetup_noStore : ∀ op ∈ clearSetup, HeapPreservingOp op := by
  simp [clearSetup, HeapPreservingOp]

theorem clearTest_noStore (origin : Nat) : ∀ op ∈ clearTest origin, HeapPreservingOp op := by
  simp [clearTest, clearTestLead, HeapPreservingOp]

theorem clear_setup_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hinput : 1 < rom.input.length) (hheap : 0 < heapWords)
    (count : Nat) (hc : count < clearSetup.length) :
    packingAccessFits rom heapWords (executeOps rom (clearSetup.take count) state) clearSetup[count] := by
  change count < 14 at hc
  interval_cases count <;>
    simp_all +decide [clearSetup, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits,
      AccessFits, PhysicalROM.words, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]

theorem clear_test_access {bits : Nat} (rom : PhysicalROM) (origin heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < (clearTest origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((clearTest origin).take count) state) (clearTest origin)[count] := by
  change count < 2 at hc
  interval_cases count <;> trivial

theorem clear_body_access {bits : Nat} (rom : PhysicalROM) (origin pointer heapWords : Nat) (state : WordState bits)
    (hi : state.register .index = BitVec.ofNat bits pointer) (halloc : pointer < heapWords)
    (count : Nat) (hc : count < (clearBody origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((clearBody origin).take count) state) (clearBody origin)[count] := by
  change count < 5 at hc
  interval_cases count <;> try exact True.intro
  change (state.register .index).toNat < heapWords
  rw [hi, BitVec.toNat_ofNat]
  exact (Nat.mod_le _ _).trans_lt halloc

theorem clear_body_frame {bits : Nat} (rom : PhysicalROM) (origin base done total : Nat) (state : WordState bits)
    (hi : state.register .index = BitVec.ofNat bits (base + done)) (hd : done < total)
    (address : BitVec bits) (hprotect : ClearProtected base total address)
    (count : Nat) (hc : count < (clearBody origin).length) :
    (packingExecuteOp rom (clearBody origin)[count] (executeOps rom ((clearBody origin).take count) state)).heap address =
      (executeOps rom ((clearBody origin).take count) state).heap address := by
  by_cases hz : count = 0
  · subst count
    have hn := hprotect done hd
    change Function.update state.heap (state.register .index) (state.register .value) address = state.heap address
    rw [hi]
    exact Function.update_of_ne hn _ _
  · have hn : HeapPreservingOp (clearBody origin)[count] := by
      change count < 5 at hc
      interval_cases count <;> simp_all [clearBody, clearBodyLead, HeapPreservingOp]
    exact congrFun (PA17A19RuntimeRanks008.preserving_step_heap rom (clearBody origin)[count] _ hn) address

theorem clear_point_of_phase {bits : Nat} (rom : PhysicalROM) (containing block : List PackingOp)
    (start heapWords base total : Nat) (hbound : start + block.length ≤ containing.length)
    (hcode : ∀ i (hi : i < block.length), containing[start + i]'(by omega) = block[i])
    (hw : WordsFit bits (packingCode containing)) (hpcf : Fits bits (5 * containing.length))
    (state : WordState bits) (ha : state.halted = false) (count : Nat) (hc : count < block.length)
    (hrun : packingRun rom containing count state = executeOps rom (block.take count) state)
    (hp : (executeOps rom (block.take count) state).pc = BitVec.ofNat bits (5 * (start + count)))
    (haccess : packingAccessFits rom heapWords (executeOps rom (block.take count) state) block[count])
    (hframe : ∀ address, ClearProtected base total address →
      (packingExecuteOp rom block[count] (executeOps rom (block.take count) state)).heap address =
        (executeOps rom (block.take count) state).heap address) :
    ClearPoint rom containing heapWords base total (packingRun rom containing count state) := by
  have hi : start + count < containing.length := by omega
  have hpNat : (executeOps rom (block.take count) state).pc.toNat = 5 * (start + count) := by
    rw [hp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hi.le).trans_lt hpcf)
  rw [hrun]
  refine ⟨by rw [executeOps_halted, ha], start + count, hi, hpNat, ?_, ?_, ?_⟩
  · rw [hpNat, physicalFetch_eq bits (packingCode containing) _ hw]
    change natFetch containing (5 * (start + count)) = containing[start + count].encode
    exact natFetch_body containing (start + count) hi
  · rw [hcode count hc]
    exact haccess
  · rw [hcode count hc]
    exact hframe

theorem clear_setup_point {bits origin : Nat} {containing : List PackingOp} (em : ClearEmbedded bits origin containing)
    (rom : PhysicalROM) (heapWords base total : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hinput : 1 < rom.input.length) (hheap : 0 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count < 14) : ClearPoint rom containing heapWords base total (packingRun rom containing count state) := by
  have hb : origin + clearSetup.length ≤ containing.length := by
    have hh := em.bound; rw [clearProgramAt_length, clearSetup_length] at *; omega
  have hcount : count < clearSetup.length := by rwa [clearSetup_length]
  apply clear_point_of_phase rom containing clearSetup origin heapWords base total hb (clear_setup_code em) em.words em.pcfit
    state ha count hcount
    (PA17A19RuntimeRanks008.straight_prefix rom containing clearSetup origin hb (clear_setup_code em) clearSetup_straight
      em.words em.pcfit state hp ha count hcount.le)
    (PA17A19RuntimeRanks008.prefix_pc rom clearSetup origin clearSetup_straight state hp count hcount.le)
    (clear_setup_access rom heapWords state h1 hinput hheap count hcount)
  intro address _
  exact congrFun (PA17A19RuntimeRanks008.preserving_step_heap rom clearSetup[count] _
    (clearSetup_noStore _ (List.getElem_mem hcount))) address

theorem clear_test_point {bits origin : Nat} {containing : List PackingOp} (em : ClearEmbedded bits origin containing)
    (rom : PhysicalROM) (heapWords base total : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 14))) (ha : state.halted = false)
    (count : Nat) (hc : count < 2) : ClearPoint rom containing heapWords base total (packingRun rom containing count state) := by
  have hb : origin + 14 + (clearTest origin).length ≤ containing.length := by
    have hh := em.bound; rw [clearProgramAt_length, clearTest_length] at *; omega
  have hcount : count < (clearTest origin).length := by rwa [clearTest_length]
  refine clear_point_of_phase rom containing (clearTest origin) (origin + 14) heapWords base total hb (clear_test_code em)
    em.words em.pcfit state ha count hcount
    (PA17A19RuntimeRanks008.last_prefix rom containing (clearTestLead origin) (.jumpIfZero .total .old) (origin + 14) hb
      (clear_test_code em) (clearTestLead_straight origin) em.words em.pcfit state hp ha count (by rw [clearTestLead_length]; omega))
    ?_ (clear_test_access rom origin heapWords state count hcount) ?_
  · rw [clearTest, List.take_append_of_le_length (show count ≤ (clearTestLead origin).length by rw [clearTestLead_length]; omega)]
    exact PA17A19RuntimeRanks008.prefix_pc rom (clearTestLead origin) (origin + 14) (clearTestLead_straight origin) state hp count
      (by rw [clearTestLead_length]; omega)
  · intro address _
    exact congrFun (PA17A19RuntimeRanks008.preserving_step_heap rom (clearTest origin)[count] _
      (clearTest_noStore origin _ (List.getElem_mem hcount))) address

theorem clear_body_point {bits origin : Nat} {containing : List PackingOp} (em : ClearEmbedded bits origin containing)
    (rom : PhysicalROM) (heapWords base done total : Nat) (state : WordState bits)
    (hi : state.register .index = BitVec.ofNat bits (base + done)) (hd : done < total) (halloc : base + total ≤ heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 16))) (ha : state.halted = false)
    (count : Nat) (hc : count < 5) : ClearPoint rom containing heapWords base total (packingRun rom containing count state) := by
  have hb : origin + 16 + (clearBody origin).length ≤ containing.length := by
    have hh := em.bound; rw [clearProgramAt_length, clearBody_length] at *; omega
  have hcount : count < (clearBody origin).length := by rwa [clearBody_length]
  refine clear_point_of_phase rom containing (clearBody origin) (origin + 16) heapWords base total hb (clear_body_code em)
    em.words em.pcfit state ha count hcount
    (PA17A19RuntimeRanks008.last_prefix rom containing (clearBodyLead origin) (.jumpIfZero .value .old) (origin + 16) hb
      (clear_body_code em) (clearBodyLead_straight origin) em.words em.pcfit state hp ha count (by rw [clearBodyLead_length]; omega))
    ?_ (clear_body_access rom origin (base + done) heapWords state hi (by omega) count hcount)
    (fun address hprotect => clear_body_frame rom origin base done total state hi hd address hprotect count hcount)
  rw [clearBody, List.take_append_of_le_length (show count ≤ (clearBodyLead origin).length by rw [clearBodyLead_length]; omega)]
  exact PA17A19RuntimeRanks008.prefix_pc rom (clearBodyLead origin) (origin + 16) (clearBodyLead_straight origin) state hp count
    (by rw [clearBodyLead_length]; omega)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
