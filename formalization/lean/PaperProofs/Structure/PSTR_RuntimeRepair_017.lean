module

public import PaperProofs.Structure.PSTR_AdvanceHeap_016
public import PaperProofs.Structure.PSTR_Callback_001

/-! One genuine contiguous physical repair block: set the selected unused
tool bit, then advance the stored stage. There is exactly one final HALT;
this is not a composition that restarts separately halted helper runs. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeRepair

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def program : List PackingOp := PSTRRuntimeMarkUsed.program ++ PSTRRuntimeAdvance.program

theorem program_length : program.length = 21 := rfl

theorem program_straight : StraightProgram program := by
  intro op ho
  rcases List.mem_append.mp ho with hm | ha
  · exact PSTRRuntimeMarkUsed.program_straight op hm
  · exact PSTRRuntimeAdvance.program_straight op ha

theorem code_length : (packingCode program).length = 110 := by
  rw [packingCode_length, program_length]

theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, PSTRRuntimeMarkUsed.program, PSTRRuntimeAdvance.program,
    PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word,
    Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 105 < 2 ^ bits
  omega

theorem execute_represents {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q)) :
    HeapRepresents q full capWords
      { configuration with stage := configuration.stage + 1, used := insert tool configuration.used }
      (executeOps rom program state).heap := by
  have haddr : (state.register .address).toNat < capWords := by
    rw [haddress]
    have ht := tool.isLt
    omega
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q) :=
    (Nat.mul_lt_mul_of_pos_right haddr hwp).trans
      ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt hr)
  let middle := executeOps rom PSTRRuntimeMarkUsed.program state
  have hmheap : middle.heap = PSTRRuntimeMarkUsed.markHeap
      ((tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q) state.heap := by
    dsimp only [middle]
    rw [PSTRRuntimeMarkUsed.execute_heap rom state (by omega) hw hwidth rep.2.2.2.1 hstart,
      haddress]
  have hmrep : HeapRepresents q full capWords
      { configuration with used := insert tool configuration.used } middle.heap := by
    rw [hmheap]
    exact PSTRMarkUsedHeap.heapRepresents_insert full configuration capWords state.heap tool
      hb hq rep unused bitmap hr hi
  rw [program, executeOps_append,
    PSTRRuntimeAdvance.execute_heap rom middle (packedCapacityWords q capWords bits) hmrep.2.2.1]
  exact PSTRAdvanceHeap.heapRepresents_advance full
    { configuration with used := insert tool configuration.used } capWords middle.heap
    hb hq hmrep bitmap hr hi hnext

theorem actual_repair {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 22 state
    after.halted = true ∧ HeapRepresents q full capWords
      { configuration with stage := configuration.stage + 1, used := insert tool configuration.used }
      after.heap := by
  dsimp only
  rw [show 22 = program.length + 1 from rfl,
    packingRun_executeOps_halt rom _ _ program_straight (code_fit hb) (pc_fit hb) hp ha]
  exact ⟨rfl, execute_represents rom full configuration capWords state tool hb hq hw rep unused
    bitmap hr hi hnext haddress hwidth⟩

theorem actual_error {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits) (tool : Fin q)
    (hlaminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (hchoose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩
      configuration.used).tool = some tool)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 22 state
    after.halted = true ∧ HeapRepresents q full capWords
      (nextConfiguration q full configuration .error) after.heap := by
  have unused : tool ∉ configuration.used :=
    ((PSTRCallback.callback_stage q full hlaminar ⟨configuration.stage, allowed.2⟩
      configuration.used).2.2.2 tool hchoose).2.1
  have hc : nextConfiguration q full configuration .error =
      { configuration with stage := configuration.stage + 1, used := insert tool configuration.used } := by
    have hs : configuration.stage < full.length + 1 := by have hh := allowed.2; omega
    simp only [nextConfiguration, hs, dite_true, hchoose]
    have hf := allowed.1
    cases configuration
    simp_all only
  rw [hc]
  exact actual_repair rom full configuration capWords state tool hb hq hw rep unused
    bitmap hr hi hnext haddress hwidth hp ha

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (packingDynamicTrace rom program 22 state).length ≤ 264 :=
  packingDynamicTrace_length_le rom program 22 state

end PaperProofs.Structure.LaminarTree.PSTRRuntimeRepair
