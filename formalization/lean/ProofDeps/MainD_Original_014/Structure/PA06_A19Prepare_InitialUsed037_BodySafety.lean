module

public import Structure.PA06_A19Prepare_InitialUsed037_Body
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate exact88-op prefix safety from real read/write/advance blocks.
The loop invariant must discharge these internal pointer/source facts. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
open AlgorithmClaims.PackedCapacityRAM
open PA17PackedTranslator034 (PackedAccessSafe)

variable {bits : Nat}

private theorem prefixHeap_append (pred : (BitVec bits → BitVec bits) → Prop)
    (rom : PhysicalROM) (left right : List PackingOp) (state : WordState bits)
    (hl : ∀ count ≤ left.length, pred (executeOps rom (left.take count) state).heap)
    (hr : ∀ count ≤ right.length,
      pred (executeOps rom (right.take count) (executeOps rom left state)).heap) :
    ∀ count ≤ (left ++ right).length, pred (executeOps rom ((left ++ right).take count) state).heap := by
  intro count hc
  by_cases hleft : count ≤ left.length
  · rw [List.take_append_of_le_length hleft]
    exact hl count hleft
  · have hn : left.length ≤ count := by omega
    rw [List.take_append, List.take_of_length_le hn, executeOps_append]
    exact hr (count - left.length) (by simp only [List.length_append] at hc; omega)

theorem body_accessSafe (q C H : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hphysical : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1 < H)
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hroom16 : (state.register .address).toNat + pointerSlot < H)
    (hfit17 : Fits bits ((state.register .address).toNat + cursorSlot))
    (hroom17 : (state.register .address).toNat + cursorSlot < H)
    (hrom : (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat < (rom.words .input).length) :
    PackedAccessSafe H rom body state := by
  let loaded := executeOps rom readUsed state
  let written := executeOps rom (PA06A19PrepareBankPacked021.safeWrite pointerSlot) loaded
  let advanced := executeOps rom (advance pointerSlot) written
  have hloadedH : loaded.heap = state.heap := readUsed_heap rom state
  have hloadedA : loaded.register .address = state.register .address := readUsed_address rom state
  have hloadedP : PA06A19PrepareBankPacked021.pointer pointerSlot loaded =
      PA06A19PrepareBankPacked021.pointer pointerSlot state := by
    unfold PA06A19PrepareBankPacked021.pointer
    rw [hloadedH, hloadedA]
  have hwriteA : written.register .address = state.register .address :=
    (PA06A19PrepareBankPacked021.safeWrite_address pointerSlot rom loaded).trans hloadedA
  have hadvanceA : advanced.register .address = state.register .address :=
    (advance_address pointerSlot rom written).trans hwriteA
  have hread := readUsed_accessSafe rom H state hfit17 hroom17 hrom
  have hwrite := PA06A19PrepareBankPacked021.safeWrite_accessSafe q C pointerSlot H rom loaded
    (by rw [hloadedH]; exact hh) hq hb hw (by rw [hloadedP]; exact ha)
    (by rw [hloadedP]; exact hs) (by rw [hloadedP]; exact hf) (by rw [hloadedP]; exact hphysical)
    (by rw [hloadedA]; exact hbank) (by rw [hloadedA]; exact hfit16) (by rw [hloadedA]; exact hroom16)
  have hptr := advance_accessSafe pointerSlot rom H written
    (by rw [hwriteA]; exact hfit16) (by rw [hwriteA]; exact hroom16)
  have hcursor := advance_accessSafe cursorSlot rom H advanced
    (by rw [hadvanceA]; exact hfit17) (by rw [hadvanceA]; exact hroom17)
  have hfirst := PackedAccessSafe.append H rom readUsed (PA06A19PrepareBankPacked021.safeWrite pointerSlot) state hread hwrite
  have hsecond := PackedAccessSafe.append H rom _ (advance pointerSlot) state hfirst (by
    simpa only [executeOps_append, loaded, written] using hptr)
  exact PackedAccessSafe.append H rom _ (advance cursorSlot) state hsecond (by
    simpa only [executeOps_append, loaded, written, advanced] using hcursor)

theorem body_prefix_header (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hfit17 : Fits bits ((state.register .address).toNat + cursorSlot))
    (count : Nat) (hc : count ≤ 88) :
    PA06A19PrepareRuntimePacked016.Header q (executeOps rom (body.take count) state).heap := by
  let loaded := executeOps rom readUsed state
  let written := executeOps rom (PA06A19PrepareBankPacked021.safeWrite pointerSlot) loaded
  let advanced := executeOps rom (advance pointerSlot) written
  let pred : (BitVec bits → BitVec bits) → Prop := PA06A19PrepareRuntimePacked016.Header q
  have hloadedH : loaded.heap = state.heap := readUsed_heap rom state
  have hloadedA : loaded.register .address = state.register .address := readUsed_address rom state
  have hloadedP : PA06A19PrepareBankPacked021.pointer pointerSlot loaded =
      PA06A19PrepareBankPacked021.pointer pointerSlot state := by
    unfold PA06A19PrepareBankPacked021.pointer
    rw [hloadedH, hloadedA]
  have hwriteA : written.register .address = state.register .address :=
    (PA06A19PrepareBankPacked021.safeWrite_address pointerSlot rom loaded).trans hloadedA
  have hadvanceA : advanced.register .address = state.register .address :=
    (advance_address pointerSlot rom written).trans hwriteA
  have hread (n : Nat) (_hn : n ≤ readUsed.length) : pred (executeOps rom (readUsed.take n) state).heap := by
    rw [readUsed_prefix_heap]
    exact hh
  have hwrite (n : Nat) (hn : n ≤ (PA06A19PrepareBankPacked021.safeWrite pointerSlot).length) :
      pred (executeOps rom ((PA06A19PrepareBankPacked021.safeWrite pointerSlot).take n) loaded).heap := by
    exact PA06A19PrepareBankPacked021.safeWrite_prefix_header q C pointerSlot rom loaded
      (by rw [hloadedH]; exact hh) hq hb hw (by rw [hloadedP]; exact ha)
      (by rw [hloadedP]; exact hs) (by rw [hloadedP]; exact hf)
      (by rw [hloadedA]; exact hbank) (by rw [hloadedA]; exact hfit16) n
      (by simpa only [PA06A19PrepareBankPacked021.safeWrite_length] using hn)
  have hwritten : pred written.heap := by
    have hh' := hwrite 72 (by simpa only [PA06A19PrepareBankPacked021.safeWrite_length] using Nat.le_refl 72)
    have ht : (PA06A19PrepareBankPacked021.safeWrite pointerSlot).take 72 = PA06A19PrepareBankPacked021.safeWrite pointerSlot := by
      simpa only [PA06A19PrepareBankPacked021.safeWrite_length] using
        (List.take_length (l := PA06A19PrepareBankPacked021.safeWrite pointerSlot))
    simpa only [ht] using hh'
  have hafter16 : 4 ≤ (written.register .address).toNat + pointerSlot := by rw [hwriteA]; omega
  have hafter17 : 4 ≤ (advanced.register .address).toNat + cursorSlot := by
    rw [hadvanceA]
    dsimp only [pointerSlot, cursorSlot] at *
    omega
  have hptr (n : Nat) (hn : n ≤ (advance pointerSlot).length) :
      pred (executeOps rom ((advance pointerSlot).take n) written).heap :=
    advance_prefix_header q pointerSlot rom written hwritten hafter16
      (by rw [hwriteA]; exact hfit16) n (by simpa only [advance_length] using hn)
  have hadvanced : pred advanced.heap := by
    have hh' := hptr 6 (by simpa only [advance_length] using Nat.le_refl 6)
    have ht : (advance pointerSlot).take 6 = advance pointerSlot := by
      simpa only [advance_length] using (List.take_length (l := advance pointerSlot))
    simpa only [ht] using hh'
  have hcursor (n : Nat) (hn : n ≤ (advance cursorSlot).length) :
      pred (executeOps rom ((advance cursorSlot).take n) advanced).heap :=
    advance_prefix_header q cursorSlot rom advanced hadvanced hafter17
      (by rw [hadvanceA]; exact hfit17) n (by simpa only [advance_length] using hn)
  have hfirst := prefixHeap_append pred rom readUsed (PA06A19PrepareBankPacked021.safeWrite pointerSlot) state hread hwrite
  have hsecond := prefixHeap_append pred rom _ (advance pointerSlot) state hfirst (by
    simpa only [executeOps_append, loaded, written] using hptr)
  have hthird := prefixHeap_append pred rom _ (advance cursorSlot) state hsecond (by
    simpa only [executeOps_append, loaded, written, advanced] using hcursor)
  exact hthird count (by change count ≤ body.length; simpa only [body_length] using hc)

theorem body_prefix_capacity (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hfit17 : Fits bits ((state.register .address).toNat + cursorSlot))
    (hregion : Fits bits (C * CapacityBits.width q))
    (hvalue : ((executeOps rom readUsed state).register .value).toNat ≤ q)
    (hbound : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap state.heap)))
    (count : Nat) (hc : count ≤ 88) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap (executeOps rom (body.take count) state).heap)) := by
  let loaded := executeOps rom readUsed state
  let written := executeOps rom (PA06A19PrepareBankPacked021.safeWrite pointerSlot) loaded
  let advanced := executeOps rom (advance pointerSlot) written
  let pred : (BitVec bits → BitVec bits) → Prop := fun heap =>
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap heap))
  have hloadedH : loaded.heap = state.heap := readUsed_heap rom state
  have hloadedA : loaded.register .address = state.register .address := readUsed_address rom state
  have hloadedP : PA06A19PrepareBankPacked021.pointer pointerSlot loaded =
      PA06A19PrepareBankPacked021.pointer pointerSlot state := by
    unfold PA06A19PrepareBankPacked021.pointer
    rw [hloadedH, hloadedA]
  have hwriteA : written.register .address = state.register .address :=
    (PA06A19PrepareBankPacked021.safeWrite_address pointerSlot rom loaded).trans hloadedA
  have hadvanceA : advanced.register .address = state.register .address :=
    (advance_address pointerSlot rom written).trans hwriteA
  have hread (n : Nat) (_hn : n ≤ readUsed.length) : pred (executeOps rom (readUsed.take n) state).heap := by
    rw [readUsed_prefix_heap]
    exact hbound
  have hwrite (n : Nat) (hn : n ≤ (PA06A19PrepareBankPacked021.safeWrite pointerSlot).length) :
      pred (executeOps rom ((PA06A19PrepareBankPacked021.safeWrite pointerSlot).take n) loaded).heap := by
    exact PA06A19PrepareBankPacked021.safeWrite_prefix_capacityBounded q C pointerSlot rom loaded
      (by rw [hloadedH]; exact hh) hq hb hw (by rw [hloadedP]; exact ha)
      (by rw [hloadedP]; exact hs) (by rw [hloadedP]; exact hf)
      (by rw [hloadedA]; exact hbank) (by rw [hloadedA]; exact hfit16)
      hregion hvalue (by rw [hloadedH]; exact hbound) n
      (by simpa only [PA06A19PrepareBankPacked021.safeWrite_length] using hn)
  have hwritten : pred written.heap := by
    have hh' := hwrite 72 (by simpa only [PA06A19PrepareBankPacked021.safeWrite_length] using Nat.le_refl 72)
    have ht : (PA06A19PrepareBankPacked021.safeWrite pointerSlot).take 72 = PA06A19PrepareBankPacked021.safeWrite pointerSlot := by
      simpa only [PA06A19PrepareBankPacked021.safeWrite_length] using
        (List.take_length (l := PA06A19PrepareBankPacked021.safeWrite pointerSlot))
    simpa only [ht] using hh'
  have hafter16 : 4 + packedCapacityWords q C bits ≤ (written.register .address).toNat + pointerSlot := by rw [hwriteA]; omega
  have hafter17 : 4 + packedCapacityWords q C bits ≤ (advanced.register .address).toNat + cursorSlot := by
    rw [hadvanceA]
    dsimp only [pointerSlot, cursorSlot] at *
    omega
  have hptr (n : Nat) (hn : n ≤ (advance pointerSlot).length) :
      pred (executeOps rom ((advance pointerSlot).take n) written).heap := by
    intro other ho
    rw [advance_prefix_capacity q C pointerSlot rom written hb hregion hafter16
      (by rw [hwriteA]; exact hfit16) n (by simpa only [advance_length] using hn) other ho]
    exact hwritten other ho
  have hadvanced : pred advanced.heap := by
    have hh' := hptr 6 (by simpa only [advance_length] using Nat.le_refl 6)
    have ht : (advance pointerSlot).take 6 = advance pointerSlot := by
      simpa only [advance_length] using (List.take_length (l := advance pointerSlot))
    simpa only [ht] using hh'
  have hcursor (n : Nat) (hn : n ≤ (advance cursorSlot).length) :
      pred (executeOps rom ((advance cursorSlot).take n) advanced).heap := by
    intro other ho
    rw [advance_prefix_capacity q C cursorSlot rom advanced hb hregion hafter17
      (by rw [hadvanceA]; exact hfit17) n (by simpa only [advance_length] using hn) other ho]
    exact hadvanced other ho
  have hfirst := prefixHeap_append pred rom readUsed (PA06A19PrepareBankPacked021.safeWrite pointerSlot) state hread hwrite
  have hsecond := prefixHeap_append pred rom _ (advance pointerSlot) state hfirst (by
    simpa only [executeOps_append, loaded, written] using hptr)
  have hthird := prefixHeap_append pred rom _ (advance cursorSlot) state hsecond (by
    simpa only [executeOps_append, loaded, written, advanced] using hcursor)
  exact hthird count (by change count ≤ body.length; simpa only [body_length] using hc)

theorem body_prefix_run (rom : PhysicalROM) (left right : List PackingOp)
    (hcode : WordsFit bits (packingCode (left ++ body ++ right)))
    (hpcCode : Fits bits (5 * (left ++ body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 88) :
    packingRun rom (left ++ body ++ right) count state = executeOps rom (body.take count) state := by
  have hlen : (body.take count).length = count := List.length_take_of_le (by rw [body_length]; exact hc)
  conv_lhs => rw [← hlen]
  apply PSTRWordSegments.straight_segment rom (left ++ body ++ right) (body.take count) left.length
    (by simp only [List.length_append, body_length, hlen]; omega) ?_ ?_ hcode hpcCode state hpc ha
  · intro position hp
    have hpos : position < body.length := by rw [hlen] at hp; rw [body_length]; omega
    simpa only [List.getElem_take] using PA17UniformGenerator035a.segment_index left body right position hpos
  · intro op hop
    exact body_straight op (List.mem_of_mem_take hop)

theorem body_prefix_actual (q C H : Nat) (rom : PhysicalROM) (left right : List PackingOp)
    (hcode : WordsFit bits (packingCode (left ++ body ++ right)))
    (hpcCode : Fits bits (5 * (left ++ body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (hactive : state.halted = false)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hphysical : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1 < H)
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hroom16 : (state.register .address).toNat + pointerSlot < H)
    (hfit17 : Fits bits ((state.register .address).toNat + cursorSlot))
    (hroom17 : (state.register .address).toNat + cursorSlot < H)
    (hrom : (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat < (rom.words .input).length)
    (count : Nat) (hc : count < 88) :
    let code := left ++ body ++ right
    let actual := packingRun rom code count state
    actual.halted = false ∧ actual.pc.toNat = 5 * (left.length + count) ∧
      actual.pc.toNat + 4 < (packingCode code).length ∧
      PackingOp.decode (RawTreePreprocessingClaims.fetch code actual) = some (body[count]'(by rw [body_length]; exact hc)) ∧
      packingAccessFits rom H actual (body[count]'(by rw [body_length]; exact hc)) := by
  have hrun := body_prefix_run rom left right hcode hpcCode state hpc hactive count hc.le
  have hstraight : StraightProgram (body.take count) := fun op hop => body_straight op (List.mem_of_mem_take hop)
  have hp : (executeOps rom (body.take count) state).pc.toNat = 5 * (left.length + count) := by
    rw [executeOps_pc rom _ state hstraight, hpc,
      List.length_take_of_le (by rw [body_length]; exact hc.le), BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    rw [show 5 * left.length + 5 * count = 5 * (left.length + count) by omega]
    exact Nat.mod_eq_of_lt ((by
      simp only [List.length_append, body_length]
      omega : 5 * (left.length + count) ≤ 5 * (left ++ body ++ right).length).trans_lt hpcCode)
  dsimp only
  simp only [hrun]
  refine ⟨(executeOps_halted rom _ state).trans hactive, hp, ?_, ?_, ?_⟩
  · rw [hp, packingCode_length]
    simp only [List.length_append, body_length]
    omega
  · change PackingOp.decode (physicalFetch bits (packingCode (left ++ body ++ right))
      (executeOps rom (body.take count) state).pc.toNat) = _
    rw [hp, physicalFetch_eq _ _ _ hcode]
    change PackingOp.decode (natFetch (left ++ body ++ right) (5 * (left.length + count))) = _
    rw [natFetch_body _ (left.length + count) (by simp only [List.length_append, body_length]; omega), decode_encode]
    exact congrArg some (PA17UniformGenerator035a.segment_index left body right count (by rw [body_length]; exact hc))
  · exact body_accessSafe q C H rom state hh hq hb hw ha hs hf hphysical hbank hfit16 hroom16 hfit17 hroom17 hrom
      count (by rw [body_length]; exact hc)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
