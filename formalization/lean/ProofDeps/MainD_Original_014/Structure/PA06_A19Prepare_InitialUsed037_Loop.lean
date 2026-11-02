module

public import Structure.PA06_A19Prepare_InitialUsed037_Effects
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate concrete loop invariant. It mentions only reached physical
data, past used bits and frames; it does not assume BodyExits or the desired
whole-loop result. Actual body/tail preservation must be proved below. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
open AlgorithmClaims.PackedCapacityRAM

def scalar (q : Nat) (full : List (Finset (Fin q)))
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q)) (a : Nat) : Nat :=
  unpackHeap q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) (dataHeap heap) a

structure Current (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original : WordState (indexWidth 32 full.length q)) (j : Nat)
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  base : state.register .address = original.register .address
  header : PA06A19PrepareRuntimePacked016.Header q state.heap
  bounded : CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
    (unpackHeap q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) (dataHeap state.heap))
  pointer : (state.heap (original.register .address + BitVec.ofNat _ pointerSlot)).toNat = usedPointer full.length q (treeSize q full) j
  cursor : (state.heap (original.register .address + BitVec.ofNat _ cursorSlot)).toNat = romCursor full.length q j
  remaining : (state.heap (original.register .address + BitVec.ofNat _ counterSlot)).toNat = q - j
  written : ∀ tool : Fin q, tool.val < j → scalar q full state.heap (tableWords full.length q (treeSize q full) + tool.val) = bit (decide (tool ∈ used))
  table_frame : ∀ a < tableWords full.length q (treeSize q full), scalar q full state.heap a = scalar q full original.heap a
  ordinary_frame : ∀ point : BitVec (indexWidth 32 full.length q),
    4 + packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) ≤ point.toNat →
    point ≠ original.register .address + BitVec.ofNat _ pointerSlot →
    point ≠ original.register .address + BitVec.ofNat _ cursorSlot →
    point ≠ original.register .address + BitVec.ofNat _ counterSlot → state.heap point = original.heap point

def valid (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original state : WordState (indexWidth 32 full.length q)) : Prop :=
  ∃ j : Nat, j ≤ q ∧ Current q full used original j state

theorem Current.congr (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original : WordState (indexWidth 32 full.length q)) (j : Nat)
    (old fresh : WordState (indexWidth 32 full.length q)) (h : Current q full used original j old)
    (hheap : fresh.heap = old.heap) (hbase : fresh.register .address = old.register .address) :
    Current q full used original j fresh := by
  refine ⟨hbase.trans h.base, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hheap]
  · exact h.header
  · exact h.bounded
  · exact h.pointer
  · exact h.cursor
  · exact h.remaining
  · exact h.written
  · exact h.table_frame
  · exact h.ordinary_frame

theorem current_head (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original : WordState (indexWidth 32 full.length q)) (j : Nat)
    (state : WordState (indexWidth 32 full.length q)) (h : Current q full used original j state)
    (rom : PhysicalROM) (exit : Nat) :
    Current q full used original j (executeOps rom (relativeLoopHead counterSlot exit) state) :=
  Current.congr q full used original j state _ h
    (relativeLoopHead_word_heap rom counterSlot exit state) (relativeLoopHead_word_base rom counterSlot exit state)

theorem current_pointer (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original : WordState (indexWidth 32 full.length q)) (j : Nat)
    (state : WordState (indexWidth 32 full.length q)) (h : Current q full used original j state) :
    (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat = usedPointer full.length q (treeSize q full) j := by
  unfold PA06A19PrepareBankPacked021.pointer
  rw [h.base]
  exact h.pointer

theorem current_cursor (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original : WordState (indexWidth 32 full.length q)) (j : Nat)
    (state : WordState (indexWidth 32 full.length q)) (h : Current q full used original j state) :
    (state.heap (state.register .address + BitVec.ofNat _ cursorSlot)).toNat = romCursor full.length q j := by
  rw [h.base]
  exact h.cursor

theorem current_remaining (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original : WordState (indexWidth 32 full.length q)) (j : Nat)
    (state : WordState (indexWidth 32 full.length q)) (h : Current q full used original j state) :
    (state.heap (state.register .address + BitVec.ofNat _ counterSlot)).toNat = q - j := by
  rw [h.base]
  exact h.remaining

theorem current_read_value (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (j : Nat) (hj : j < q)
    (state : WordState (indexWidth 32 full.length q)) (h : Current q full used original j state) :
    ((executeOps (controllerInput q full used) readUsed state).register .value).toNat = bit (decide (⟨j, hj⟩ ∈ used)) ∧
    ((executeOps (controllerInput q full used) readUsed state).register .value).toNat ≤ q := by
  have hr := readUsed_initial_bit q full used state ⟨j, hj⟩ (current_cursor q full used original j state h)
  have hb : bit (decide (⟨j, hj⟩ ∈ used)) ≤ 1 := by unfold bit; split_ifs <;> omega
  have hfit : Fits (indexWidth 32 full.length q) (bit (decide (⟨j, hj⟩ ∈ used))) :=
    (hb.trans (by decide : 1 ≤ 8)).trans_lt (PA17WordBounds023.small_word_fit full.length q)
  rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  exact ⟨rfl, hb.trans (Nat.succ_le_of_lt hq)⟩

theorem current_read_word_bound (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (j : Nat) (hj : j < q)
    (state : WordState (indexWidth 32 full.length q)) (h : Current q full used original j state) :
    (BitVec.ofNat (indexWidth 32 full.length q) ((controllerInput q full used).semantic.read .input
      (state.heap (state.register .address + BitVec.ofNat _ cursorSlot)).toNat)).toNat ≤ q := by
  have hh := (current_read_value q full used hq original j hj state h).2
  rw [readUsed_value] at hh
  exact hh

structure StateBounds (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  pointer_lt : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < capacityWords 8192 full.length q (treeSize q full)
  product : Fits (indexWidth 32 full.length q)
    ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q)
  physical : Fits (indexWidth 32 full.length q)
    ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / indexWidth 32 full.length q + 4 + 1)
  physical_room : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q /
    indexWidth 32 full.length q + 4 + 1 < PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)
  after_lookahead : 4 + packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) + 1 ≤
    (state.register .address).toNat + pointerSlot
  fit_pointer : Fits (indexWidth 32 full.length q) ((state.register .address).toNat + pointerSlot)
  room_pointer : (state.register .address).toNat + pointerSlot < PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)
  fit_cursor : Fits (indexWidth 32 full.length q) ((state.register .address).toNat + cursorSlot)
  room_cursor : (state.register .address).toNat + cursorSlot < PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)
  fit_counter : Fits (indexWidth 32 full.length q) ((state.register .address).toNat + counterSlot)
  room_counter : (state.register .address).toNat + counterSlot < PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)
  region : Fits (indexWidth 32 full.length q) (capacityWords 8192 full.length q (treeSize q full) * CapacityBits.width q)

/-- Every bound is proved from original data plus the concrete reached
state representation. StateBounds is never an original-caller oracle. -/
theorem current_bounds (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (j : Nat) (hj : j < q) (state : WordState (indexWidth 32 full.length q))
    (h : Current q full used original j state) : StateBounds q full state := by
  have hbase : (state.register .address).toNat = PA06A19PrepareControlBank017.controlBase full.length q
      (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) :=
    (congrArg BitVec.toNat h.base).trans hd.base
  have hp := current_pointer q full used original j state h
  have hr16 := actual_control_room q full hq pointerSlot (by decide)
  have hr17 := actual_control_room q full hq cursorSlot (by decide)
  have hr18 := actual_control_room q full hq counterSlot (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact pointer_lt_capacity full.length q (treeSize q full) j hq hj
  · rw [hp]
    exact actual_pointer_product_fits q full hq j hj
  · rw [hp]
    exact (actual_physical_next_room q full hq j hj).1
  · rw [hp]
    exact (actual_physical_next_room q full hq j hj).2
  · rw [hbase]
    exact actual_control_after_lookahead q full pointerSlot
  · rw [hbase]
    exact hr16.2
  · rw [hbase]
    exact hr16.1
  · rw [hbase]
    exact hr17.2
  · rw [hbase]
    exact hr17.1
  · rw [hbase]
    exact hr18.2
  · rw [hbase]
    exact hr18.1
  · have hr := PA06A19PrepareRuntimeLayout026.actual_product_fits q full hq
    rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hr
    exact hr

theorem current_rom_room (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original : WordState (indexWidth 32 full.length q)) (j : Nat) (hj : j < q)
    (state : WordState (indexWidth 32 full.length q)) (h : Current q full used original j state) :
    (state.heap (state.register .address + BitVec.ofNat _ cursorSlot)).toNat < ((controllerInput q full used).words .input).length := by
  rw [current_cursor q full used original j state h]
  exact actual_cursor_read_lt q full used j hj

structure BodyStep (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original before : WordState (indexWidth 32 full.length q)) (j : Nat)
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  base : state.register .address = original.register .address
  header : PA06A19PrepareRuntimePacked016.Header q state.heap
  bounded : CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
    (unpackHeap q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) (dataHeap state.heap))
  pointer : (state.heap (original.register .address + BitVec.ofNat _ pointerSlot)).toNat = usedPointer full.length q (treeSize q full) (j + 1)
  cursor : (state.heap (original.register .address + BitVec.ofNat _ cursorSlot)).toNat = romCursor full.length q (j + 1)
  counter : state.heap (original.register .address + BitVec.ofNat _ counterSlot) = before.heap (original.register .address + BitVec.ofNat _ counterSlot)
  written : ∀ tool : Fin q, tool.val < j + 1 → scalar q full state.heap (tableWords full.length q (treeSize q full) + tool.val) = bit (decide (tool ∈ used))
  table_frame : ∀ a < tableWords full.length q (treeSize q full), scalar q full state.heap a = scalar q full original.heap a
  ordinary_frame : ∀ point : BitVec (indexWidth 32 full.length q),
    4 + packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) ≤ point.toNat →
    point ≠ original.register .address + BitVec.ofNat _ pointerSlot →
    point ≠ original.register .address + BitVec.ofNat _ cursorSlot →
    point ≠ original.register .address + BitVec.ofNat _ counterSlot → state.heap point = original.heap point

/-- One actual body, including the real ROM bit and72-op replacement.
Remaining is preserved here; the existing real9-op tail decrements it. -/
theorem current_body_step (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (j : Nat) (hj : j < q) (state : WordState (indexWidth 32 full.length q))
    (h : Current q full used original j state) :
    BodyStep q full used original state j (executeOps (controllerInput q full used) body state) := by
  let rom := controllerInput q full used
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q (treeSize q full)
  let after := executeOps rom body state
  have hb := PA17PackingBounds043.bits_pos full.length q
  have hw := PA17PackingBounds043.width_le_bits full.length q
  have b := current_bounds q full used hq original hd j hj state h
  have hvalue := (current_read_value q full used hq original j hj state h).2
  have hword := current_read_word_bound q full used hq original j hj state h
  have hcontrols := body_controls q C rom state h.header hq hb hw b.pointer_lt b.product b.physical
    b.after_lookahead b.fit_pointer b.fit_cursor b.fit_counter
  have hptrNext : Fits bits ((state.heap (original.register .address + BitVec.ofNat bits pointerSlot)).toNat + 1) := by
    rw [h.pointer]
    exact actual_pointer_next_fits q full hq j hj
  have hcursorNext : Fits bits ((state.heap (original.register .address + BitVec.ofNat bits cursorSlot)).toNat + 1) := by
    rw [h.cursor]
    exact actual_cursor_next_fits q full hq j hj
  have hptr : (after.heap (original.register .address + BitVec.ofNat bits pointerSlot)).toNat =
      usedPointer full.length q (treeSize q full) (j + 1) := by
    have he := hcontrols.1
    simp only [h.base] at he
    rw [he, increment_toNat _ hptrNext, h.pointer]
    unfold usedPointer
    omega
  have hcursor : (after.heap (original.register .address + BitVec.ofNat bits cursorSlot)).toNat = romCursor full.length q (j + 1) := by
    have he := hcontrols.2.1
    simp only [h.base] at he
    rw [he, increment_toNat _ hcursorNext, h.cursor]
    unfold romCursor
    omega
  have hcounter : after.heap (original.register .address + BitVec.ofNat bits counterSlot) =
      state.heap (original.register .address + BitVec.ofNat bits counterSlot) := by
    simpa only [h.base] using hcontrols.2.2
  have htake : body.take 88 = body := by simpa only [body_length] using (List.take_length (l := body))
  have hheader := body_prefix_header q C rom state h.header hq hb hw b.pointer_lt b.product b.physical
    b.after_lookahead b.fit_pointer b.fit_cursor 88 le_rfl
  rw [htake] at hheader
  have hbounded := body_prefix_capacity q C rom state h.header hq hb hw b.pointer_lt b.product b.physical
    b.after_lookahead b.fit_pointer b.fit_cursor b.region hvalue h.bounded 88 le_rfl
  rw [htake] at hbounded
  refine ⟨(body_address rom state).trans h.base, hheader, hbounded, hptr, hcursor, hcounter, ?_, ?_, ?_⟩
  · intro tool ht
    have ho := pointer_lt_capacity full.length q (treeSize q full) tool.val hq tool.isLt
    by_cases heq : tool.val = j
    · have htool : tool = ⟨j, hj⟩ := Fin.ext heq
      subst tool
      have he := body_target q C rom state h.header hq hb hw b.pointer_lt b.product b.physical
        b.after_lookahead b.fit_pointer b.fit_cursor b.region hword
      have hv := (current_read_value q full used hq original j hj state h).1
      rw [readUsed_value] at hv
      rw [current_pointer q full used original j state h] at he
      exact he.trans hv
    · have hne : tableWords full.length q (treeSize q full) + tool.val ≠
          (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat := by
        rw [current_pointer q full used original j state h]
        unfold usedPointer
        omega
      have he := body_other_capacity q C (tableWords full.length q (treeSize q full) + tool.val) rom state
        h.header hq hb hw b.pointer_lt b.product b.physical b.after_lookahead b.fit_pointer b.fit_cursor b.region hword ho hne
      exact he.trans (h.written tool (by omega))
  · intro a ha
    have ht0 := pointer_lt_capacity full.length q (treeSize q full) 0 hq hq
    have ho : a < C := by unfold usedPointer at ht0; omega
    have hne : a ≠ (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat := by
      rw [current_pointer q full used original j state h]
      unfold usedPointer
      omega
    exact (body_other_capacity q C a rom state h.header hq hb hw b.pointer_lt b.product b.physical
      b.after_lookahead b.fit_pointer b.fit_cursor b.region hword ho hne).trans (h.table_frame a ha)
  · intro point hp hne16 hne17 hne18
    have he := body_ordinary_frame q C rom state h.header hq hb hw b.pointer_lt b.product b.physical
      b.after_lookahead b.fit_pointer hword point hp
      (by rw [h.base]; exact hne16) (by rw [h.base]; exact hne17)
    exact he.trans (h.ordinary_frame point hp hne16 hne17 hne18)

private theorem bank_key_ne {bits : Nat} (base : BitVec bits) (slot other : Nat)
    (hs : Fits bits (base.toNat + slot)) (ho : Fits bits (base.toNat + other))
    (hne : slot ≠ other) : base + BitVec.ofNat bits slot ≠ base + BitVec.ofNat bits other := by
  simp only [PA06A19PrepareBankPacked021.bankWord_eq]
  exact (ofNat_injective_of_fit _ _ hs ho).not.mpr (by omega)

/-- Construct the next invariant from an abstract reached state. This keeps
all field projections independent of the concrete tail execution term. -/
private theorem tail_current_of_fields (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (j : Nat) (hj : j < q) (before : WordState (indexWidth 32 full.length q))
    (hbefore : Current q full used original j before)
    (done after : WordState (indexWidth 32 full.length q)) (h : BodyStep q full used original before j done)
    (hbase : after.register .address = done.register .address)
    (hheap : after.heap = Function.update done.heap
      (original.register .address + BitVec.ofNat _ counterSlot) (BitVec.ofNat _ (q - (j + 1)))) :
    Current q full used original (j + 1) after := by
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q (treeSize q full)
  let CB := (original.register .address).toNat
  let key := original.register .address + BitVec.ofNat bits counterSlot
  let value := BitVec.ofNat bits (q - (j + 1))
  have b := current_bounds q full used hq original hd j hj before hbefore
  have hfit16 : Fits bits (CB + pointerSlot) := by
    dsimp only [CB]
    rw [hd.base]
    exact (actual_control_room q full hq pointerSlot (by decide)).2
  have hfit17 : Fits bits (CB + cursorSlot) := by
    dsimp only [CB]
    rw [hd.base]
    exact (actual_control_room q full hq cursorSlot (by decide)).2
  have hfit18 : Fits bits (CB + counterSlot) := by
    dsimp only [CB]
    rw [hd.base]
    exact (actual_control_room q full hq counterSlot (by decide)).2
  have hafter : 4 + packedCapacityWords q C bits ≤ CB + counterSlot := by
    have hh := actual_control_after_lookahead q full counterSlot
    change 4 + packedCapacityWords q C bits + 1 ≤
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full) (packedCapacityWords q C bits) + counterSlot at hh
    rw [← hd.base] at hh
    dsimp only [CB]
    omega
  have hne16 : original.register .address + BitVec.ofNat bits pointerSlot ≠ key :=
    bank_key_ne (original.register .address) pointerSlot counterSlot hfit16 hfit18 (by decide)
  have hne17 : original.register .address + BitVec.ofNat bits cursorSlot ≠ key :=
    bank_key_ne (original.register .address) cursorSlot counterSlot hfit17 hfit18 (by decide)
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q 0 hq (by omega)
  have hQfit : Fits bits q := (by dsimp only [bits]; omega : q ≤ 2 ^ bits - 1).trans_lt (PA17GeneratorStatic048.maxWord_fits bits)
  have hremaining : Fits bits (q - (j + 1)) := (Nat.sub_le _ _).trans_lt hQfit
  have hcap (a : Nat) (ha : a < C) :
      unpackHeap q C bits (dataHeap after.heap) a =
        unpackHeap q C bits (dataHeap done.heap) a := by
    rw [hheap]
    simp only [PA06A19PrepareBankPacked021.bankWord_eq]
    exact update_control_capacity q C (CB + counterSlot) value done.heap
      (PA17PackingBounds043.bits_pos full.length q) b.region hafter hfit18 a ha
  refine ⟨hbase.trans h.base, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hheap]
    simp only [PA06A19PrepareBankPacked021.bankWord_eq]
    exact PA06A19PrepareRuntimePacked016.update_header q (CB + counterSlot) value done.heap h.header (by omega) hfit18
  · intro a ha
    rw [hcap a ha]
    exact h.bounded a ha
  · rw [hheap, Function.update_of_ne hne16]
    exact h.pointer
  · rw [hheap, Function.update_of_ne hne17]
    exact h.cursor
  · rw [hheap, Function.update_self]
    change (BitVec.ofNat bits (q - (j + 1))).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hremaining]
  · intro tool ht
    have ho := pointer_lt_capacity full.length q (treeSize q full) tool.val hq tool.isLt
    change tableWords full.length q (treeSize q full) + tool.val < C at ho
    change unpackHeap q C bits (dataHeap after.heap)
      (tableWords full.length q (treeSize q full) + tool.val) = _
    rw [hcap (tableWords full.length q (treeSize q full) + tool.val) ho]
    exact h.written tool ht
  · intro a ha
    have ht0 := pointer_lt_capacity full.length q (treeSize q full) 0 hq hq
    have ho : a < C := by unfold usedPointer at ht0; omega
    change unpackHeap q C bits (dataHeap after.heap) a = _
    rw [hcap a ho]
    exact h.table_frame a ha
  · intro point hp hn16 hn17 hn18
    rw [hheap, Function.update_of_ne hn18]
    exact h.ordinary_frame point hp hn16 hn17 hn18

theorem tail_current (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (j : Nat) (hj : j < q) (before : WordState (indexWidth 32 full.length q))
    (hbefore : Current q full used original j before)
    (done : WordState (indexWidth 32 full.length q)) (h : BodyStep q full used original before j done)
    (rom : PhysicalROM) (entry : Nat) :
    Current q full used original (j + 1) (executeOps rom (relativeLoopTail counterSlot entry) done) := by
  have hcount : (done.heap (original.register .address + BitVec.ofNat _ counterSlot)).toNat = q - j := by
    rw [h.counter]
    exact hbefore.remaining
  have hone : (BitVec.ofNat (indexWidth 32 full.length q) 1).toNat = 1 := Nat.mod_eq_of_lt
    ((by decide : 1 ≤ 8).trans_lt (PA17WordBounds023.small_word_fit full.length q))
  have hheap : (executeOps rom (relativeLoopTail counterSlot entry) done).heap = Function.update done.heap
      (original.register .address + BitVec.ofNat _ counterSlot) (BitVec.ofNat _ (q - (j + 1))) := by
    rw [relativeLoopTail_word_heap, h.base, hcount, hone,
      show q - j - 1 = q - (j + 1) by omega]
  exact tail_current_of_fields q full used hq original hd j hj before hbefore done
    (executeOps rom (relativeLoopTail counterSlot entry) done) h
    (relativeLoopTail_word_base rom counterSlot entry done) hheap

/-- Assemble the body exit facts with abstract body and tail states. -/
private theorem body_exit_of_fields (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (original state tested done after : WordState (indexWidth 32 full.length q))
    (j : Nat) (hj : j + 1 ≤ q) (pc : BitVec (indexWidth 32 full.length q))
    (h : Current q full used original j state) (hs : BodyStep q full used original tested j done)
    (hp : done.pc = pc) (ha : done.halted = false) (htheap : tested.heap = state.heap)
    (hnext : Current q full used original (j + 1) after) :
    done.pc = pc ∧ done.halted = false ∧ done.register .address = state.register .address ∧
      done.heap (state.register .address + BitVec.ofNat _ counterSlot) =
        state.heap (state.register .address + BitVec.ofNat _ counterSlot) ∧ valid q full used original after := by
  refine ⟨hp, ha, hs.base.trans h.base.symm, ?_, j + 1, hj, hnext⟩
  have he := hs.counter
  simpa only [h.base, htheap] using he

/-- The concrete88-op body discharges BodyExits, including invariant after
the actual9-op tail. No BodyExits/loop result is taken as a caller premise. -/
theorem concrete_body_exits (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (left right : List PackingOp)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ relativeLoopBlock counterSlot left.length body ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ relativeLoopBlock counterSlot left.length body ++ right).length)) :
    PSTRBuildLower.WordLoop.BodyExits (valid q full used original) (controllerInput q full used)
      left body right counterSlot (fun _ => 88) := by
  intro state hv hpc ha hcounter
  obtain ⟨j, hj, h⟩ := hv
  have hjlt : j < q := by
    have hc := current_remaining q full used original j state h
    omega
  let rom := controllerInput q full used
  let bits := indexWidth 32 full.length q
  let tested := executeOps rom (relativeLoopHead counterSlot (5 * (left.length + body.length + 14))) state
  let bodyLead := left ++ relativeLoopHead counterSlot (5 * (left.length + body.length + 14))
  let bodyRight := relativeLoopTail counterSlot (5 * left.length) ++ right
  have ht : Current q full used original j tested := current_head q full used original j state h rom _
  have hpTest : tested.pc = BitVec.ofNat bits (5 * (left.length + 5)) := by
    have he : 5 * left.length + 25 = 5 * (left.length + 5) := by omega
    simpa only [tested, relativeLoopHead_word_pc, ite_eq_right hcounter, hpc, BitVec.ofNat_add_ofNat]
      using congrArg (BitVec.ofNat bits) he
  have haTest : tested.halted = false := (executeOps_halted rom _ state).trans ha
  have hlead : bodyLead.length = left.length + 5 := by simp only [bodyLead, List.length_append, relativeLoopHead_length]
  have hbodyCode : left ++ relativeLoopBlock counterSlot left.length body ++ right = bodyLead ++ body ++ bodyRight := by
    simp only [relativeLoopBlock, bodyLead, bodyRight, List.append_assoc]
  have hrun : packingRun rom (left ++ relativeLoopBlock counterSlot left.length body ++ right) 88 tested = executeOps rom body tested := by
    rw [hbodyCode]
    exact body_run rom bodyLead bodyRight (by rw [← hbodyCode]; exact hcode)
      (by rw [← hbodyCode]; exact hpcCode) tested (by rw [hlead]; exact hpTest) haTest
  have hs := current_body_step q full used hq original hd j hjlt tested ht
  have hnext := tail_current q full used hq original hd j hjlt tested ht (executeOps rom body tested) hs rom (5 * left.length)
  have hpDone : (executeOps rom body tested).pc = BitVec.ofNat bits (5 * (left.length + 5 + body.length)) := by
    have hpStep : (executeOps rom body tested).pc = tested.pc + BitVec.ofNat bits (5 * body.length) :=
      executeOps_pc rom body tested body_straight
    have hpEntry : tested.pc + BitVec.ofNat bits (5 * body.length) =
        BitVec.ofNat bits (5 * (left.length + 5)) + BitVec.ofNat bits (5 * body.length) :=
      congrArg (fun pc : BitVec bits => pc + BitVec.ofNat bits (5 * body.length)) hpTest
    have hpSum : BitVec.ofNat bits (5 * (left.length + 5)) + BitVec.ofNat bits (5 * body.length) =
        BitVec.ofNat bits (5 * (left.length + 5 + body.length)) := by
      have hsum : 5 * (left.length + 5) + 5 * body.length = 5 * (left.length + 5 + body.length) := by omega
      exact (BitVec.ofNat_add_ofNat (n := bits) (5 * (left.length + 5)) (5 * body.length)).trans
        (congrArg (BitVec.ofNat bits) hsum)
    exact hpStep.trans (hpEntry.trans hpSum)
  have hfields := body_exit_of_fields q full used original state tested (executeOps rom body tested)
    (executeOps rom (relativeLoopTail counterSlot (5 * left.length)) (executeOps rom body tested))
    j (by omega) (BitVec.ofNat bits (5 * (left.length + 5 + body.length))) h hs hpDone
    ((executeOps_halted rom body tested).trans haTest) (relativeLoopHead_word_heap rom counterSlot _ state) hnext
  dsimp only
  let done := packingRun rom (left ++ relativeLoopBlock counterSlot left.length body ++ right) 88 tested
  change done.pc = BitVec.ofNat bits (5 * (left.length + 5 + body.length)) ∧ done.halted = false ∧
    done.register .address = state.register .address ∧
    done.heap (state.register .address + BitVec.ofNat bits counterSlot) = state.heap (state.register .address + BitVec.ofNat bits counterSlot) ∧
    valid q full used original (executeOps rom (relativeLoopTail counterSlot (5 * left.length)) done)
  rw [show done = executeOps rom body tested from hrun]
  exact hfields

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
