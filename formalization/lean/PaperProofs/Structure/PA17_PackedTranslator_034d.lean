module

public import PaperProofs.Structure.PA17_PackedTranslator_034b

/-! Composable actual packed-instruction access certificates. Data equality
transports the existing scalar programs from their local PC-zero proof to
their real position inside a larger straight program. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

def PackedDataEq {bits : Nat} (left right : WordState bits) : Prop :=
  left.register = right.register ∧ left.heap = right.heap

theorem packingExecuteOp_dataEq {bits : Nat} (rom : PhysicalROM) (op : PackingOp) (left right : WordState bits)
    (h : PackedDataEq left right) : PackedDataEq (packingExecuteOp rom op left) (packingExecuteOp rom op right) := by
  rcases left with ⟨lr, lh, lp, la⟩
  rcases right with ⟨rr, rh, rp, ra⟩
  rcases h with ⟨hr, hh⟩
  dsimp only at hr hh
  subst rr
  subst rh
  cases op with
  | base op =>
    cases op with
    | base instruction => cases instruction <;> exact ⟨rfl, rfl⟩
    | subtract _ _ _ => exact ⟨rfl, rfl⟩
  | arithmetic _ _ _ _ => exact ⟨rfl, rfl⟩
  | jumpIfZero _ _ => exact ⟨rfl, rfl⟩

theorem executeOps_dataEq {bits : Nat} (rom : PhysicalROM) (ops : List PackingOp) (left right : WordState bits)
    (h : PackedDataEq left right) : PackedDataEq (executeOps rom ops left) (executeOps rom ops right) := by
  induction ops generalizing left right with
  | nil => exact h
  | cons op later ih => exact ih _ _ (packingExecuteOp_dataEq rom op left right h)

theorem packingAccessFits_dataEq {bits : Nat} (heapWords : Nat) (rom : PhysicalROM) (op : PackingOp)
    (left right : WordState bits) (h : PackedDataEq left right) :
    packingAccessFits rom heapWords left op ↔ packingAccessFits rom heapWords right op := by
  have hr := h.1
  cases op with
  | base op =>
    cases op with
    | base instruction => cases instruction <;> simp [packingAccessFits, AccessFits, hr]
    | subtract _ _ _ => rfl
  | arithmetic _ _ _ _ => rfl
  | jumpIfZero _ _ => rfl

def PackedAccessSafe {bits : Nat} (heapWords : Nat) (rom : PhysicalROM) (ops : List PackingOp) (state : WordState bits) : Prop :=
  ∀ count (hc : count < ops.length), packingAccessFits rom heapWords (executeOps rom (ops.take count) state) ops[count]

theorem PackedAccessSafe.nil {bits : Nat} (heapWords : Nat) (rom : PhysicalROM) (state : WordState bits) :
    PackedAccessSafe heapWords rom [] state := by intro count hc; simp at hc

theorem PackedAccessSafe.append {bits : Nat} (heapWords : Nat) (rom : PhysicalROM)
    (left right : List PackingOp) (state : WordState bits)
    (hl : PackedAccessSafe heapWords rom left state)
    (hr : PackedAccessSafe heapWords rom right (executeOps rom left state)) :
    PackedAccessSafe heapWords rom (left ++ right) state := by
  intro count hc
  by_cases hs : count < left.length
  · rw [List.take_append_of_le_length hs.le, List.getElem_append_left hs]
    exact hl count hs
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
    have he : extra < right.length := by rw [List.length_append] at hc; omega
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      executeOps_append, List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using hr extra he

theorem PackedAccessSafe.of_dataEq {bits : Nat} (heapWords : Nat) (rom : PhysicalROM) (ops : List PackingOp)
    (left right : WordState bits) (h : PackedDataEq left right)
    (hr : PackedAccessSafe heapWords rom ops right) : PackedAccessSafe heapWords rom ops left := by
  intro count hc
  exact (packingAccessFits_dataEq heapWords rom ops[count] _ _ (executeOps_dataEq rom (ops.take count) left right h)).mpr (hr count hc)

theorem readProgram_accessSafe {bits : Nat} (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords) :
    PackedAccessSafe heapWords rom (readProgram q bits) state := by
  let normalized : WordState bits := { state with pc := BitVec.ofNat bits 0, halted := false }
  apply PackedAccessSafe.of_dataEq heapWords rom _ state normalized ⟨rfl, rfl⟩
  intro count hc
  rw [← packingRun_eq_executeOps_take rom (readProgram q bits) normalized (readProgram_straight q bits)
    (readProgram_code_fit q hbits hwidth) (readProgram_pc_fit q hbits) rfl rfl count hc.le]
  exact readProgram_accessFits q heapWords rom normalized hbits hwidth hstart hnext hlookahead rfl rfl count hc

theorem safeWriteProgram_accessSafe {bits : Nat} (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords) :
    PackedAccessSafe heapWords rom (safeWriteProgram q bits) state := by
  let normalized : WordState bits := { state with pc := BitVec.ofNat bits 0, halted := false }
  apply PackedAccessSafe.of_dataEq heapWords rom _ state normalized ⟨rfl, rfl⟩
  intro count hc
  rw [← packingRun_eq_executeOps_take rom (safeWriteProgram q bits) normalized (safeWriteProgram_straight q bits)
    (safeWriteProgram_code_fit q hbits hwidth) (safeWriteProgram_pc_fit q hbits) rfl rfl count hc.le]
  exact safeWriteProgram_accessFits q heapWords rom normalized hbits hwidth hstart hnext hlookahead rfl rfl count hc

theorem loadReg_accessSafe {bits : Nat} (heapWords spillBase : Nat) (source target : Register)
    (rom : PhysicalROM) (state : WordState bits) (hfit : Fits bits (spillBase + source.word))
    (haccess : spillBase + source.word < heapWords) : PackedAccessSafe heapWords rom (loadReg spillBase source target) state := by
  intro count hc
  change count < 2 at hc
  interval_cases count <;>
    simp [loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, haccess]

theorem saveReg_accessSafe {bits : Nat} (heapWords spillBase : Nat) (target : Register)
    (rom : PhysicalROM) (state : WordState bits) (hfit : Fits bits (spillBase + target.word))
    (haccess : spillBase + target.word < heapWords) : PackedAccessSafe heapWords rom (saveReg spillBase target) state := by
  intro count hc
  change count < 2 at hc
  interval_cases count <;>
    simp [saveReg, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, haccess]

theorem capAddress_accessSafe {bits : Nat} (heapWords capWords spillBase : Nat) (pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hfit : Fits bits (spillBase + pointer.word))
    (haccess : spillBase + pointer.word < heapWords) : PackedAccessSafe heapWords rom (capAddress capWords spillBase pointer) state := by
  intro count hc
  change count < 6 at hc
  interval_cases count <;>
    simp [capAddress, loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, haccess]

theorem indexAddress_accessSafe {bits : Nat} (heapWords q capWords spillBase : Nat) (pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hfit : Fits bits (spillBase + pointer.word))
    (haccess : spillBase + pointer.word < heapWords) : PackedAccessSafe heapWords rom (indexAddress q bits capWords spillBase pointer) state := by
  intro count hc
  change count < 6 at hc
  interval_cases count <;>
    simp [indexAddress, loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, haccess]

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
