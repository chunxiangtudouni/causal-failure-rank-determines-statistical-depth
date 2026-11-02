module
public import PaperProofs.Structure.PA17_PackedStore_042a
public import PaperProofs.Structure.PA17_PackedTranslator_034e
import Mathlib.Tactic.IntervalCases

/-! Real clear-then-write50 segment of write87. The source is masked by the
actual capacity branch before writing; arbitrary index words stay arbitrary. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
namespace PaperProofs.Structure.LaminarTree.PA17PackedStore042b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034 PA17PackedStore042a

structure Layout (q cap indexWords spill words bits : Nat) : Prop where
  cap_pos : 0 < cap
  bits_min : 8 ≤ bits
  width : CapacityBits.width q ≤ bits
  cap_fit : Fits bits cap
  region_fit : Fits bits (cap * CapacityBits.width q)
  base : spill = packedCapacityWords q cap bits + indexWords
  allocation : spill + spillWords ≤ words
  footprint : Fits bits words

def writePrefix (q bits cap spill : Nat) (pointer source : Register) : List PackingOp :=
  selectInput q bits cap spill pointer source ++ safeWriteProgram q bits

def writeTail (q bits cap spill : Nat) (pointer source : Register) : List PackingOp :=
  indexAddress q bits cap spill pointer ++
    [.base (.subtract .flag .total .address), .base (.base (.loadHeap .old .index))] ++
    loadReg spill source .fresh ++
    [.base (.base (.select .value .flag .old .fresh)), .base (.base (.storeHeap .index .value))]

theorem writeMacro_split (q bits cap spill : Nat) (pointer source : Register) :
    writeMacro q bits cap spill pointer source = writePrefix q bits cap spill pointer source ++ writeTail q bits cap spill pointer source := by
  simp only [writeMacro, writePrefix, writeTail, selectInput, List.append_assoc]

theorem writePrefix_length (q bits cap spill : Nat) (pointer source : Register) :
    (writePrefix q bits cap spill pointer source).length = 75 := rfl

theorem writeTail_length (q bits cap spill : Nat) (pointer source : Register) :
    (writeTail q bits cap spill pointer source).length = 12 := rfl

theorem Layout.spill_access {q cap indexWords spill words bits : Nat} (hl : Layout q cap indexWords spill words bits) (r : Register) :
    spill + r.word < words := by
  have hr := register_word_lt r
  have ha := hl.allocation
  omega

theorem selectInput_take_heap {bits : Nat} (q cap spill : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (count : Nat)
    (hc : count ≤ (selectInput q bits cap spill pointer source).length) :
    (executeOps rom ((selectInput q bits cap spill pointer source).take count) state).heap = state.heap := by
  change count ≤ 25 at hc
  interval_cases count <;> rfl

theorem selectInput_accessSafe {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits) :
    PackedAccessSafe words rom (selectInput q bits cap spill pointer source) state := by
  let prepared := executeOps rom (capAddress cap spill pointer) state
  let scalar := executeOps rom (readProgram q bits) prepared
  have hptr := hl.spill_access pointer
  have hsource := hl.spill_access source
  have h1 := capAddress_accessSafe words cap spill pointer rom state (hptr.trans hl.footprint) hptr
  have hb := scalar_access_bounds q cap indexWords spill words (by have := hl.bits_min; omega) hl.base hl.allocation
    hl.footprint hl.region_fit prepared (capAddress_address_le cap spill pointer rom state hl.cap_fit)
  have h2 := readProgram_accessSafe q words rom prepared (by have := hl.bits_min; omega) hl.width hb.1 hb.2.1 hb.2.2
  have h3 := loadReg_accessSafe words spill source .fresh rom scalar (hsource.trans hl.footprint) hsource
  have h4 : PackedAccessSafe words rom [.base (.base (.select .value .flag .fresh .value))]
      (executeOps rom (loadReg spill source .fresh) scalar) := by
    intro count hc
    change count < 1 at hc
    have heq : count = 0 := by omega
    subst count
    trivial
  simp only [selectInput, List.append_assoc]
  exact PackedAccessSafe.append _ _ _ _ _ h1 (PackedAccessSafe.append _ _ _ _ _ h2 (PackedAccessSafe.append _ _ _ _ _ h3 h4))

theorem selectInput_scalar_bounds {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits) :
    let selected := executeOps rom (selectInput q bits cap spill pointer source) state
    Fits bits ((selected.register .address).toNat * CapacityBits.width q) ∧
      Fits bits ((selected.register .address).toNat * CapacityBits.width q / bits + 1) ∧
      (selected.register .address).toNat * CapacityBits.width q / bits + 1 < words := by
  intro selected
  apply scalar_access_bounds q cap indexWords spill words (by have := hl.bits_min; omega) hl.base hl.allocation hl.footprint hl.region_fit selected
  rw [selectInput_address q cap spill pointer source rom state hl.cap_fit, BitVec.toNat_ofNat]
  have hchosen := chosenAddress_lt cap (saved spill pointer state).toNat hl.cap_pos
  rw [Nat.mod_eq_of_lt (hchosen.trans hl.cap_fit)]
  exact hchosen.le

theorem writePrefix_accessSafe {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits) :
    PackedAccessSafe words rom (writePrefix q bits cap spill pointer source) state := by
  have hs := selectInput_accessSafe q cap indexWords spill words pointer source rom state hl
  have hb := selectInput_scalar_bounds q cap indexWords spill words pointer source rom state hl
  exact PackedAccessSafe.append words rom _ _ state hs
    (safeWriteProgram_accessSafe q words rom _ hl.bits_min hl.width hb.1 hb.2.1 hb.2.2)

theorem writePrefix_heap {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits) :
    let selected := executeOps rom (selectInput q bits cap spill pointer source) state
    (executeOps rom (writePrefix q bits cap spill pointer source) state).heap =
      writeHeap (CapacityBits.width q) ((selected.register .address).toNat * CapacityBits.width q) (selected.register .value) state.heap := by
  intro selected
  have hb := selectInput_scalar_bounds q cap indexWords spill words pointer source rom state hl
  rw [writePrefix, executeOps_append, safeWriteProgram_heap q rom _ (by have := hl.bits_min; omega) hl.width hb.1 hb.2.1,
    selectInput_heap]

theorem writeHeap_physical_frame {bits : Nat} (q cap address physical : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (ha : address < cap) (hphysical : packedCapacityWords q cap bits ≤ physical) (hfit : Fits bits physical)
    (hnext : Fits bits (address * CapacityBits.width q / bits + 1)) (hv : value.toNat < 2 ^ CapacityBits.width q) :
    writeHeap (CapacityBits.width q) (address * CapacityBits.width q) value heap (BitVec.ofNat bits physical) =
      heap (BitVec.ofNat bits physical) := by
  let other := cap + (physical - packedCapacityWords q cap bits)
  have ho : cap ≤ other := Nat.le_add_right _ _
  have heq : packedCapacityWords q cap bits + (other - cap) = physical := by dsimp only [other]; omega
  have hu := unpackHeap_write_index q cap address other value heap hbits hwidth ha ho hnext (by rw [heq]; exact hfit) hv
  simp only [unpackHeap, not_lt_of_ge ho, ite_false, heq] at hu
  exact BitVec.eq_of_toNat_eq hu

theorem writePrefix_spill_frame {bits : Nat} (q cap indexWords spill words : Nat) (pointer source register : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    saved spill register (executeOps rom (writePrefix q bits cap spill pointer source) state) = saved spill register state := by
  let selected := executeOps rom (selectInput q bits cap spill pointer source) state
  have ha : (selected.register .address).toNat < cap := by
    rw [selectInput_address q cap spill pointer source rom state hl.cap_fit, BitVec.toNat_ofNat]
    have hh := chosenAddress_lt cap (saved spill pointer state).toNat hl.cap_pos
    rw [Nat.mod_eq_of_lt (hh.trans hl.cap_fit)]
    exact hh
  have hv := selectInput_capacityBound q cap spill pointer source rom state (by have := hl.bits_min; omega) hl.width hl.cap_fit hl.cap_pos hsource hbound
  have hb := selectInput_scalar_bounds q cap indexWords spill words pointer source rom state hl
  unfold saved
  rw [writePrefix_heap q cap indexWords spill words pointer source rom state hl]
  exact writeHeap_physical_frame q cap _ (spill + register.word) (selected.register .value) state.heap
    (by have := hl.bits_min; omega) hl.width ha (by have := hl.base; omega)
    ((hl.spill_access register).trans hl.footprint) hb.2.1 (CapacityBits.value_lt_two_pow_width q _ hv)

def CapacitySafe {bits : Nat} (q cap : Nat) (rom : PhysicalROM) (code : List PackingOp) (state : WordState bits) : Prop :=
  ∀ count ≤ code.length, CapacityPrefixBounded q cap (unpackHeap q cap bits (executeOps rom (code.take count) state).heap)

theorem CapacitySafe.append {bits : Nat} (q cap : Nat) (rom : PhysicalROM) (left right : List PackingOp) (state : WordState bits)
    (hl : CapacitySafe q cap rom left state) (hr : CapacitySafe q cap rom right (executeOps rom left state)) :
    CapacitySafe q cap rom (left ++ right) state := by
  intro count hc
  by_cases hs : count ≤ left.length
  · rw [List.take_append_of_le_length hs]
    exact hl count hs
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, executeOps_append]
    apply hr
    rw [List.length_append] at hc
    omega

theorem writePrefix_capacitySafe {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    CapacitySafe q cap rom (writePrefix q bits cap spill pointer source) state := by
  let selected := executeOps rom (selectInput q bits cap spill pointer source) state
  have hv := selectInput_capacityBound q cap spill pointer source rom state (by have := hl.bits_min; omega) hl.width hl.cap_fit hl.cap_pos hsource hbound
  have hb := selectInput_scalar_bounds q cap indexWords spill words pointer source rom state hl
  have ha : (selected.register .address).toNat < cap := by
    rw [selectInput_address q cap spill pointer source rom state hl.cap_fit, BitVec.toNat_ofNat]
    have hh := chosenAddress_lt cap (saved spill pointer state).toNat hl.cap_pos
    rw [Nat.mod_eq_of_lt (hh.trans hl.cap_fit)]
    exact hh
  apply CapacitySafe.append q cap rom _ _ state
  · intro count hc
    rw [selectInput_take_heap q cap spill pointer source rom state count hc]
    exact hbound
  · intro count hc
    apply safeWriteProgram_prefix_capacityBounded q cap rom selected (by have := hl.bits_min; omega) hl.width hb.1 hb.2.1 hl.region_fit ha hv
      (by rw [show selected.heap = state.heap from selectInput_heap q cap spill pointer source rom state]; exact hbound) count hc

end PaperProofs.Structure.LaminarTree.PA17PackedStore042b
