module
public import PaperProofs.Structure.PA17_PackedStore_042c
import Mathlib.Tactic.IntervalCases

/-! Complete actual writeMacro87: allocated decoded update, all-prefix
capacity, real allocated accesses, and unchanged seven virtual registers. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
namespace PaperProofs.Structure.LaminarTree.PA17PackedStore042d

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034
open PA17PackedStore042a PA17PackedStore042b PA17PackedStore042c

theorem writeTail_take_heap {bits : Nat} (q cap spill : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (count : Nat)
    (hc : count ≤ (writeTail q bits cap spill pointer source).length) :
    (executeOps rom ((writeTail q bits cap spill pointer source).take count) state).heap =
      if count < 12 then state.heap else (executeOps rom (writeTail q bits cap spill pointer source) state).heap := by
  change count ≤ 12 at hc
  by_cases hh : count < 12
  · rw [ite_eq_left hh]
    interval_cases count <;> rfl
  · have he : count = 12 := by omega
    subst count
    rw [show 12 = (writeTail q bits cap spill pointer source).length from rfl, List.take_length]
    rfl

theorem writeTail_capacitySafe {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (haddress : (saved spill pointer state).toNat < cap + indexWords)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    CapacitySafe q cap rom (writeTail q bits cap spill pointer source) state := by
  intro count hc other ho
  rw [writeTail_take_heap q cap spill pointer source rom state count hc]
  split_ifs
  · exact hbound other ho
  · rw [writeTail_heap q cap spill pointer source rom state hl.cap_fit]
    rw [index_update_capacity q cap _ _ state.heap (by have := hl.bits_min; omega) hl.region_fit
      (Nat.le_add_right _ _) ((index_address_access q cap indexWords spill words _ hl haddress).trans hl.footprint) other ho]
    exact hbound other ho

theorem writeTail_accessSafe {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (haddress : (saved spill pointer state).toNat < cap + indexWords) :
    PackedAccessSafe words rom (writeTail q bits cap spill pointer source) state := by
  let indexed := executeOps rom (indexAddress q bits cap spill pointer) state
  let compared := executeOps rom [.base (.subtract .flag .total .address), .base (.base (.loadHeap .old .index))] indexed
  let sourced := executeOps rom (loadReg spill source .fresh) compared
  have hptr := hl.spill_access pointer
  have hsrc := hl.spill_access source
  have h1 := indexAddress_accessSafe words q cap spill pointer rom state (hptr.trans hl.footprint) hptr
  have hia := index_address_access q cap indexWords spill words (saved spill pointer state).toNat hl haddress
  have hi : (indexed.register .index).toNat = packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap) := by
    dsimp only [indexed]
    rw [indexAddress_index q cap spill pointer rom state hl.cap_fit, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (hia.trans hl.footprint)
  have h2 : PackedAccessSafe words rom [.base (.subtract .flag .total .address), .base (.base (.loadHeap .old .index))] indexed := by
    intro count hc
    change count < 2 at hc
    interval_cases count <;> simp [executeOps, packingAccessFits, AccessFits, packingExecuteOp, wordOp, hi, hia]
  have h3 := loadReg_accessSafe words spill source .fresh rom compared (hsrc.trans hl.footprint) hsrc
  have hsindex : sourced.register .index = indexed.register .index := by
    dsimp only [sourced]
    rw [loadReg_register_frame spill source .fresh rom compared .index (by decide) (by decide)]
    rfl
  have h4 : PackedAccessSafe words rom [.base (.base (.select .value .flag .old .fresh)), .base (.base (.storeHeap .index .value))] sourced := by
    intro count hc
    change count < 2 at hc
    interval_cases count <;> simp [executeOps, packingAccessFits, AccessFits, packingExecuteOp, wordOp, wordInstruction, hsindex, hi, hia]
  simp only [writeTail, List.append_assoc]
  exact PackedAccessSafe.append _ _ _ _ _ h1
    (PackedAccessSafe.append _ _ _ _ _ h2 (PackedAccessSafe.append _ _ _ _ _ h3 h4))

theorem writeMacro_capacitySafe {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (haddress : (saved spill pointer state).toNat < cap + indexWords)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    CapacitySafe q cap rom (writeMacro q bits cap spill pointer source) state := by
  have hp := writePrefix_capacitySafe q cap indexWords spill words pointer source rom state hl hsource hbound
  have hf := writePrefix_spill_frame q cap indexWords spill words pointer source pointer rom state hl hsource hbound
  rw [writeMacro_split]
  apply CapacitySafe.append q cap rom _ _ state hp
  apply writeTail_capacitySafe q cap indexWords spill words pointer source rom _ hl (by rw [hf]; exact haddress)
  simpa only [List.take_length] using hp _ le_rfl

theorem writeMacro_accessSafe {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (haddress : (saved spill pointer state).toNat < cap + indexWords)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    PackedAccessSafe words rom (writeMacro q bits cap spill pointer source) state := by
  have hp := writePrefix_accessSafe q cap indexWords spill words pointer source rom state hl
  have hf := writePrefix_spill_frame q cap indexWords spill words pointer source pointer rom state hl hsource hbound
  rw [writeMacro_split]
  apply PackedAccessSafe.append words rom _ _ state hp
  exact writeTail_accessSafe q cap indexWords spill words pointer source rom _ hl (by rw [hf]; exact haddress)

theorem writeMacro_spill_frame {bits : Nat} (q cap indexWords spill words : Nat) (pointer source register : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (haddress : (saved spill pointer state).toNat < cap + indexWords)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    saved spill register (executeOps rom (writeMacro q bits cap spill pointer source) state) = saved spill register state := by
  let written := executeOps rom (writePrefix q bits cap spill pointer source) state
  have hptr := writePrefix_spill_frame q cap indexWords spill words pointer source pointer rom state hl hsource hbound
  have hsrc := writePrefix_spill_frame q cap indexWords spill words pointer source source rom state hl hsource hbound
  have hreg := writePrefix_spill_frame q cap indexWords spill words pointer source register rom state hl hsource hbound
  rw [writeMacro_split, executeOps_append]
  change saved spill register (executeOps rom (writeTail q bits cap spill pointer source) written) = _
  by_cases hc : (saved spill pointer state).toNat < cap
  · unfold saved
    rw [writeTail_heap_capacity q cap spill pointer source rom written hl.cap_fit (by rw [hptr]; exact hc)]
    exact hreg
  · unfold saved
    rw [writeTail_heap q cap spill pointer source rom written hl.cap_fit, hptr, hsrc, ite_eq_right hc]
    have hpaccess := index_address_access q cap indexWords spill words (saved spill pointer state).toNat hl haddress
    have hregaccess := hl.spill_access register
    have htarget : packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap) < spill := by
      have hb := hl.base
      omega
    have hne : spill + register.word ≠ packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap) := by omega
    rw [Function.update_of_ne ((ofNat_injective_of_fit _ _ (hregaccess.trans hl.footprint) (hpaccess.trans hl.footprint)).not.mpr hne)]
    exact hreg

theorem writeMacro_correct {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (haddress : (saved spill pointer state).toNat < cap + indexWords)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    PackedAccessSafe words rom (writeMacro q bits cap spill pointer source) state ∧
      CapacitySafe q cap rom (writeMacro q bits cap spill pointer source) state ∧
      (∀ other < cap + indexWords,
        unpackHeap q cap bits (executeOps rom (writeMacro q bits cap spill pointer source) state).heap other =
          (Function.update (unpackHeap q cap bits state.heap) (saved spill pointer state).toNat (saved spill source state).toNat) other) ∧
      ∀ register, saved spill register (executeOps rom (writeMacro q bits cap spill pointer source) state) = saved spill register state :=
  ⟨writeMacro_accessSafe q cap indexWords spill words pointer source rom state hl haddress hsource hbound,
    writeMacro_capacitySafe q cap indexWords spill words pointer source rom state hl haddress hsource hbound,
    writeMacro_decoded q cap indexWords spill words pointer source rom state hl haddress hsource hbound,
    fun register => writeMacro_spill_frame q cap indexWords spill words pointer source register rom state hl haddress hsource hbound⟩

end PaperProofs.Structure.LaminarTree.PA17PackedStore042d
