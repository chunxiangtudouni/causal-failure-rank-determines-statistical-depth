module
public import PaperProofs.Structure.PA17_PackedStore_042b

/-! Actual final twelve instructions of write87: both index paths execute,
with the old word stored back on the capacity branch. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
namespace PaperProofs.Structure.LaminarTree.PA17PackedStore042c

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034
open PA17PackedStore042a PA17PackedStore042b

theorem writeTail_heap {bits : Nat} (q cap spill : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hcap : Fits bits cap) :
    (executeOps rom (writeTail q bits cap spill pointer source) state).heap =
      Function.update state.heap
        (BitVec.ofNat bits (packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap)))
        (if (saved spill pointer state).toNat < cap then
          state.heap (BitVec.ofNat bits (packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap)))
         else saved spill source state) := by
  let indexed := executeOps rom (indexAddress q bits cap spill pointer) state
  let compared := executeOps rom [.base (.subtract .flag .total .address), .base (.base (.loadHeap .old .index))] indexed
  let sourced := executeOps rom (loadReg spill source .fresh) compared
  have hiHeap : indexed.heap = state.heap := indexAddress_heap q cap spill pointer rom state
  have hiIndex : indexed.register .index = BitVec.ofNat bits (packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap)) :=
    indexAddress_index q cap spill pointer rom state hcap
  have hiAddress : indexed.register .address = saved spill pointer state := indexAddress_address q cap spill pointer rom state
  have hiTotal : indexed.register .total = BitVec.ofNat bits cap := indexAddress_total q cap spill pointer rom state
  have hcFlag : compared.register .flag = BitVec.ofNat bits (cap - (saved spill pointer state).toNat) := by
    change BitVec.ofNat bits ((indexed.register .total).toNat - (indexed.register .address).toNat) = _
    rw [hiTotal, hiAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap]
  have hcOld : compared.register .old = state.heap (BitVec.ofNat bits (packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap))) := by
    change indexed.heap (indexed.register .index) = _
    rw [hiHeap, hiIndex]
  have hcIndex : compared.register .index = indexed.register .index := rfl
  have hcHeap : compared.heap = indexed.heap := rfl
  have hsHeap : sourced.heap = state.heap := by dsimp only [sourced]; rw [loadReg_heap, hcHeap, hiHeap]
  have hsIndex : sourced.register .index = BitVec.ofNat bits (packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap)) := by
    dsimp only [sourced]
    rw [loadReg_register_frame spill source .fresh rom compared .index (by decide) (by decide), hcIndex, hiIndex]
  have hsFlag : sourced.register .flag = BitVec.ofNat bits (cap - (saved spill pointer state).toNat) := by
    dsimp only [sourced]
    rw [loadReg_register_frame spill source .fresh rom compared .flag (by decide) (by decide), hcFlag]
  have hsOld : sourced.register .old = state.heap (BitVec.ofNat bits (packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap))) := by
    dsimp only [sourced]
    rw [loadReg_register_frame spill source .fresh rom compared .old (by decide) (by decide), hcOld]
  have hsFresh : sourced.register .fresh = saved spill source state := by
    dsimp only [sourced]
    rw [loadReg_value, hcHeap, hiHeap]
    rfl
  have hwhole : executeOps rom (writeTail q bits cap spill pointer source) state =
      executeOps rom [.base (.base (.select .value .flag .old .fresh)), .base (.base (.storeHeap .index .value))] sourced := by
    simp only [writeTail, executeOps_append]
    rfl
  rw [hwhole]
  change Function.update sourced.heap (sourced.register .index)
    (if (sourced.register .flag).toNat = 0 then sourced.register .fresh else sourced.register .old) = _
  rw [hsHeap, hsIndex, hsFlag, hsOld, hsFresh]
  have hf : cap - (saved spill pointer state).toNat < 2 ^ bits := (Nat.sub_le _ _).trans_lt hcap
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  by_cases ha : (saved spill pointer state).toNat < cap
  · have hn : cap - (saved spill pointer state).toNat ≠ 0 := by omega
    simp only [ha, hn, ite_false, ite_true]
  · have hz : cap - (saved spill pointer state).toNat = 0 := by omega
    simp only [ha, hz, ite_true, ite_false]

theorem writeTail_heap_capacity {bits : Nat} (q cap spill : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hcap : Fits bits cap)
    (ha : (saved spill pointer state).toNat < cap) :
    (executeOps rom (writeTail q bits cap spill pointer source) state).heap = state.heap := by
  rw [writeTail_heap q cap spill pointer source rom state hcap, ite_eq_left ha]
  funext address
  by_cases he : address = BitVec.ofNat bits (packedCapacityWords q cap bits + ((saved spill pointer state).toNat - cap))
  · rw [he, Function.update_self]
  · rw [Function.update_of_ne he]

theorem index_address_access {bits : Nat} (q cap indexWords spill words address : Nat)
    (hl : Layout q cap indexWords spill words bits) (ha : address < cap + indexWords) :
    packedCapacityWords q cap bits + (address - cap) < words := by
  have hbase := hl.base
  have halloc := hl.allocation
  simp only [spillWords] at halloc
  omega

theorem capacity_write_decoded {bits : Nat} (q cap indexWords spill words address : Nat)
    (hl : Layout q cap indexWords spill words bits) (ha : address < cap) (value : BitVec bits)
    (hv : value.toNat ≤ q) (heap : BitVec bits → BitVec bits) (other : Nat) (ho : other < cap + indexWords) :
    unpackHeap q cap bits (writeHeap (CapacityBits.width q) (address * CapacityBits.width q) value heap) other =
      (Function.update (unpackHeap q cap bits heap) address value.toNat) other := by
  have hbits : 0 < bits := by have := hl.bits_min; omega
  have hlook := packed_lookahead_le q cap bits address hbits ha
  have hnext : Fits bits (address * CapacityBits.width q / bits + 1) := by
    have hbase := hl.base
    have halloc := hl.allocation
    simp only [spillWords] at halloc
    apply lt_of_lt_of_le _ (Nat.le_of_lt hl.footprint)
    omega
  have hvalue := CapacityBits.value_lt_two_pow_width q _ hv
  by_cases he : other = address
  · subst other
    rw [Function.update_self]
    exact unpackHeap_write_target q cap address value heap hbits hl.width ha hnext hvalue
  · rw [Function.update_of_ne he]
    by_cases hoc : other < cap
    · exact unpackHeap_write_other_capacity q cap address other value heap hbits hl.width hnext hl.region_fit hvalue hoc he
    · exact unpackHeap_write_index q cap address other value heap hbits hl.width ha (by omega) hnext
        ((index_address_access q cap indexWords spill words other hl ho).trans hl.footprint) hvalue

theorem writePrefix_decoded {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) (other : Nat) (ho : other < cap + indexWords) :
    unpackHeap q cap bits (executeOps rom (writePrefix q bits cap spill pointer source) state).heap other =
      if (saved spill pointer state).toNat < cap then
        (Function.update (unpackHeap q cap bits state.heap) (saved spill pointer state).toNat (saved spill source state).toNat) other
      else unpackHeap q cap bits state.heap other := by
  let selected := executeOps rom (selectInput q bits cap spill pointer source) state
  have hbits : 0 < bits := by have := hl.bits_min; omega
  have hchosen := chosenAddress_lt cap (saved spill pointer state).toNat hl.cap_pos
  have ha : (selected.register .address).toNat < cap := by
    rw [selectInput_address q cap spill pointer source rom state hl.cap_fit, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hchosen.trans hl.cap_fit)]
    exact hchosen
  have hv := selectInput_capacityBound q cap spill pointer source rom state hbits hl.width hl.cap_fit hl.cap_pos hsource hbound
  rw [writePrefix_heap q cap indexWords spill words pointer source rom state hl,
    capacity_write_decoded q cap indexWords spill words _ hl ha _ hv state.heap other ho]
  have haddr : (selected.register .address).toNat = chosenAddress cap (saved spill pointer state).toNat := by
    rw [selectInput_address q cap spill pointer source rom state hl.cap_fit, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hchosen.trans hl.cap_fit)]
  have hval := selectInput_value q cap spill pointer source rom state hbits hl.width hl.cap_fit hl.cap_pos
  change (selected.register .value).toNat = _ at hval
  rw [haddr, hval]
  by_cases hc : (saved spill pointer state).toNat < cap
  · simp only [hc, chosenAddress, ite_true]
  · simp only [hc, chosenAddress, ite_false]
    by_cases he : other = 0
    · subst other; rw [Function.update_self]
    · rw [Function.update_of_ne he]

theorem index_store_decoded {bits : Nat} (q cap indexWords spill words address : Nat)
    (hl : Layout q cap indexWords spill words bits) (ha : cap ≤ address) (had : address < cap + indexWords)
    (value : BitVec bits) (heap : BitVec bits → BitVec bits) (other : Nat) (ho : other < cap + indexWords) :
    unpackHeap q cap bits (Function.update heap (BitVec.ofNat bits (packedCapacityWords q cap bits + (address - cap))) value) other =
      (Function.update (unpackHeap q cap bits heap) address value.toNat) other := by
  have hp := index_address_access q cap indexWords spill words address hl had
  have hfit := hp.trans hl.footprint
  by_cases he : other = address
  · subst other
    rw [unpackHeap, ite_eq_right (not_lt_of_ge ha), Function.update_self, Function.update_self]
  · rw [Function.update_of_ne he]
    by_cases hoc : other < cap
    · exact index_update_capacity q cap _ value heap (by have := hl.bits_min; omega) hl.region_fit (Nat.le_add_right _ _) hfit other hoc
    · have hother := (index_address_access q cap indexWords spill words other hl ho).trans hl.footprint
      have hne : packedCapacityWords q cap bits + (other - cap) ≠ packedCapacityWords q cap bits + (address - cap) := by omega
      rw [unpackHeap, unpackHeap, ite_eq_right hoc, ite_eq_right hoc,
        Function.update_of_ne ((ofNat_injective_of_fit _ _ hother hfit).not.mpr hne)]

theorem writeMacro_decoded {bits : Nat} (q cap indexWords spill words : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hl : Layout q cap indexWords spill words bits)
    (haddress : (saved spill pointer state).toNat < cap + indexWords)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) (other : Nat) (ho : other < cap + indexWords) :
    unpackHeap q cap bits (executeOps rom (writeMacro q bits cap spill pointer source) state).heap other =
      (Function.update (unpackHeap q cap bits state.heap) (saved spill pointer state).toNat (saved spill source state).toNat) other := by
  let written := executeOps rom (writePrefix q bits cap spill pointer source) state
  have hptr := writePrefix_spill_frame q cap indexWords spill words pointer source pointer rom state hl hsource hbound
  have hsrc := writePrefix_spill_frame q cap indexWords spill words pointer source source rom state hl hsource hbound
  have hw := writePrefix_decoded q cap indexWords spill words pointer source rom state hl hsource hbound
  rw [writeMacro_split, executeOps_append]
  change unpackHeap q cap bits (executeOps rom (writeTail q bits cap spill pointer source) written).heap other = _
  by_cases hc : (saved spill pointer state).toNat < cap
  · rw [writeTail_heap_capacity q cap spill pointer source rom written hl.cap_fit (by rw [hptr]; exact hc)]
    simpa only [hc, ite_true] using hw other ho
  · rw [writeTail_heap q cap spill pointer source rom written hl.cap_fit, hptr, hsrc, ite_eq_right hc,
      index_store_decoded q cap indexWords spill words _ hl (by omega) haddress _ written.heap other ho]
    by_cases he : other = (saved spill pointer state).toNat
    · subst other
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      simpa only [hc, ite_false] using hw other ho

end PaperProofs.Structure.LaminarTree.PA17PackedStore042c
