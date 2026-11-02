module

public import PaperProofs.Structure.PA17_PackedTranslator_034f
public import PaperProofs.Structure.PA17_PackedStore_042d
public import PaperProofs.Structure.PA17_WordExecution_021

/-! Every ordinary translated macro has its actual allocated accesses.
The original ROM-pointer access is transported through the actual saved
register load. Scalar load/store macros retain their separate real proofs. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

theorem PackedAccessSafe.singleton {bits : Nat} (heapWords : Nat) (rom : PhysicalROM) (op : PackingOp)
    (state : WordState bits) (ha : packingAccessFits rom heapWords state op) :
    PackedAccessSafe heapWords rom [op] state := by
  intro count hc
  change count < 1 at hc
  have hz : count = 0 := by omega
  subst count
  exact ha

theorem twoRead_accessSafe {bits : Nat} (heapWords spillBase : Nat) (target left right : Register)
    (op : Op) (rom : PhysicalROM) (hop : ∀ state : WordState bits, packingAccessFits rom heapWords state (.base op))
    (state : WordState bits) (halloc : spillBase + spillWords ≤ heapWords) (hfoot : Fits bits heapWords) :
    PackedAccessSafe heapWords rom
      (loadReg spillBase left .old ++ loadReg spillBase right .fresh ++ [.base op] ++ saveReg spillBase target) state := by
  have hslot (register : Register) : spillBase + register.word < heapWords := by have := register_word_lt register; omega
  let first := executeOps rom (loadReg spillBase left .old) state
  let second := executeOps rom (loadReg spillBase right .fresh) first
  let evaluated := executeOps rom [.base op] second
  have h1 := loadReg_accessSafe heapWords spillBase left .old rom state ((hslot left).trans hfoot) (hslot left)
  have h2 := loadReg_accessSafe heapWords spillBase right .fresh rom first ((hslot right).trans hfoot) (hslot right)
  have h3 := PackedAccessSafe.singleton heapWords rom (.base op) second (hop second)
  have h4 := saveReg_accessSafe heapWords spillBase target rom evaluated ((hslot target).trans hfoot) (hslot target)
  simp only [List.append_assoc]
  exact PackedAccessSafe.append _ _ _ _ _ h1
    (PackedAccessSafe.append _ _ _ _ _ h2 (PackedAccessSafe.append _ _ _ _ _ h3 h4))

theorem translateOp_nonheap_accessSafe {bits : Nat} (q capWords spillBase heapWords : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (state : WordState bits)
    (halloc : spillBase + spillWords ≤ heapWords) (hfoot : Fits bits heapWords)
    (horiginal : packingAccessFits rom heapWords (virtualState spillBase state) (.base op)) :
    PackedAccessSafe heapWords rom (translateOp q bits capWords spillBase op) state := by
  have hslot (register : Register) : spillBase + register.word < heapWords := by have := register_word_lt register; omega
  cases op with
  | subtract target left right =>
    exact twoRead_accessSafe heapWords spillBase target left right (.subtract .value .old .fresh) rom (fun _ => trivial) state halloc hfoot
  | base instruction =>
    cases instruction with
    | constant target value =>
      have h1 := PackedAccessSafe.singleton heapWords rom (.base (.base (.constant .value value))) state trivial
      have h2 := saveReg_accessSafe heapWords spillBase target rom
        (executeOps rom [.base (.base (.constant .value value))] state) ((hslot target).trans hfoot) (hslot target)
      exact PackedAccessSafe.append _ _ _ _ _ h1 h2
    | add target left right =>
      exact twoRead_accessSafe heapWords spillBase target left right (.base (.add .value .old .fresh)) rom (fun _ => trivial) state halloc hfoot
    | minimum target left right =>
      exact twoRead_accessSafe heapWords spillBase target left right (.base (.minimum .value .old .fresh)) rom (fun _ => trivial) state halloc hfoot
    | select target condition whenTrue whenFalse =>
      let tested := executeOps rom (loadReg spillBase condition .flag) state
      let first := executeOps rom (loadReg spillBase whenTrue .old) tested
      let second := executeOps rom (loadReg spillBase whenFalse .fresh) first
      let evaluated := executeOps rom [.base (.base (.select .value .flag .old .fresh))] second
      have h1 := loadReg_accessSafe heapWords spillBase condition .flag rom state ((hslot condition).trans hfoot) (hslot condition)
      have h2 := loadReg_accessSafe heapWords spillBase whenTrue .old rom tested ((hslot whenTrue).trans hfoot) (hslot whenTrue)
      have h3 := loadReg_accessSafe heapWords spillBase whenFalse .fresh rom first ((hslot whenFalse).trans hfoot) (hslot whenFalse)
      have h4 := PackedAccessSafe.singleton heapWords rom (.base (.base (.select .value .flag .old .fresh))) second trivial
      have h5 := saveReg_accessSafe heapWords spillBase target rom evaluated ((hslot target).trans hfoot) (hslot target)
      simp only [translateOp, List.append_assoc]
      exact PackedAccessSafe.append _ _ _ _ _ h1
        (PackedAccessSafe.append _ _ _ _ _ h2 (PackedAccessSafe.append _ _ _ _ _ h3 (PackedAccessSafe.append _ _ _ _ _ h4 h5)))
    | loadROM region target pointer =>
      let addressed := executeOps rom (loadReg spillBase pointer .index) state
      let loaded := executeOps rom [.base (.base (.loadROM region .value .index))] addressed
      have h1 := loadReg_accessSafe heapWords spillBase pointer .index rom state ((hslot pointer).trans hfoot) (hslot pointer)
      have h2 : PackedAccessSafe heapWords rom [.base (.base (.loadROM region .value .index))] addressed := by
        apply PackedAccessSafe.singleton
        change (addressed.register .index).toNat < (rom.words region).length
        rw [loadReg_value]
        exact horiginal
      have h3 := saveReg_accessSafe heapWords spillBase target rom loaded ((hslot target).trans hfoot) (hslot target)
      simp only [translateOp, List.append_assoc]
      exact PackedAccessSafe.append _ _ _ _ _ h1 (PackedAccessSafe.append _ _ _ _ _ h2 h3)
    | loadHeap target pointer => cases hn
    | storeHeap pointer source => cases hn

theorem translateOp_nonheap_capacitySafe {bits : Nat} (q capWords indexWords spillBase : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfoot : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (hbound : CapacityPrefixBounded q capWords (unpackHeap q capWords bits state.heap)) :
    PA17PackedStore042b.CapacitySafe q capWords rom (translateOp q bits capWords spillBase op) state := by
  intro count hc address ha
  rw [translateOp_nonheap_prefix_old_heap q capWords indexWords spillBase op hn rom state hbits hbase hfoot hregion count hc address (by omega)]
  exact hbound address ha

theorem readMacro_capacitySafe {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hspill : packedCapacityWords q capWords bits ≤ spillBase) (hphysical : Fits bits (spillBase + target.word))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (hbound : CapacityPrefixBounded q capWords (unpackHeap q capWords bits state.heap)) :
    PA17PackedStore042b.CapacitySafe q capWords rom (readMacro q bits capWords spillBase target pointer) state := by
  intro count hc address ha
  rw [readMacro_prefix_capacity_frame q capWords spillBase target pointer rom state hbits hregion hspill hphysical count hc address ha]
  exact hbound address ha

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
