module

public import PaperProofs.Structure.PA17_PackedTranslator_034g

/-! Concrete per-original-Op simulation. Logical arithmetic/ROM Ops use the
original word ISA; real heap loads/stores use read32/write87. The old heap
and all seven saved registers are related at each real macro boundary. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

structure SpillSim {bits : Nat} (q capWords indexWords spillBase : Nat) (logical : State) (physical : WordState bits) : Prop where
  registers : ∀ register, (savedRegisters spillBase physical.heap register).toNat = logical.register register
  heap : ∀ address < capWords + indexWords, unpackHeap q capWords bits physical.heap address = logical.heap address

theorem SpillSim.registers_fit {bits : Nat} {q capWords indexWords spillBase : Nat}
    {logical : State} {physical : WordState bits} (hs : SpillSim q capWords indexWords spillBase logical physical) :
    ∀ register, Fits bits (logical.register register) := by
  intro register
  rw [← hs.registers register]
  exact (savedRegisters spillBase physical.heap register).isLt

theorem SpillSim.virtual_registers {bits : Nat} {q capWords indexWords spillBase : Nat}
    {logical : State} {physical : WordState bits} (hs : SpillSim q capWords indexWords spillBase logical physical) :
    (virtualState spillBase physical).register = (wordState bits logical).register := by
  funext register
  change savedRegisters spillBase physical.heap register = BitVec.ofNat bits (logical.register register)
  rw [← hs.registers register]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem SpillSim.capacity {bits : Nat} {q capWords indexWords spillBase : Nat}
    {logical : State} {physical : WordState bits} (hs : SpillSim q capWords indexWords spillBase logical physical)
    (hbound : CapacityPrefixBounded q capWords logical.heap) :
    CapacityPrefixBounded q capWords (unpackHeap q capWords bits physical.heap) := by
  intro address ha
  rw [hs.heap address (by omega)]
  exact hbound address ha

theorem op_nonheap_heap (rom : ROM) (op : Op) (hn : NonHeapOp op) (state : State) :
    (op.execute rom state).heap = state.heap := by
  cases op with
  | base instruction =>
    cases instruction with
    | constant _ _ => rfl
    | add _ _ _ => rfl
    | minimum _ _ _ => rfl
    | select _ _ _ _ => rfl
    | loadROM _ _ _ => rfl
    | loadHeap _ _ => cases hn
    | storeHeap _ _ => cases hn
  | subtract _ _ _ => rfl

theorem nonheap_simulates {bits : Nat} (q capWords indexWords spillBase heapWords : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords spillBase heapWords bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical)
    (hafter : ∀ register, Fits bits ((op.execute rom.semantic logical).register register)) :
    SpillSim q capWords indexWords spillBase (op.execute rom.semantic logical)
      (executeOps rom (translateOp q bits capWords spillBase op) physical) := by
  have hfoot : Fits bits (spillBase + spillWords) := lt_of_le_of_lt hl.allocation hl.footprint
  have hw : (wordOp rom op (virtualState spillBase physical)).register =
      (wordState bits (op.execute rom.semantic logical)).register := by
    calc
      _ = (wordOp rom op (wordState bits logical)).register :=
        wordOp_nonheap_register_congr op hn rom _ _ hs.virtual_registers
      _ = _ := congrArg WordState.register (PA17WordExecution021.op_toWord bits rom op logical hs.registers_fit)
  have hv := (translateOp_nonheap_savedRegisters q capWords spillBase op hn rom physical hfoot).trans hw
  constructor
  · intro register
    rw [hv]
    exact Nat.mod_eq_of_lt (hafter register)
  · intro address ha
    rw [translateOp_nonheap_old_heap q capWords indexWords spillBase op hn rom physical
      (by have := hl.bits_min; omega) hl.base hfoot hl.region_fit address ha,
      op_nonheap_heap rom.semantic op hn logical]
    exact hs.heap address ha

theorem SpillSim.nonheap_access {bits : Nat} {q capWords indexWords spillBase : Nat}
    {logical : State} {physical : WordState bits} (hs : SpillSim q capWords indexWords spillBase logical physical)
    (heapWords : Nat) (op : Op) (hn : NonHeapOp op) (rom : PhysicalROM)
    (ha : AccessFits rom (capWords + indexWords) logical op) :
    packingAccessFits rom heapWords (virtualState spillBase physical) (.base op) := by
  cases op with
  | subtract _ _ _ => trivial
  | base instruction =>
    cases instruction with
    | constant _ _ => trivial
    | add _ _ _ => trivial
    | minimum _ _ _ => trivial
    | select _ _ _ _ => trivial
    | loadROM region target pointer =>
      change (savedRegisters spillBase physical.heap pointer).toNat < (rom.words region).length
      rw [hs.registers pointer]
      exact ha
    | loadHeap _ _ => cases hn
    | storeHeap _ _ => cases hn

theorem read_simulates {bits : Nat} (q capWords indexWords spillBase heapWords : Nat) (target pointer : Register)
    (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords spillBase heapWords bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical)
    (haddress : logical.register pointer < capWords + indexWords) :
    SpillSim q capWords indexWords spillBase ((Op.base (.loadHeap target pointer)).execute rom.semantic logical)
      (executeOps rom (readMacro q bits capWords spillBase target pointer) physical) := by
  have hfoot : Fits bits (spillBase + spillWords) := lt_of_le_of_lt hl.allocation hl.footprint
  have hv := readMacro_value q capWords spillBase target pointer rom physical (by have := hl.bits_min; omega)
    hl.width hl.cap_fit hl.region_fit
  have hp : (physical.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat = logical.register pointer := hs.registers pointer
  rw [hp, hs.heap (logical.register pointer) haddress] at hv
  have hsaved := readMacro_savedRegisters q capWords spillBase target pointer rom physical hfoot
  constructor
  · intro register
    change (savedRegisters spillBase (executeOps rom (readMacro q bits capWords spillBase target pointer) physical).heap register).toNat =
      Function.update logical.register target (logical.heap (logical.register pointer)) register
    rw [hsaved]
    by_cases heq : register = target
    · subst register
      simp only [Function.update_self]
      exact hv
    · simp only [Function.update_of_ne heq]
      exact hs.registers register
  · intro address ha
    have hf := readMacro_prefix_old_heap q capWords indexWords spillBase target pointer rom physical
      (by have := hl.bits_min; omega) hl.base hfoot hl.region_fit
      (readMacro q bits capWords spillBase target pointer).length le_rfl address ha
    rw [List.take_length] at hf
    exact hf.trans (hs.heap address ha)

theorem store_simulates {bits : Nat} (q capWords indexWords spillBase heapWords : Nat) (pointer source : Register)
    (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords spillBase heapWords bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical)
    (haddress : logical.register pointer < capWords + indexWords)
    (hbefore : CapacityPrefixBounded q capWords logical.heap)
    (hafter : CapacityPrefixBounded q capWords ((Op.base (.storeHeap pointer source)).execute rom.semantic logical).heap) :
    SpillSim q capWords indexWords spillBase ((Op.base (.storeHeap pointer source)).execute rom.semantic logical)
      (executeOps rom (writeMacro q bits capWords spillBase pointer source) physical) := by
  have hp : (PA17PackedStore042a.saved spillBase pointer physical).toNat = logical.register pointer := hs.registers pointer
  have hsrc : (PA17PackedStore042a.saved spillBase source physical).toNat = logical.register source := hs.registers source
  have hcapSource : (PA17PackedStore042a.saved spillBase pointer physical).toNat < capWords →
      (PA17PackedStore042a.saved spillBase source physical).toNat ≤ q := by
    rw [hp, hsrc]
    intro ha
    have hh := hafter (logical.register pointer) ha
    change Function.update logical.heap (logical.register pointer) (logical.register source) (logical.register pointer) ≤ q at hh
    simpa only [Function.update_self] using hh
  have hh := PA17PackedStore042d.writeMacro_correct q capWords indexWords spillBase heapWords pointer source rom physical hl
    (by rw [hp]; exact haddress) hcapSource (hs.capacity hbefore)
  constructor
  · intro register
    have hf := hh.2.2.2 register
    change savedRegisters spillBase (executeOps rom (writeMacro q bits capWords spillBase pointer source) physical).heap register =
      savedRegisters spillBase physical.heap register at hf
    change (savedRegisters spillBase (executeOps rom (writeMacro q bits capWords spillBase pointer source) physical).heap register).toNat =
      logical.register register
    rw [hf]
    exact hs.registers register
  · intro address ha
    have hv := hh.2.2.1 address ha
    rw [hp, hsrc] at hv
    change unpackHeap q capWords bits (executeOps rom (writeMacro q bits capWords spillBase pointer source) physical).heap address =
      Function.update logical.heap (logical.register pointer) (logical.register source) address
    by_cases heq : address = logical.register pointer
    · subst address
      simpa only [Function.update_self] using hv
    · simp only [Function.update_of_ne heq] at hv ⊢
      exact hv.trans (hs.heap address ha)

theorem translateOp_correct {bits : Nat} (q capWords indexWords spillBase heapWords : Nat) (op : Op)
    (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords spillBase heapWords bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical)
    (haccess : AccessFits rom (capWords + indexWords) logical op)
    (hafterFit : ∀ register, Fits bits ((op.execute rom.semantic logical).register register))
    (hbefore : CapacityPrefixBounded q capWords logical.heap)
    (hafter : CapacityPrefixBounded q capWords (op.execute rom.semantic logical).heap) :
    PackedAccessSafe heapWords rom (translateOp q bits capWords spillBase op) physical ∧
      PA17PackedStore042b.CapacitySafe q capWords rom (translateOp q bits capWords spillBase op) physical ∧
      SpillSim q capWords indexWords spillBase (op.execute rom.semantic logical)
        (executeOps rom (translateOp q bits capWords spillBase op) physical) := by
  have hfoot : Fits bits (spillBase + spillWords) := lt_of_le_of_lt hl.allocation hl.footprint
  have hb := hs.capacity hbefore
  by_cases hn : NonHeapOp op
  · exact ⟨translateOp_nonheap_accessSafe q capWords spillBase heapWords op hn rom physical hl.allocation hl.footprint
        (hs.nonheap_access heapWords op hn rom haccess),
      translateOp_nonheap_capacitySafe q capWords indexWords spillBase op hn rom physical
        (by have := hl.bits_min; omega) hl.base hfoot hl.region_fit hb,
      nonheap_simulates q capWords indexWords spillBase heapWords op hn rom logical physical hl hs hafterFit⟩
  · cases op with
    | subtract _ _ _ => exact False.elim (hn trivial)
    | base instruction =>
      cases instruction with
      | constant _ _ => exact False.elim (hn trivial)
      | add _ _ _ => exact False.elim (hn trivial)
      | minimum _ _ _ => exact False.elim (hn trivial)
      | select _ _ _ _ => exact False.elim (hn trivial)
      | loadROM _ _ _ => exact False.elim (hn trivial)
      | loadHeap target pointer =>
        have hp : (physical.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat = logical.register pointer := hs.registers pointer
        have ha : (physical.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < capWords + indexWords := by
          rw [hp]
          exact haccess
        exact ⟨readMacro_accessSafe q capWords indexWords spillBase heapWords target pointer rom physical hl.bits_min hl.width hl.cap_fit
            hl.region_fit hl.base hl.allocation hl.footprint ha,
          readMacro_capacitySafe q capWords spillBase target pointer rom physical (by have := hl.bits_min; omega)
            (by have := hl.base; omega) (spill_slot_fits spillBase hfoot target) hl.region_fit hb,
          read_simulates q capWords indexWords spillBase heapWords target pointer rom logical physical hl hs haccess⟩
      | storeHeap pointer source =>
        have hp : (PA17PackedStore042a.saved spillBase pointer physical).toNat = logical.register pointer := hs.registers pointer
        have hsrc : (PA17PackedStore042a.saved spillBase source physical).toNat = logical.register source := hs.registers source
        have hcapSource : (PA17PackedStore042a.saved spillBase pointer physical).toNat < capWords →
            (PA17PackedStore042a.saved spillBase source physical).toNat ≤ q := by
          rw [hp, hsrc]
          intro ha
          have hh := hafter (logical.register pointer) ha
          change Function.update logical.heap (logical.register pointer) (logical.register source) (logical.register pointer) ≤ q at hh
          simpa only [Function.update_self] using hh
        have hw := PA17PackedStore042d.writeMacro_correct q capWords indexWords spillBase heapWords pointer source rom physical hl
          (by rw [hp]; exact haccess) hcapSource hb
        exact ⟨hw.1, hw.2.1,
          store_simulates q capWords indexWords spillBase heapWords pointer source rom logical physical hl hs haccess hbefore hafter⟩

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
