module

public import PaperProofs.Structure.PA17_PackedTranslator_034j

/-! Final restoration and concrete whole-program data refinement. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

theorem restore_take_heap {bits : Nat} (spillBase : Nat) (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ (restore spillBase).length) :
    (executeOps rom ((restore spillBase).take count) state).heap = state.heap := by
  change count ≤ 10 at hc
  interval_cases count <;> rfl

theorem restore_accessSafe {bits : Nat} (spillBase heapWords : Nat) (rom : PhysicalROM)
    (state : WordState bits) (halloc : spillBase + spillWords ≤ heapWords) (hfit : Fits bits heapWords) :
    PackedAccessSafe heapWords rom (restore spillBase) state := by
  have hr (register : Register) (current : WordState bits) :
      PackedAccessSafe heapWords rom (loadReg spillBase register register) current := by
    have hw := register_word_lt register
    exact loadReg_accessSafe heapWords spillBase register register rom current
      (by unfold Fits at *; omega) (by omega)
  simp only [restore, restoredRegisters, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  repeat' first
    | apply PackedAccessSafe.append
    | exact hr _ _

theorem restore_capacitySafe {bits : Nat} (q capWords spillBase : Nat) (rom : PhysicalROM)
    (state : WordState bits) (hbound : CapacityPrefixBounded q capWords (unpackHeap q capWords bits state.heap)) :
    PA17PackedStore042b.CapacitySafe q capWords rom (restore spillBase) state := by
  intro count hc
  rw [restore_take_heap spillBase rom state count hc]
  exact hbound

theorem restore_wipe_registers {bits : Nat} (q capWords indexWords spillBase : Nat)
    (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical) :
    ∀ register, ((executeOps rom (restore spillBase ++ physicalWipe spillBase) physical).register register).toNat =
      (execute rom.semantic (wipe (capWords + indexWords)) logical).register register := by
  intro register
  rw [restore_physicalWipe_register, wipe_register]
  split_ifs with heq
  · rfl
  · exact hs.registers register

theorem restore_wipe_heap {bits : Nat} (q capWords indexWords spillBase : Nat)
    (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfit : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q)) :
    ∀ address < capWords + newIndexWords indexWords,
      unpackHeap q capWords bits (executeOps rom (restore spillBase ++ physicalWipe spillBase) physical).heap address =
        (execute rom.semantic (wipe (capWords + indexWords)) logical).heap address := by
  intro address ha
  rw [executeOps_append]
  by_cases hold : address < capWords + indexWords
  · have hp := physicalWipe_take_old_heap q capWords indexWords spillBase rom
      (executeOps rom (restore spillBase) physical) hbits hbase hfit hregion (physicalWipe spillBase).length le_rfl address hold
    rw [List.take_length, restore_heap] at hp
    rw [hp, hs.heap address hold, wipe_frame rom.semantic (capWords + indexWords) logical address (Or.inl hold)]
  · obtain ⟨offset, heq⟩ := Nat.exists_eq_add_of_le (show capWords + indexWords ≤ address by omega)
    have hoff : offset < spillWords := by unfold newIndexWords at ha; omega
    rw [heq, physicalWipe_decoded_zero q capWords indexWords spillBase rom _ hbase hfit offset hoff,
      wipe_zero rom.semantic (capWords + indexWords) logical offset hoff]

theorem restore_wipe_safe {bits : Nat} (q capWords indexWords spillBase heapWords : Nat)
    (rom : PhysicalROM) (state : WordState bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords spillBase heapWords bits)
    (hbound : CapacityPrefixBounded q capWords (unpackHeap q capWords bits state.heap)) :
    PackedAccessSafe heapWords rom (restore spillBase ++ physicalWipe spillBase) state ∧
      PA17PackedStore042b.CapacitySafe q capWords rom (restore spillBase ++ physicalWipe spillBase) state := by
  constructor
  · exact PackedAccessSafe.append heapWords rom _ _ state
      (restore_accessSafe spillBase heapWords rom state hl.allocation hl.footprint)
      (physicalWipe_accessSafe spillBase heapWords rom _ hl.allocation hl.footprint)
  · apply PA17PackedStore042b.CapacitySafe.append q capWords rom _ _ state
    · exact restore_capacitySafe q capWords spillBase rom state hbound
    · apply physicalWipe_capacitySafe q capWords indexWords spillBase rom _
        (by have := hl.bits_min; omega) hl.base (lt_of_le_of_lt hl.allocation hl.footprint) hl.region_fit
      rw [restore_heap]
      exact hbound

theorem packedProgram_data_correct {bits : Nat} (q capWords indexWords heapWords : Nat)
    (body : List Op) (rom : PhysicalROM) (heap : BitVec bits → BitVec bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords
      (physicalSpillBase q bits capWords indexWords) heapWords bits)
    (hregister : ∀ count ≤ body.length, ∀ register,
      Fits bits ((execute rom.semantic (body.take count)
        (execute rom.semantic (wipe (capWords + indexWords))
          (initial (unpackHeap q capWords bits heap)))).register register))
    (haccess : ∀ count (hc : count < body.length),
      AccessFits rom (capWords + indexWords)
        (execute rom.semantic (body.take count)
          (execute rom.semantic (wipe (capWords + indexWords))
            (initial (unpackHeap q capWords bits heap)))) body[count])
    (hcapacity : CapacityThroughout q capWords rom body
      (execute rom.semantic (wipe (capWords + indexWords))
        (initial (unpackHeap q capWords bits heap)))) :
    PackedAccessSafe heapWords rom (packedProgram q bits capWords indexWords body) (packingInitial heap) ∧
      PA17PackedStore042b.CapacitySafe q capWords rom
        (packedProgram q bits capWords indexWords body) (packingInitial heap) ∧
      (∀ register, ((executeOps rom (packedProgram q bits capWords indexWords body) (packingInitial heap)).register register).toNat =
        (execute rom.semantic (logicalProgram (capWords + indexWords) body)
          (initial (unpackHeap q capWords bits heap))).register register) ∧
      ∀ address < capWords + newIndexWords indexWords,
        unpackHeap q capWords bits (executeOps rom (packedProgram q bits capWords indexWords body) (packingInitial heap)).heap address =
          (execute rom.semantic (logicalProgram (capWords + indexWords) body)
            (initial (unpackHeap q capWords bits heap))).heap address := by
  let spill := physicalSpillBase q bits capWords indexWords
  let front := physicalWipe spill
  let middle := body.flatMap (translateOp q bits capWords spill)
  let tail := restore spill ++ physicalWipe spill
  let pre := execute rom.semantic (wipe (capWords + indexWords)) (initial (unpackHeap q capWords bits heap))
  let initialized := executeOps rom front (packingInitial heap)
  have hbits : 0 < bits := by have := hl.bits_min; omega
  have hfit : Fits bits (spill + spillWords) := lt_of_le_of_lt hl.allocation hl.footprint
  have hs := physicalWipe_initial_sim q capWords indexWords spill rom heap hbits hl.base hfit hl.region_fit
  have hm := translateBody_correct q capWords indexWords spill heapWords body rom pre initialized hl hs
    hregister haccess hcapacity
  have hbound : CapacityPrefixBounded q capWords (unpackHeap q capWords bits heap) := by
    intro address ha
    have hh := hcapacity 0 (by omega) address ha
    change pre.heap address ≤ q at hh
    dsimp only [pre] at hh
    rw [wipe_frame rom.semantic (capWords + indexWords) _ address (Or.inl (by omega))] at hh
    exact hh
  have hfrontAccess := physicalWipe_accessSafe spill heapWords rom (packingInitial heap) hl.allocation hl.footprint
  have hfrontCap := physicalWipe_capacitySafe q capWords indexWords spill rom (packingInitial heap)
    hbits hl.base hfit hl.region_fit hbound
  have hmiddleCap : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (executeOps rom middle initialized).heap) := by
    have hh := hm.2.1 middle.length le_rfl
    change CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (executeOps rom (middle.take middle.length) initialized).heap) at hh
    simpa only [List.take_length] using hh
  have ht := restore_wipe_safe q capWords indexWords spill heapWords rom
    (executeOps rom middle initialized) hl hmiddleCap
  have hcode : packedProgram q bits capWords indexWords body = front ++ (middle ++ tail) := by
    simp only [packedProgram, front, middle, tail, spill, List.append_assoc]
  rw [hcode]
  refine ⟨PackedAccessSafe.append heapWords rom front (middle ++ tail) (packingInitial heap) hfrontAccess
      (PackedAccessSafe.append heapWords rom middle tail initialized hm.1 ht.1),
    PA17PackedStore042b.CapacitySafe.append q capWords rom front (middle ++ tail) (packingInitial heap) hfrontCap
      (PA17PackedStore042b.CapacitySafe.append q capWords rom middle tail initialized hm.2.1 ht.2), ?_, ?_⟩
  · rw [executeOps_append, executeOps_append, logicalProgram_execute]
    exact restore_wipe_registers q capWords indexWords spill rom (execute rom.semantic body pre)
      (executeOps rom middle initialized) hm.2.2
  · rw [executeOps_append, executeOps_append, logicalProgram_execute]
    exact restore_wipe_heap q capWords indexWords spill rom (execute rom.semantic body pre)
      (executeOps rom middle initialized) hm.2.2 hbits hl.base hfit hl.region_fit

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
