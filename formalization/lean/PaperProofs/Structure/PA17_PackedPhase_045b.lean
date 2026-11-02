module

public import PaperProofs.Structure.PA17_PackedPhase_045a
public import PaperProofs.Structure.PA17_PackingBounds_043

/-! Code-word Fits for the actual immutable translation AST. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedPhase045

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034

theorem packingCode_fit_append {bits : Nat} (left right : List PackingOp)
    (hl : WordsFit bits (packingCode left)) (hr : WordsFit bits (packingCode right)) :
    WordsFit bits (packingCode (left ++ right)) := by
  intro value hv
  rw [packingCode, List.flatMap_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · exact hl value (List.mem_append.mpr (Or.inl hv))
    · exact hr value (List.mem_append.mpr (Or.inl hv))
  · exact hl value (List.mem_append.mpr (Or.inr hv))

theorem base_program_codeFit (bits : Nat) (ops : List Op) (h : WordsFit bits (haltingWords ops)) :
    WordsFit bits (packingCode (ops.map PackingOp.base)) := by
  simpa only [packingCode, haltingWords, IndexedClosureRAM.programWords, List.flatMap_map,
    Function.comp_def, PackingOp.encode] using h

theorem loadReg_codeFit {bits : Nat} (spillBase : Nat) (source target : Register)
    (hsmall : Fits bits 8) (hfit : Fits bits (spillBase + source.word)) :
    WordsFit bits (packingCode (loadReg spillBase source target)) := by
  apply base_program_codeFit bits [.base (.constant .total (spillBase + source.word)), .base (.loadHeap target .total)]
  apply PA17WordBounds023.haltingWords_fit bits _ hsmall
  intro op ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact hfit
  · trivial

theorem saveReg_codeFit {bits : Nat} (spillBase : Nat) (target : Register)
    (hsmall : Fits bits 8) (hfit : Fits bits (spillBase + target.word)) :
    WordsFit bits (packingCode (saveReg spillBase target)) := by
  apply base_program_codeFit bits [.base (.constant .total (spillBase + target.word)), .base (.storeHeap .total .value)]
  apply PA17WordBounds023.haltingWords_fit bits _ hsmall
  intro op ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact hfit
  · trivial

theorem capAddress_codeFit {bits : Nat} (capWords spillBase : Nat) (pointer : Register)
    (hsmall : Fits bits 8) (hcap : Fits bits capWords) (hspill : Fits bits (spillBase + spillWords)) :
    WordsFit bits (packingCode (capAddress capWords spillBase pointer)) := by
  apply packingCode_fit_append
  · exact loadReg_codeFit spillBase pointer .address hsmall (spill_slot_fits spillBase hspill pointer)
  · apply base_program_codeFit bits [.base (.constant .total capWords), .subtract .flag .total .address,
        .base (.constant .fresh 0), .base (.select .address .flag .address .fresh)]
    apply PA17WordBounds023.haltingWords_fit bits _ hsmall
    intro op ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact hcap
    · trivial
    · exact lt_of_le_of_lt (by omega) hsmall
    · trivial

theorem indexAddress_codeFit {bits : Nat} (q capWords spillBase : Nat) (pointer : Register)
    (hsmall : Fits bits 8) (hcap : Fits bits capWords) (hspill : Fits bits (spillBase + spillWords))
    (hpacked : Fits bits (packedCapacityWords q capWords bits)) :
    WordsFit bits (packingCode (indexAddress q bits capWords spillBase pointer)) := by
  apply packingCode_fit_append
  · exact loadReg_codeFit spillBase pointer .address hsmall (spill_slot_fits spillBase hspill pointer)
  · apply base_program_codeFit bits [.base (.constant .total capWords), .subtract .fresh .address .total,
        .base (.constant .old (packedCapacityWords q capWords bits)), .base (.add .index .old .fresh)]
    apply PA17WordBounds023.haltingWords_fit bits _ hsmall
    intro op ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact hcap
    · trivial
    · exact hpacked
    · trivial

theorem base_list_codeFit (bits : Nat) (ops : List Op) (hsmall : Fits bits 8)
    (himm : ∀ op ∈ ops, PA17WordBounds023.ImmediateFits bits op) :
    WordsFit bits (packingCode (ops.map PackingOp.base)) :=
  base_program_codeFit bits ops (PA17WordBounds023.haltingWords_fit bits ops hsmall himm)

theorem readMacro_codeFit {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hcap : Fits bits capWords) (hspill : Fits bits (spillBase + spillWords))
    (hpacked : Fits bits (packedCapacityWords q capWords bits)) :
    WordsFit bits (packingCode (readMacro q bits capWords spillBase target pointer)) := by
  have hsmall : Fits bits 8 := lt_of_lt_of_le (by decide : 8 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) hbits)
  rw [readMacro]
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  · exact capAddress_codeFit capWords spillBase pointer hsmall hcap hspill
  · exact readProgram_code_fit q (by omega) hwidth
  · exact indexAddress_codeFit q capWords spillBase pointer hsmall hcap hspill hpacked
  · exact base_list_codeFit bits [.base (.loadHeap .fresh .index), .base (.select .value .flag .value .fresh)] hsmall
      (by simp [PA17WordBounds023.ImmediateFits])
  · exact saveReg_codeFit spillBase target hsmall (spill_slot_fits spillBase hspill target)

theorem writeMacro_codeFit {bits : Nat} (q capWords spillBase : Nat) (pointer source : Register)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hcap : Fits bits capWords) (hspill : Fits bits (spillBase + spillWords))
    (hpacked : Fits bits (packedCapacityWords q capWords bits)) :
    WordsFit bits (packingCode (writeMacro q bits capWords spillBase pointer source)) := by
  have hsmall : Fits bits 8 := lt_of_lt_of_le (by decide : 8 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) hbits)
  rw [writeMacro]
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  · exact capAddress_codeFit capWords spillBase pointer hsmall hcap hspill
  · exact readProgram_code_fit q (by omega) hwidth
  · exact loadReg_codeFit spillBase source .fresh hsmall (spill_slot_fits spillBase hspill source)
  · exact base_list_codeFit bits [.base (.select .value .flag .fresh .value)] hsmall (by simp [PA17WordBounds023.ImmediateFits])
  · exact safeWriteProgram_code_fit q hbits hwidth
  · exact indexAddress_codeFit q capWords spillBase pointer hsmall hcap hspill hpacked
  · exact base_list_codeFit bits [.subtract .flag .total .address, .base (.loadHeap .old .index)] hsmall
      (by simp [PA17WordBounds023.ImmediateFits])
  · exact loadReg_codeFit spillBase source .fresh hsmall (spill_slot_fits spillBase hspill source)
  · exact base_list_codeFit bits [.base (.select .value .flag .old .fresh), .base (.storeHeap .index .value)] hsmall
      (by simp [PA17WordBounds023.ImmediateFits])

theorem physicalWipe_codeFit {bits : Nat} (spillBase : Nat) (hsmall : Fits bits 8)
    (hspill : Fits bits (spillBase + spillWords)) :
    WordsFit bits (packingCode (physicalWipe spillBase)) := by
  apply base_program_codeFit bits (wipe spillBase)
  apply PA17WordBounds023.haltingWords_fit bits _ hsmall
  intro op ho
  simp only [wipe, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with (rfl | ho) | rfl
  · exact lt_of_le_of_lt (by omega) hsmall
  · obtain ⟨index, hi, hop⟩ := List.mem_flatMap.mp ho
    have hr : index < spillWords := List.mem_range.mp hi
    simp only [wipeBlock, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · unfold PA17WordBounds023.ImmediateFits Fits at *
      omega
    · trivial
  · exact lt_of_le_of_lt (by omega) hsmall

theorem restore_codeFit {bits : Nat} (spillBase : Nat) (hsmall : Fits bits 8)
    (hspill : Fits bits (spillBase + spillWords)) :
    WordsFit bits (packingCode (restore spillBase)) := by
  simp only [restore, restoredRegisters, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  repeat' first
    | apply packingCode_fit_append
    | exact loadReg_codeFit _ _ _ hsmall (spill_slot_fits spillBase hspill _)

theorem translateOp_codeFit {bits : Nat} (q capWords spillBase : Nat) (op : Op)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hcap : Fits bits capWords) (hspill : Fits bits (spillBase + spillWords))
    (hpacked : Fits bits (packedCapacityWords q capWords bits))
    (himm : PA17WordBounds023.ImmediateFits bits op) :
    WordsFit bits (packingCode (translateOp q bits capWords spillBase op)) := by
  have hsmall : Fits bits 8 := lt_of_lt_of_le (by decide : 8 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) hbits)
  have hload (source target : Register) := loadReg_codeFit spillBase source target hsmall (spill_slot_fits spillBase hspill source)
  have hsave (target : Register) := saveReg_codeFit spillBase target hsmall (spill_slot_fits spillBase hspill target)
  cases op with
  | base instruction =>
    cases instruction with
    | loadHeap target pointer => exact readMacro_codeFit q capWords spillBase target pointer hbits hwidth hcap hspill hpacked
    | storeHeap pointer source => exact writeMacro_codeFit q capWords spillBase pointer source hbits hwidth hcap hspill hpacked
    | constant target value =>
      apply packingCode_fit_append
      · exact base_list_codeFit bits [.base (.constant .value value)] hsmall (by simpa [PA17WordBounds023.ImmediateFits] using himm)
      · exact hsave target
    | add target left right =>
      repeat' apply packingCode_fit_append
      · exact hload left .old
      · exact hload right .fresh
      · exact base_list_codeFit bits [.base (.add .value .old .fresh)] hsmall (by simp [PA17WordBounds023.ImmediateFits])
      · exact hsave target
    | minimum target left right =>
      repeat' apply packingCode_fit_append
      · exact hload left .old
      · exact hload right .fresh
      · exact base_list_codeFit bits [.base (.minimum .value .old .fresh)] hsmall (by simp [PA17WordBounds023.ImmediateFits])
      · exact hsave target
    | select target condition whenTrue whenFalse =>
      repeat' apply packingCode_fit_append
      · exact hload condition .flag
      · exact hload whenTrue .old
      · exact hload whenFalse .fresh
      · exact base_list_codeFit bits [.base (.select .value .flag .old .fresh)] hsmall (by simp [PA17WordBounds023.ImmediateFits])
      · exact hsave target
    | loadROM region target pointer =>
      repeat' apply packingCode_fit_append
      · exact hload pointer .index
      · exact base_list_codeFit bits [.base (.loadROM region .value .index)] hsmall (by simp [PA17WordBounds023.ImmediateFits])
      · exact hsave target
  | subtract target left right =>
    repeat' apply packingCode_fit_append
    · exact hload left .old
    · exact hload right .fresh
    · exact base_list_codeFit bits [.subtract .value .old .fresh] hsmall (by simp [PA17WordBounds023.ImmediateFits])
    · exact hsave target

theorem packedProgram_codeFit {bits : Nat} (q capWords indexWords heapWords : Nat)
    (body : List Op) (rom : PhysicalROM) (state : State)
    (hl : PA17PackedStore042b.Layout q capWords indexWords
      (physicalSpillBase q bits capWords indexWords) heapWords bits)
    (hregister : ∀ count ≤ body.length, ∀ register,
      Fits bits ((execute rom.semantic (body.take count) state).register register)) :
    WordsFit bits (packingCode (packedProgram q bits capWords indexWords body)) := by
  let spill := physicalSpillBase q bits capWords indexWords
  have hsmall : Fits bits 8 := lt_of_lt_of_le (by decide : 8 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) hl.bits_min)
  have hspill : Fits bits (spill + spillWords) := lt_of_le_of_lt hl.allocation hl.footprint
  have hpacked : Fits bits (packedCapacityWords q capWords bits) := by
    unfold Fits at *
    have := hl.base
    omega
  have himm (op : Op) (ho : op ∈ body) : PA17WordBounds023.ImmediateFits bits op := by
    obtain ⟨index, hi, heq⟩ := List.getElem_of_mem ho
    cases op with
    | subtract _ _ _ => trivial
    | base instruction =>
      cases instruction with
      | constant target value =>
        have hr := hregister (index + 1) (by omega) target
        rw [PA17WordExecution021.execute_take_succ rom.semantic body index hi state, heq] at hr
        simpa only [PA17WordBounds023.ImmediateFits, Op.execute, Instruction.execute, Function.update_self] using hr
      | add _ _ _ => trivial
      | minimum _ _ _ => trivial
      | select _ _ _ _ => trivial
      | loadROM _ _ _ => trivial
      | loadHeap _ _ => trivial
      | storeHeap _ _ => trivial
  have hmiddleAux (entries : List Op) (hi : ∀ op ∈ entries, PA17WordBounds023.ImmediateFits bits op) :
      WordsFit bits (packingCode (entries.flatMap (translateOp q bits capWords spill))) := by
    induction entries with
    | nil => exact base_list_codeFit bits [] hsmall (by simp)
    | cons op later ih =>
      rw [List.flatMap_cons]
      exact packingCode_fit_append _ _
        (translateOp_codeFit q capWords spill op hl.bits_min hl.width hl.cap_fit hspill hpacked (hi op List.mem_cons_self))
        (ih (fun entry he => hi entry (List.mem_cons_of_mem _ he)))
  rw [packedProgram]
  apply packingCode_fit_append
  apply packingCode_fit_append
  apply packingCode_fit_append
  · exact physicalWipe_codeFit spill hsmall hspill
  · exact hmiddleAux body himm
  · exact restore_codeFit spill hsmall hspill
  · exact physicalWipe_codeFit spill hsmall hspill

end PaperProofs.Structure.LaminarTree.PA17PackedPhase045
