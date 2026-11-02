module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED actual fetched-prefix safety for the nine non-query chunks
of the same191-op leaf/tool producer. Every final PC is derived from its
actual instructions. Numeric premises are local block results, not a new
original-caller whole-run safety or metadata-output assumption. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (loadRel storeRel setRel incrementRel RunFacts)

theorem scan_chunk_final_offset (rom : PhysicalROM) (start : Nat) (chunk : ScanChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + scanChunkOffset chunk)) :
    ∃ offset ≤ 191, (runOps rom (scanChunkCode start chunk) state).pc = 5 * (start + offset) := by
  cases chunk with
  | «initialize» =>
    refine ⟨4, by decide, ?_⟩
    change (runOps rom scanInitialize state).pc = _
    rw [runOps_pc rom _ state (by simp [scanInitialize, setRel, storeRel, NoJump]),
      show scanInitialize.length = 4 by rfl, hpc]
    simp only [scanChunkOffset, Nat.add_zero]
    omega
  | outerTest =>
    have hp := scanBoundedTest_pc rom (state.register .address)
      (state.heap (state.register .address + 2)) (state.heap (state.register .address + 19))
      2 19 (start + 191) state rfl rfl rfl
    by_cases hz : state.heap (state.register .address + 2) - state.heap (state.register .address + 19) = 0
    · refine ⟨191, by decide, ?_⟩
      change (runOps rom (scanBoundedTest 2 19 (start + 191)) state).pc = _
      rw [hp, ite_eq_left hz]
    · refine ⟨13, by decide, ?_⟩
      change (runOps rom (scanBoundedTest 2 19 (start + 191)) state).pc = _
      rw [hp, ite_eq_right hz, hpc]
      simp only [scanChunkOffset]
      omega
  | rowInitialize =>
    refine ⟨51, by decide, ?_⟩
    change (runOps rom scanRowInitialize state).pc = _
    rw [runOps_pc rom _ state (by
      simp [scanRowInitialize, loadRel, storeRel, setRel, storeField, fieldPointer,
        fieldPointerLead, fieldPointerExtra, cardProgram, NoJump]),
      show scanRowInitialize.length = 38 by rfl, hpc]
    simp only [scanChunkOffset]
    omega
  | innerTest =>
    have hp := scanBoundedTest_pc rom (state.register .address)
      (state.heap (state.register .address + 1)) (state.heap (state.register .address + 20))
      1 20 (start + 180) state rfl rfl rfl
    by_cases hz : state.heap (state.register .address + 1) - state.heap (state.register .address + 20) = 0
    · refine ⟨180, by decide, ?_⟩
      change (runOps rom (scanBoundedTest 1 20 (start + 180)) state).pc = _
      rw [hp, ite_eq_left hz]
    · refine ⟨60, by decide, ?_⟩
      change (runOps rom (scanBoundedTest 1 20 (start + 180)) state).pc = _
      rw [hp, ite_eq_right hz, hpc]
      simp only [scanChunkOffset]
      omega
  | arguments =>
    refine ⟨66, by decide, ?_⟩
    change (runOps rom scanArguments state).pc = _
    rw [runOps_pc rom _ state (by simp [scanArguments, loadRel, NoJump]),
      show scanArguments.length = 6 by rfl, hpc]
    simp only [scanChunkOffset]
    omega
  | score =>
    have hp := scanScore_pc rom (state.register .address)
      (state.heap (state.register .address + 21)) (start + 169) state rfl rfl
    by_cases hm : state.heap (state.register .address + 21) = 1 ∧ state.register .value ≠ 0
    · refine ⟨123, by decide, ?_⟩
      change (runOps rom (scanScore (start + 169)) state).pc = _
      rw [hp, ite_eq_left hm, hpc]
      simp only [scanChunkOffset]
      omega
    · refine ⟨169, by decide, ?_⟩
      change (runOps rom (scanScore (start + 169)) state).pc = _
      rw [hp, ite_eq_right hm]
  | matched =>
    refine ⟨169, by decide, ?_⟩
    change (runOps rom recordSingleton state).pc = _
    rw [runOps_pc rom _ state recordSingleton_noJump, recordSingleton_length, hpc]
    simp only [scanChunkOffset]
    omega
  | innerTail =>
    refine ⟨51, by decide, ?_⟩
    simp [scanChunkCode, scanInnerTail, incrementRel, loadRel, storeRel, jumpTo,
      runOps, natExecuteOp, Op.execute, Instruction.execute]
  | outerTail =>
    refine ⟨4, by decide, ?_⟩
    simp [scanChunkCode, scanOuterTail, incrementRel, loadRel, storeRel, jumpTo,
      runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem scan_chunk_prefix_pc (rom : PhysicalROM) (start : Nat) (chunk : ScanChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + scanChunkOffset chunk))
    (count : Nat) (hc : count < scanChunkLength chunk) :
    (runOps rom ((scanChunkCode start chunk).take count) state).pc =
      5 * (start + scanChunkOffset chunk + count) := by
  have hlen := scan_chunk_lead_length start chunk
  have hn : count ≤ (scanChunkLead start chunk).length := by omega
  rw [scan_chunk_split, List.take_append_of_le_length hn,
    runOps_pc rom _ state (fun op hm => scan_chunk_lead_noJump start chunk op (List.mem_of_mem_take hm)),
    List.length_take_of_le hn, hpc]
  omega

theorem scan_chunk_safe (rom : PhysicalROM) (B H : Nat) (containing : List PackingOp) (start : Nat)
    (code : LeafToolCodeAt containing start) (chunk : ScanChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + scanChunkOffset chunk)) (ha : state.halted = false)
    (numeric : NumericSafe B H rom (scanChunkCode start chunk) state) :
    RunFacts B H rom containing (scanChunkLength chunk) state := by
  constructor
  · constructor
    · intro count hc
      rw [scan_chunk_run_prefix rom containing start code chunk state hpc ha count hc]
      refine ⟨numeric.1 count (by rw [scan_chunk_length]; exact hc),
        (runOps_halted rom _ state).trans ha, ?_⟩
      by_cases he : count = scanChunkLength chunk
      · subst count
        rw [List.take_of_length_le (by rw [scan_chunk_length])]
        obtain ⟨offset, ho, hp⟩ := scan_chunk_final_offset rom start chunk state hpc
        exact ⟨start + offset, by have hb := code.1; omega, hp⟩
      · have hl : count < scanChunkLength chunk := by omega
        exact ⟨start + scanChunkOffset chunk + count,
          by have hs := scan_chunk_span chunk; have hb := code.1; omega,
          scan_chunk_prefix_pc rom start chunk state hpc count hl⟩
    · intro count hc
      rw [scan_chunk_run_prefix rom containing start code chunk state hpc ha count hc.le]
      have hi : start + scanChunkOffset chunk + count < containing.length := by
        have hs := scan_chunk_span chunk
        have hb := code.1
        omega
      refine ⟨start + scanChunkOffset chunk + count, hi,
        scan_chunk_prefix_pc rom start chunk state hpc count hc, ?_⟩
      have hh := (code.2 (scanChunkOffset chunk + count) (by have hs := scan_chunk_span chunk; omega)).trans
        (scan_chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ _ (by omega),
        List.getD_eq_getElem _ _ (by rw [scan_chunk_length]; exact hc)] at hh
      have he : containing[start + scanChunkOffset chunk + count] =
          (scanChunkCode start chunk)[count]'(by rw [scan_chunk_length]; exact hc) := by
        simpa only [Nat.add_assoc] using hh
      rw [he]
      exact numeric.2 count (by rw [scan_chunk_length]; exact hc)
  · intro count hc
    rw [scan_chunk_run_prefix rom containing start code chunk state hpc ha count hc]
    cases chunk <;> dsimp only [scanChunkLength] at hc <;> interval_cases count <;> rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
