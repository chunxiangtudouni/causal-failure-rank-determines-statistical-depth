module

public import Structure.PA06_A19Prepare_ChildrenCache023_WordSafety

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled transport from proved individual block numeric
bounds to every real fetched clock of that block. The final-PC alternatives
come from the actual fixed instructions, not an assumed execution trace. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m

/-- Actual run facts needed by this ABI: numeric/access safety together
with preservation of the hardware CB at every clock. This is an output
bundle of the block proofs, never an original caller premise. -/
def RunFacts (B H : Nat) (rom : PhysicalROM) (code : List PackingOp) (steps : Nat) (state : NatState) : Prop :=
  RunSafe B H rom code steps state ∧
    ∀ count ≤ steps, (natRun rom code count state).register .address = state.register .address

theorem RunFacts.add (B H : Nat) (rom : PhysicalROM) (code : List PackingOp) (left right : Nat)
    (state : NatState) (hl : RunFacts B H rom code left state)
    (hr : RunFacts B H rom code right (natRun rom code left state)) :
    RunFacts B H rom code (left + right) state := by
  refine ⟨RunSafe.add B H rom code left right state hl.1 hr.1, ?_⟩
  intro count hc
  by_cases hleft : count ≤ left
  · exact hl.2 count hleft
  · have he : count = left + (count - left) := by omega
    rw [he, natRun_add, hr.2 (count - left) (by omega), hl.2 left le_rfl]

theorem chunk_final_offset (rom : PhysicalROM) (start : Nat) (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) :
    ∃ offset ≤ 144, (runOps rom (chunkCode start chunk) state).pc = 5 * (start + offset) := by
  cases chunk with
  | «initialize» =>
    refine ⟨32, by decide, ?_⟩
    change (runOps rom initializeCache state).pc = _
    rw [runOps_pc rom _ state (by simp [initializeCache, loadRel, storeRel, setRel, NoJump]), initializeCache_length, hpc]
    simp only [chunkOffset, Nat.add_zero]
    omega
  | initializeRow =>
    refine ⟨49, by decide, ?_⟩
    change (runOps rom initializeRow state).pc = _
    rw [runOps_pc rom _ state (by simp [initializeRow, setRel, storeRel, NoJump]), initializeRow_length, hpc]
    simp only [chunkOffset]
    omega
  | matched =>
    refine ⟨111, by decide, ?_⟩
    change (runOps rom matched state).pc = _
    rw [runOps_pc rom _ state (by simp [matched, writeChild, incrementRel, loadRel, storeRel, NoJump]), matched_length, hpc]
    simp only [chunkOffset]
    omega
  | outerTest =>
    have hp := branch_pc rom (state.register .address) (state.heap (state.register .address + 70))
      (state.heap (state.register .address + 64)) 64 (start + 144) state rfl rfl rfl
    by_cases hz : state.heap (state.register .address + 70) - state.heap (state.register .address + 64) = 0
    · refine ⟨144, by decide, ?_⟩
      change (runOps rom (boundedTest 64 (start + 144)) state).pc = _
      rw [hp, ite_eq_left hz]
    · refine ⟨41, by decide, ?_⟩
      change (runOps rom (boundedTest 64 (start + 144)) state).pc = _
      rw [hp, ite_eq_right hz, hpc]
      simp only [chunkOffset]
      omega
  | innerTest =>
    have hp := branch_pc rom (state.register .address) (state.heap (state.register .address + 70))
      (state.heap (state.register .address + 65)) 65 (start + 122) state rfl rfl rfl
    by_cases hz : state.heap (state.register .address + 70) - state.heap (state.register .address + 65) = 0
    · refine ⟨122, by decide, ?_⟩
      change (runOps rom (boundedTest 65 (start + 122)) state).pc = _
      rw [hp, ite_eq_left hz]
    · refine ⟨58, by decide, ?_⟩
      change (runOps rom (boundedTest 65 (start + 122)) state).pc = _
      rw [hp, ite_eq_right hz, hpc]
      simp only [chunkOffset]
      omega
  | matchTest =>
    let CB := state.register .address
    let M := state.heap (CB + 528)
    let parent := state.heap (CB + 64)
    let child := state.heap (CB + 65)
    have hp := match_pc rom CB M parent child start state rfl rfl rfl rfl
    by_cases hz : state.heap (parentAddress CB M child) = parent + 1
    · refine ⟨84, by decide, ?_⟩
      change (runOps rom (matchTest start) state).pc = _
      rw [hp, ite_eq_left hz]
    · refine ⟨81, by decide, ?_⟩
      change (runOps rom (matchTest start) state).pc = _
      rw [hp, ite_eq_right hz, hpc]
      simp only [chunkOffset]
      omega
  | skip =>
    refine ⟨111, by decide, ?_⟩
    simp [chunkCode, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
  | innerTail => exact ⟨49, by decide, innerTail_pc rom start state⟩
  | outerTail => exact ⟨32, by decide, outerTail_pc rom start state⟩

/-- Before the final operation every chunk follows its proved straight
lead. This is a PC fact of actual code, with no numeric certificate input. -/
theorem chunk_prefix_pc (rom : PhysicalROM) (start : Nat) (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk))
    (count : Nat) (hc : count < chunkLength chunk) :
    (runOps rom ((chunkCode start chunk).take count) state).pc = 5 * (start + chunkOffset chunk + count) := by
  have hlen := chunk_lead_length start chunk
  have hn : count ≤ (chunkLead start chunk).length := by omega
  rw [chunk_split, List.take_append_of_le_length hn,
    runOps_pc rom _ state (fun op hm => chunk_lead_noJump start chunk op (List.mem_of_mem_take hm)),
    List.length_take_of_le hn, hpc]
  omega

/-- Internal block composition. The supplied numeric result is proved by
one of WordSafety's actual-field lemmas and is never a new paper premise. -/
theorem chunk_safe (rom : PhysicalROM) (B H : Nat) (containing : List PackingOp) (start : Nat)
    (code : CodeAt containing start) (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (numeric : NumericSafe B H rom (chunkCode start chunk) state) :
    RunFacts B H rom containing (chunkLength chunk) state := by
  constructor
  · constructor
    · intro count hc
      rw [chunk_run_prefix rom containing start code chunk state hpc ha count hc]
      refine ⟨numeric.1 count (by rw [chunk_code_length]; exact hc),
        (runOps_halted rom _ state).trans ha, ?_⟩
      by_cases he : count = chunkLength chunk
      · subst count
        rw [List.take_of_length_le (by rw [chunk_code_length])]
        obtain ⟨offset, ho, hp⟩ := chunk_final_offset rom start chunk state hpc
        exact ⟨start + offset, by have hb := code.1; omega, hp⟩
      · have hl : count < chunkLength chunk := by omega
        exact ⟨start + chunkOffset chunk + count,
          by have hs := chunk_span chunk; have hb := code.1; omega,
          chunk_prefix_pc rom start chunk state hpc count hl⟩
    · intro count hc
      rw [chunk_run_prefix rom containing start code chunk state hpc ha count hc.le]
      have hi : start + chunkOffset chunk + count < containing.length := by
        have hs := chunk_span chunk
        have hb := code.1
        omega
      refine ⟨start + chunkOffset chunk + count, hi, chunk_prefix_pc rom start chunk state hpc count hc, ?_⟩
      have hh := (code.2 (chunkOffset chunk + count) (by have hs := chunk_span chunk; omega)).trans
        (chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ _ (by omega),
        List.getD_eq_getElem _ _ (by rw [chunk_code_length]; exact hc)] at hh
      have he : containing[start + chunkOffset chunk + count] = (chunkCode start chunk)[count]'(by rw [chunk_code_length]; exact hc) := by
        simpa only [Nat.add_assoc] using hh
      rw [he]
      exact numeric.2 count (by rw [chunk_code_length]; exact hc)
  
  · intro count hc
    rw [chunk_run_prefix rom containing start code chunk state hpc ha count hc]
    cases chunk <;> dsimp only [chunkLength] at hc <;> interval_cases count <;> rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
