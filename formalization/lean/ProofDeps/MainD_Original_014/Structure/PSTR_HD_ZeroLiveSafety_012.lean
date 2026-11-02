module

public import Structure.PSTR_HD_ZeroLive_011

/-! The fixed zero-tool live program fetches every body instruction and HALT.
Its memory addresses are the original raw command/N and persistent stage/
failed words, with no stage or answer supplied again as a call input. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroLive

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingClaims

variable {bits : Nat}

theorem input_fit (full : List (Finset (Fin 0))) (command : Command)
    (hb : 8 ≤ bits) (hN : Fits bits full.length) :
    ∀ region, WordsFit bits ((callInput 0 full command).words region) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have h0 : Fits bits 0 := by unfold Fits; omega
  have h1 : Fits bits 1 := by unfold Fits; omega
  have h2 : Fits bits 2 := by unfold Fits; omega
  intro region value hv
  rw [command_rom] at hv
  cases region with
  | input =>
    simp only [PhysicalROM.words, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hN
    · exact h0
    · cases command <;> assumption
  | internal => cases hv
  | children => cases hv

theorem access_prefix (full : List (Finset (Fin 0))) (command : Command)
    (heapWords : Nat) (state : WordState bits) (hb : 8 ≤ bits) (hh : 6 ≤ heapWords)
    (count : Nat) (hc : count < program.length) :
    packingAccessFits (callInput 0 full command) heapWords
      (executeOps (callInput 0 full command) (program.take count) state) program[count] := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have h0 : (0 : Nat) < 2 ^ bits := by omega
  have h2 : (2 : Nat) < 2 ^ bits := by omega
  have h4 : (4 : Nat) < 2 ^ bits := by omega
  have h5 : (5 : Nat) < 2 ^ bits := by omega
  change count < 23 at hc
  rw [command_rom]
  interval_cases count <;>
    simp_all +decide [program, List.take_succ_cons, List.take_zero,
      List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction,
      PhysicalROM.words, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega

theorem dynamic_correct (full : List (Finset (Fin 0))) (command : Command)
    (heapWords : Nat) (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hh : 6 ≤ heapWords)
    (hfoot : Fits bits ((callInput 0 full command).size + heapWords + (packingCode program).length)) :
    DynamicRunCorrect heapWords (callInput 0 full command) program 24 heap := by
  let rom := callInput 0 full command
  let state := packingInitial heap
  have code := program_code_fit hb
  have pcfit := program_pc_fit hb
  refine ⟨code, input_fit full command hb hN, hfoot, ?_, ?_⟩
  · rw [show 24 = program.length + 1 from rfl,
      packingRun_executeOps_halt rom program state program_straight code pcfit rfl rfl]
  · intro count hc
    have hcount : count ≤ program.length := by rw [program_length]; omega
    have run := packingRun_eq_executeOps_take rom program state program_straight code pcfit rfl rfl count hcount
    have active : (packingRun rom program count state).halted = false := by
      rw [run, executeOps_halted]
      rfl
    have pc : (packingRun rom program count state).pc.toNat = 5 * count := by
      rw [run, executeOps_pc rom _ state (fun op ho => program_straight op (List.mem_of_mem_take ho))]
      change (BitVec.ofNat bits 0 + BitVec.ofNat bits (5 * (program.take count).length)).toNat = _
      rw [BitVec.zero_add, List.length_take_of_le hcount, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 hcount) pcfit)
    have fetchEq : fetch program (packingRun rom program count state) = natFetch program (5 * count) := by
      change physicalFetch bits (packingCode program) _ = _
      rw [physicalFetch_eq bits _ _ code, pc]
      rfl
    refine ⟨active, ?_, ?_⟩
    · rw [pc, program_code_length]
      rw [program_length] at hcount
      omega
    · rw [fetchEq]
      by_cases hbody : count < program.length
      · rw [natFetch_body program count hbody, decode_encode, run]
        exact access_prefix full command heapWords state hb hh count hbody
      · have he : count = program.length := by omega
        subst count
        rw [natFetch_halt, decode_halt]

end PaperProofs.Structure.LaminarTree.PSTRZeroLive
