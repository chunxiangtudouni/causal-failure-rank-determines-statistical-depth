module

public import Structure.PSTR_HD_ZeroLiveClaims_013

/-! Exact physical writes of the frozen original23op q0 live program.
The command is loaded from ORIGINAL input2. No stage/failed input is added.
Before clock10 no write occurs; clock10 writes failed5; clock15 writes stage4.
All other physical words are preserved at every prefix. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine

theorem declaration_allowed_fields (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (declaration : command = .correct ∨ command = .error)
    (allowed : Allowed full configuration command) :
    configuration.failed = false ∧ configuration.stage < full.length := by
  rcases declaration with rfl | rfl <;> exact allowed

theorem next_error_none (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (allowed : Allowed full configuration .error) :
    nextConfiguration 0 full configuration .error = {configuration with failed := true} := by
  have hs : configuration.stage < full.length + 1 := by have h := allowed.2; omega
  simp [nextConfiguration, hs, callback]

def failedHeap {bits : Nat} (command : Command) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update heap (BitVec.ofNat bits 5) (BitVec.ofNat bits (PSTRZeroLive.failedWord command))

def declarationHeap {bits : Nat} (command : Command) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (failedHeap command heap) (BitVec.ofNat bits 4)
    (heap (BitVec.ofNat bits 4) + BitVec.ofNat bits (PSTRZeroLive.increment command))

theorem live_prefix_heap {bits : Nat} (full : List (Finset (Fin 0))) (command : Command)
    (state : WordState bits) (hb : 8 ≤ bits) (clock : Nat) (hc : clock ≤ 23) :
    (executeOps (callInput 0 full command) (PSTRZeroLive.program.take clock) state).heap =
      if clock < 10 then state.heap else if clock < 15 then failedHeap command state.heap else declarationHeap command state.heap := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h0 : (0 : Nat) < 2 ^ bits := by omega
  have h1 : (1 : Nat) < 2 ^ bits := by omega
  have h2 : (2 : Nat) < 2 ^ bits := by omega
  rw [PSTRZeroLive.command_rom]
  cases command <;> interval_cases clock <;>
    simp_all +decide [PSTRZeroLive.program, executeOps, packingExecuteOp, wordOp, wordInstruction,
      PhysicalROM.words, PSTRZeroLive.failedWord, PSTRZeroLive.increment, Command.word,
      failedHeap, declarationHeap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]

theorem live_prefix_frame_word {bits : Nat} (full : List (Finset (Fin 0))) (command : Command)
    (state : WordState bits) (hb : 8 ≤ bits) (address : BitVec bits)
    (h4 : address ≠ BitVec.ofNat bits 4) (h5 : address ≠ BitVec.ofNat bits 5)
    (clock : Nat) (hc : clock ≤ 23) :
    (executeOps (callInput 0 full command) (PSTRZeroLive.program.take clock) state).heap address = state.heap address := by
  rw [live_prefix_heap full command state hb clock hc]
  split_ifs
  · rfl
  · simp only [failedHeap, Function.update_of_ne h5]
  · simp only [declarationHeap, failedHeap, Function.update_of_ne h4, Function.update_of_ne h5]

theorem live_prefix_frame {bits : Nat} (full : List (Finset (Fin 0))) (command : Command)
    (state : WordState bits) (hb : 8 ≤ bits) (physical : Nat) (hf : Fits bits physical)
    (h4 : physical ≠ 4) (h5 : physical ≠ 5) (clock : Nat) (hc : clock ≤ 23) :
    (executeOps (callInput 0 full command) (PSTRZeroLive.program.take clock) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  exact live_prefix_frame_word full command state hb _
    (PSTRZeroLive.word_ne physical 4 hf (by unfold Fits; omega) h4)
    (PSTRZeroLive.word_ne physical 5 hf (by unfold Fits; omega) h5) clock hc

end PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
