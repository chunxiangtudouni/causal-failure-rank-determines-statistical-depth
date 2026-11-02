module

public import PaperProofs.Structure.PSTR_HD_ZeroHeadsLayout_008

/-! Fixed q=0 live callback. The only current datum is the original public
command. Stage is loaded from and updated in the same physical heap. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroLive

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingClaims

/-- Two saturating arithmetic operations distinguish the original commands. -/
def increment : Command → Nat | .correct => 1 | _ => 0
def failedWord : Command → Nat | .error => 1 | _ => 0
def rankWord (N stage : Nat) : Nat := if N - stage = 0 then 2 else 1
def goodWord (N stage : Nat) : Nat := if N - (stage + 1) = 0 then 2 else 1

def program : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .total .address)),
   .base (.base (.constant .address 2)),
   .base (.base (.loadROM .input .old .address)),
   .base (.base (.constant .address 4)),
   .base (.base (.loadHeap .index .address)),
   .base (.base (.constant .fresh 1)),
   .base (.subtract .flag .old .fresh),
   .base (.base (.constant .address 5)),
   .base (.base (.storeHeap .address .flag)),
   .base (.base (.minimum .value .old .fresh)),
   .base (.subtract .value .value .flag),
   .base (.base (.add .value .index .value)),
   .base (.base (.constant .address 4)),
   .base (.base (.storeHeap .address .value)),
   .base (.subtract .flag .total .index),
   .base (.base (.constant .old 2)),
   .base (.base (.select .value .flag .fresh .old)),
   .base (.base (.add .index .index .fresh)),
   .base (.subtract .flag .total .index),
   .base (.base (.select .old .flag .fresh .old)),
   .base (.base (.constant .fresh 0)),
   .base (.base (.constant .index 0))]

theorem program_length : program.length = 23 := rfl

theorem program_straight : StraightProgram program := by
  simp [StraightProgram, StraightOp, program]

theorem program_code_length : (packingCode program).length = 120 := by
  rw [packingCode_length, program_length]

theorem program_code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  have small : value < 256 := by
    simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact small.trans_le hpow

theorem program_pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 115 < 2 ^ bits
  omega

theorem command_rom (full : List (Finset (Fin 0))) (command : Command) :
    callInput 0 full command = ⟨[full.length, 0, command.word], [], []⟩ := by
  have hi : incidence full = [] := List.eq_nil_of_length_eq_zero (by rw [incidence_length]; simp)
  simp [callInput, rawIncidenceROM, hi]

theorem execute_values {bits : Nat} (full : List (Finset (Fin 0))) (command : Command)
    (stage : Nat) (state : WordState bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hs : Fits bits stage) (hs1 : Fits bits (stage + 1))
    (hload : state.heap (BitVec.ofNat bits 4) = BitVec.ofNat bits stage) :
    let result := executeOps (callInput 0 full command) program state
    result.register .value = BitVec.ofNat bits (rankWord full.length stage) ∧
    result.register .old = BitVec.ofNat bits (goodWord full.length stage) ∧
    result.register .fresh = BitVec.ofNat bits 0 ∧ result.register .index = BitVec.ofNat bits 0 ∧
    result.heap = Function.update (Function.update state.heap (BitVec.ofNat bits 5)
      (BitVec.ofNat bits (failedWord command))) (BitVec.ofNat bits 4)
      (BitVec.ofNat bits (stage + increment command)) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have h0 : (0 : Nat) < 2 ^ bits := by omega
  have h1 : (1 : Nat) < 2 ^ bits := by omega
  have h2 : (2 : Nat) < 2 ^ bits := by omega
  have h4 : (4 : Nat) < 2 ^ bits := by omega
  have h5 : (5 : Nat) < 2 ^ bits := by omega
  have hd0 : full.length - stage < 2 ^ bits := (Nat.sub_le _ _).trans_lt hN
  have hd1 : full.length - (stage + 1) < 2 ^ bits := (Nat.sub_le _ _).trans_lt hN
  unfold Fits at hN hs hs1
  rw [command_rom]
  cases command <;> by_cases hcur : full.length - stage = 0 <;>
    by_cases hgood : full.length - (stage + 1) = 0 <;>
    simp_all +decide [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
      PhysicalROM.words, rankWord, goodWord, increment, failedWord, Command.word,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt, BitVec.ofNat_add_ofNat]

theorem actual_values {bits : Nat} (full : List (Finset (Fin 0))) (command : Command)
    (stage : Nat) (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hs : Fits bits stage) (hs1 : Fits bits (stage + 1))
    (hload : heap (BitVec.ofNat bits 4) = BitVec.ofNat bits stage) :
    let result := packingRun (callInput 0 full command) program 24 (packingInitial heap)
    result.halted = true ∧
    result.register .value = BitVec.ofNat bits (rankWord full.length stage) ∧
    result.register .old = BitVec.ofNat bits (goodWord full.length stage) ∧
    result.register .fresh = BitVec.ofNat bits 0 ∧ result.register .index = BitVec.ofNat bits 0 ∧
    result.heap = Function.update (Function.update heap (BitVec.ofNat bits 5)
      (BitVec.ofNat bits (failedWord command))) (BitVec.ofNat bits 4)
      (BitVec.ofNat bits (stage + increment command)) := by
  dsimp only
  rw [show 24 = program.length + 1 from rfl,
    packingRun_executeOps_halt _ _ (packingInitial heap) program_straight
      (program_code_fit hb) (program_pc_fit hb) rfl rfl]
  exact ⟨rfl, execute_values full command stage (packingInitial heap) hb hN hs hs1 hload⟩

theorem actual_call_cost {bits : Nat} (full : List (Finset (Fin 0))) (command : Command)
    (heap : BitVec bits → BitVec bits) :
    callCost 0 full program command 24 heap ≤ 512 * liveWork 0 0 := by
  have ht := packingDynamicTrace_length_le (callInput 0 full command) program 24 (packingInitial heap)
  simp only [callCost, program_code_length, liveWork, ↓reduceIte]
  omega

end PaperProofs.Structure.LaminarTree.PSTRZeroLive

