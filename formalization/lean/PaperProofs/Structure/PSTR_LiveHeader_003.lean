module

public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.PackingExecutionCost
public import PaperProofs.Structure.RawIncidenceLaminarRAM
import Mathlib.Tactic.NormNum

/-! The live command is loaded by fixed physical code from the original raw
input. Neither the stage, used bitmap nor a query answer is a new input. This
is the header block for A19, not a full controller or preprocessor. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLiveHeader

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open RawTreePreprocessingClaims PackingMachine

theorem input_length (q : Nat) (full : List (Finset (Fin q))) (command : Command) :
    (callInput q full command).input.length = 3 + full.length * q := by
  simp only [callInput, rawIncidenceROM, List.length_append, List.length_cons,
    List.length_nil, RawIncidenceLaminarRAM.incidence_length]
  omega

theorem input_N (q : Nat) (full : List (Finset (Fin q))) (command : Command) :
    (callInput q full command).semantic.read .input 0 = full.length := rfl

theorem input_q (q : Nat) (full : List (Finset (Fin q))) (command : Command) :
    (callInput q full command).semantic.read .input 1 = q := rfl

theorem input_command (q : Nat) (full : List (Finset (Fin q))) (command : Command) :
    (callInput q full command).semantic.read .input (2 + full.length * q) = command.word := by
  rw [Nat.add_comm]
  change (incidence full ++ [command.word]).getD (full.length * q) 0 = _
  rw [← RawIncidenceLaminarRAM.incidence_length q full,
    List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

/-- Eight actual ISA instructions. The code is fixed before N, q and raw
incidence. The sole multiplication computes the public command offset. -/
def program : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .old .address)),
   .base (.base (.constant .address 1)),
   .base (.base (.loadROM .input .fresh .address)),
   .arithmetic .multiply .index .old .fresh,
   .base (.base (.constant .value 2)),
   .base (.base (.add .address .index .value)),
   .base (.base (.loadROM .input .value .address))]

theorem program_length : program.length = 8 := rfl

theorem program_straight : StraightProgram program := by
  simp [StraightProgram, StraightOp, program]

theorem program_code_length : (packingCode program).length = 45 := by
  rw [packingCode_length, program_length]

theorem program_code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits := by
    exact (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  have small : value < 256 := by
    simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact small.trans_le hpow

theorem program_pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 40 < 2 ^ bits
  omega

theorem execute_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom program state).heap = state.heap := rfl

theorem execute_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) : (executeOps rom (program.take count) state).heap = state.heap := by
  by_cases hc : count ≤ 8
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (show program.length ≤ count by rw [program_length]; omega)]
    rfl

theorem execute_registers {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (state : WordState bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hq : Fits bits q) (hpos : Fits bits (2 + full.length * q)) :
    let after := executeOps (callInput q full command) program state
    after.register .old = BitVec.ofNat bits full.length ∧
    after.register .fresh = BitVec.ofNat bits q ∧
    after.register .value = BitVec.ofNat bits command.word ∧ after.heap = state.heap := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have h0 : (0 : Nat) < 2 ^ bits := by omega
  have h1 : (1 : Nat) < 2 ^ bits := by omega
  have hread0 : ((callInput q full command).words .input).getD 0 0 = full.length := input_N q full command
  have hread1 : ((callInput q full command).words .input).getD 1 0 = q := input_q q full command
  have hreadCmd : ((callInput q full command).words .input).getD (2 + full.length * q) 0 = command.word :=
    input_command q full command
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingArithmetic, Function.update_apply, ↓reduceIte, BitVec.toNat_ofNat,
    hread0, hread1, hreadCmd, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hq,
    BitVec.ofNat_add_ofNat, Nat.add_comm (full.length * q) 2, Nat.mod_eq_of_lt hpos]

theorem actual_run {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (state : WordState bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hq : Fits bits q) (hpos : Fits bits (2 + full.length * q))
    (hpc : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) program 9 state
    after.halted = true ∧ after.register .old = BitVec.ofNat bits full.length ∧
    after.register .fresh = BitVec.ofNat bits q ∧
    after.register .value = BitVec.ofNat bits command.word ∧ after.heap = state.heap := by
  dsimp only
  rw [show 9 = program.length + 1 from rfl,
    packingRun_executeOps_halt _ _ state program_straight (program_code_fit hb) (program_pc_fit hb) hpc ha]
  exact ⟨rfl, execute_registers full command state hb hN hq hpos⟩

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    (packingDynamicTrace rom program 9 state).length ≤ 256 := by
  rw [show 9 = program.length + 1 from rfl,
    packingDynamicTrace_eq_packingTrace rom _ state program_straight
      (program_code_fit hb) (program_pc_fit hb) hpc ha]
  decide

end PaperProofs.Structure.LaminarTree.PSTRLiveHeader
