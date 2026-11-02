module

public import Structure.PSTR_LiveDispatchCode_127
public import Structure.PSTR_UniformQuery_122

/-! The live dispatcher really reloads original q/N/command, using only
original word32 rooms. These are finite actual-ISA block effects; the whole
containing-run branch composition is a separate theorem. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveDispatch

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PA17A19RuntimeEntry020 PSTRWordSegments PSTRCountKernel PSTRReplySpill

theorem small_fit {q : Nat} (full : List (Finset (Fin q))) (value : Nat) (hv : value ≤ 128) :
    Fits (wordBits full) value := by
  have hb : 32 ≤ wordBits full := PSTROriginalCountRoom.word_lower full.length q
  have hp : 2 ^ 32 ≤ 2 ^ wordBits full := Nat.pow_le_pow_right (by decide) hb
  exact (show value < 2 ^ 32 by omega).trans_le hp

theorem zero_fields {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (start done : Nat) (state : WordState (wordBits full))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start)) :
    let after := executeOps (callInput q full command) (zeroBlock done) state
    after.pc = (if q = 0 then BitVec.ofNat (wordBits full) (5 * done)
      else BitVec.ofNat (wordBits full) (5 * (start + 4))) ∧
    after.register .flag = BitVec.ofNat (wordBits full) q ∧
    after.heap = state.heap ∧ after.halted = state.halted := by
  have h1 := small_fit full 1 (by decide)
  have hq := (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
  have hread : ((callInput q full command).words .input).getD 1 0 = q :=
    PSTRLiveHeader.input_q q full command
  have pc : 5 * start + 5 + 5 + 5 + 5 = 5 * (start + 4) := by omega
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp +decide only [zeroBlock, zeroLead, List.cons_append, List.nil_append, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hp,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, hread, Nat.mod_eq_of_lt hq, BitVec.ofNat_add_ofNat, pc]
  · simp +decide only [zeroBlock, zeroLead, List.cons_append, List.nil_append, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, hread]

theorem command_fields {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (start done : Nat) (state : WordState (wordBits full))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start))
    (hqreg : state.register .flag = BitVec.ofNat (wordBits full) q) :
    let after := executeOps (callInput q full command) (commandBlock done) state
    after.pc = (if command = .query then BitVec.ofNat (wordBits full) (5 * done)
      else BitVec.ofNat (wordBits full) (5 * (start + 8))) ∧
    after.register .flag = BitVec.ofNat (wordBits full) command.word ∧
    after.heap = state.heap ∧ after.halted = state.halted := by
  have h0 := small_fit full 0 (by decide)
  have hN := (PSTROriginalCountRoom.raw_rooms full.length q).1
  have hq := (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
  have hpos := (PSTROriginalCountRoom.raw_rooms full.length q).2.1
  have hread0 : ((callInput q full command).words .input).getD 0 0 = full.length :=
    PSTRLiveHeader.input_N q full command
  have hread : ((callInput q full command).words .input).getD (2 + full.length * q) 0 = command.word :=
    PSTRLiveHeader.input_command q full command
  have pc : 5 * start + 5 + 5 + 5 + 5 + 5 + 5 + 5 + 5 = 5 * (start + 8) := by omega
  have hcmd : Fits (wordBits full) command.word := by
    cases command <;> exact small_fit full _ (by decide)
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp +decide only [commandBlock, commandLead, List.cons_append, List.nil_append, executeOps,
      packingExecuteOp, wordOp, wordInstruction, packingArithmetic, Function.update_apply, ↓reduceIte,
      hp, hqreg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0, hread0, Nat.mod_eq_of_lt hN,
      Nat.mod_eq_of_lt hq, BitVec.ofNat_add_ofNat, Nat.add_comm (full.length * q) 2,
      Nat.mod_eq_of_lt hpos, hread, Nat.mod_eq_of_lt hcmd, pc]
    cases command <;> rfl
  · simp +decide only [commandBlock, commandLead, List.cons_append, List.nil_append, executeOps,
      packingExecuteOp, wordOp, wordInstruction, packingArithmetic, Function.update_apply, ↓reduceIte,
      hqreg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0, hread0, Nat.mod_eq_of_lt hN,
      Nat.mod_eq_of_lt hq, BitVec.ofNat_add_ofNat, Nat.add_comm (full.length * q) 2,
      Nat.mod_eq_of_lt hpos, hread]

theorem correct_fields {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (start correct : Nat) (state : WordState (wordBits full))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start))
    (hcmd : state.register .flag = BitVec.ofNat (wordBits full) command.word) :
    let after := executeOps (callInput q full command) (correctBlock correct) state
    after.pc = (if command = .error then BitVec.ofNat (wordBits full) (5 * (start + 4))
      else BitVec.ofNat (wordBits full) (5 * correct)) ∧
    after.heap = state.heap ∧ after.halted = state.halted := by
  have h1 := small_fit full 1 (by decide)
  have hcfit : Fits (wordBits full) command.word := by
    cases command <;> exact small_fit full _ (by decide)
  have hsfit : Fits (wordBits full) (command.word - 1) :=
    (Nat.sub_le _ _).trans_lt hcfit
  have pc : 5 * start + 5 + 5 + 5 + 5 = 5 * (start + 4) := by omega
  refine ⟨?_, rfl, rfl⟩
  simp +decide only [correctBlock, correctLead, List.cons_append, List.nil_append, executeOps,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hp, hcmd,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcfit, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt hsfit, BitVec.ofNat_add_ofNat, pc]
  cases command <;> rfl

theorem error_fields {bits : Nat} (rom : PhysicalROM) (start failed : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) :
    let after := executeOps rom (errorBlock failed) state
    after.pc = (if (state.register .index).toNat = 0 then BitVec.ofNat bits (5 * failed)
      else BitVec.ofNat bits (5 * (start + 2))) ∧
    after.heap = state.heap ∧ after.halted = state.halted := by
  have pc : 5 * start + 5 + 5 = 5 * (start + 2) := by omega
  refine ⟨?_, rfl, rfl⟩
  simp +decide only [errorBlock, errorLead, List.cons_append, List.nil_append, executeOps,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hp,
    BitVec.ofNat_add_ofNat, pc]

theorem zeroLead_access {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (done heapWords : Nat) (state : WordState (wordBits full))
    (count : Nat) (hc : count < (zeroLead done).length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) ((zeroLead done).take count) state) (zeroLead done)[count] := by
  have h1 := small_fit full 1 (by decide)
  have hinput : 1 < (callInput q full command).input.length := by rw [PSTRLiveHeader.input_length]; omega
  change count < 3 at hc
  interval_cases count <;> try exact True.intro
  simp +decide only [zeroLead, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
    List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, packingAccessFits, AccessFits, PhysicalROM.words,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  exact hinput

theorem commandLead_access {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (done heapWords : Nat) (state : WordState (wordBits full))
    (hqreg : state.register .flag = BitVec.ofNat (wordBits full) q)
    (count : Nat) (hc : count < (commandLead done).length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) ((commandLead done).take count) state) (commandLead done)[count] := by
  have h0 := small_fit full 0 (by decide)
  have hN := (PSTROriginalCountRoom.raw_rooms full.length q).1
  have hq := (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
  have hpos := (PSTROriginalCountRoom.raw_rooms full.length q).2.1
  have hread : ((callInput q full command).words .input).getD 0 0 = full.length := rfl
  have hinput0 : 0 < (callInput q full command).input.length := by rw [PSTRLiveHeader.input_length]; omega
  have hinput : 2 + full.length * q < (callInput q full command).input.length := by rw [PSTRLiveHeader.input_length]; omega
  change count < 7 at hc
  interval_cases count
  · exact True.intro
  · simp +decide only [commandLead, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
      List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
      Function.update_apply, ↓reduceIte, packingAccessFits, AccessFits,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0]
    change _ < (callInput q full command).input.length
    exact hinput0
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · simp +decide only [commandLead, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
      List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction, packingArithmetic,
      Function.update_apply, ↓reduceIte, packingAccessFits, AccessFits, hqreg,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0, hread, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hq,
      BitVec.ofNat_add_ofNat, Nat.add_comm (full.length * q) 2, Nat.mod_eq_of_lt hpos]
    change _ < (callInput q full command).input.length
    exact hinput
  · exact True.intro

theorem correctLead_access {bits : Nat} (rom : PhysicalROM) (correct heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < (correctLead correct).length) :
    packingAccessFits rom heapWords (executeOps rom ((correctLead correct).take count) state) (correctLead correct)[count] := by
  change count < 3 at hc
  interval_cases count <;> exact True.intro

theorem errorLead_access {bits : Nat} (rom : PhysicalROM) (failed heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < (errorLead failed).length) :
    packingAccessFits rom heapWords (executeOps rom ((errorLead failed).take count) state) (errorLead failed)[count] := by
  have he : count = 0 := by change count < 1 at hc; omega
  subst count
  exact True.intro

end PaperProofs.Structure.LaminarTree.PSTRLiveDispatch
