module

public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.PackingExecutionCost
public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import PaperProofs.Structure.RawIncidenceOuterSafety
import Mathlib.Tactic.IntervalCases

/-! PA17 batch 001: fixed code-emission primitive. This supplies a generator
component, not FullGivenTreeClaims. Words are ordinary registers, emitted by
actual storeHeap instructions, not code supplied through a template ROM. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17Generator

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety

def emitFive : List PackingOp :=
  [.base (.base (.constant .index 1)),
   .base (.base (.storeHeap .address .old)),
   .base (.base (.add .address .address .index)),
   .base (.base (.storeHeap .address .fresh)),
   .base (.base (.add .address .address .index)),
   .base (.base (.storeHeap .address .total)),
   .base (.base (.add .address .address .index)),
   .base (.base (.storeHeap .address .flag)),
   .base (.base (.add .address .address .index)),
   .base (.base (.storeHeap .address .value)),
   .base (.base (.add .address .address .index))]

def sourceWords (state : NatState) : Vector Nat 5 :=
  ⟨#[state.register .old, state.register .fresh, state.register .total,
    state.register .flag, state.register .value], rfl⟩

theorem emitFive_length : emitFive.length = 11 := rfl

theorem emitFive_noJump : ∀ op ∈ emitFive, NoJump op := by
  simp [emitFive, NoJump]

theorem emitFive_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom emitFive state).heap =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update state.heap (state.register .address) (state.register .old))
              (state.register .address + 1) (state.register .fresh))
            (state.register .address + 2) (state.register .total))
          (state.register .address + 3) (state.register .flag))
        (state.register .address + 4) (state.register .value) := by
  simp [emitFive, runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem emitFive_value (rom : PhysicalROM) (state : NatState) (position : Fin 5) :
    (runOps rom emitFive state).heap (state.register .address + position.val) =
      (sourceWords state).get position := by
  rw [emitFive_heap]
  rcases position with ⟨position, hp⟩
  interval_cases position <;> simp [sourceWords, Function.update, Vector.get]

theorem emitFive_frame (rom : PhysicalROM) (state : NatState) (address : Nat)
    (houtside : address < state.register .address ∨ state.register .address + 5 ≤ address) :
    (runOps rom emitFive state).heap address = state.heap address := by
  rw [emitFive_heap]
  have h0 : address ≠ state.register .address := by omega
  have h1 : address ≠ state.register .address + 1 := by omega
  have h2 : address ≠ state.register .address + 2 := by omega
  have h3 : address ≠ state.register .address + 3 := by omega
  have h4 : address ≠ state.register .address + 4 := by omega
  simp [h0, h1, h2, h3, h4]

theorem emitFive_registers (rom : PhysicalROM) (state : NatState) :
    (runOps rom emitFive state).register =
      Function.update (Function.update state.register .index 1) .address
        (state.register .address + 5) := by
  funext register
  cases register <;>
    simp [emitFive, runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem emitFive_trace_length : (packingTrace emitFive).length = 124 := by decide

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hfit : ∀ register, Fits bits (registers register)) (target : Register) (value : Nat)
    (hv : Fits bits value) : ∀ register, Fits bits (Function.update registers target value register) := by
  intro register
  by_cases h : register = target
  · simpa only [h, Function.update_self] using hv
  · simpa only [Function.update_of_ne h] using hfit register

theorem emitFive_prefix_registersFit (rom : PhysicalROM) (bits : Nat) (state : NatState)
    (hfit : RegistersFit bits state) (hend : Fits bits (state.register .address + 5))
    (count : Nat) (hc : count ≤ 11) :
    RegistersFit bits (runOps rom (emitFive.take count) state) := by
  have hone : Fits bits 1 := lt_of_le_of_lt (by omega) hend
  induction count with
  | zero => exact hfit
  | succ count ih =>
    have hn : count < 11 := by omega
    have hprev := ih hn.le
    rw [List.take_succ_eq_append_getElem (by change count < 11; exact hn), runOps_append]
    change RegistersFit bits (natExecuteOp rom (emitFive[count]'(by change count < 11; exact hn))
      (runOps rom (emitFive.take count) state))
    interval_cases count <;>
      simp only [emitFive, List.getElem_cons_zero, List.getElem_cons_succ,
        RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hprev | apply fits_update hprev
    · exact hone
    all_goals
      simp +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]
      exact lt_of_le_of_lt (by omega) hend

theorem emitFive_prefix_accessFits (rom : PhysicalROM) (heapWords : Nat) (state : NatState)
    (hend : state.register .address + 5 ≤ heapWords) (count : Nat) (hc : count < 11) :
    NatAccessFits rom heapWords (runOps rom (emitFive.take count) state)
      (emitFive.getD count (.base (.base (.constant .value 0)))) := by
  interval_cases count <;>
    simp +decide [emitFive, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, Nat.add_assoc]
  all_goals omega

theorem emitFive_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    natRun rom (left ++ emitFive ++ right) 11 state = runOps rom emitFive state := by
  apply natRun_of_straight_segment rom (left ++ emitFive ++ right) emitFive left.length
    (by simp only [List.length_append, emitFive_length]; omega) ?_ emitFive_noJump state hpc hactive
  intro position hp
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp

theorem emitFive_prefix_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 11) :
    natRun rom (left ++ emitFive ++ right) count state = runOps rom (emitFive.take count) state := by
  have hlen : (emitFive.take count).length = count :=
    List.length_take_of_le (by change count ≤ 11; exact hc)
  conv_lhs => rw [← hlen]
  apply natRun_of_straight_segment rom (left ++ emitFive ++ right) (emitFive.take count) left.length
    (by simp only [List.length_append, emitFive_length, hlen]; omega) ?_ ?_ state hpc hactive
  · intro position hp
    have hp' : position < count := by simpa only [hlen] using hp
    rw [List.getElem_append_left (by simp only [List.length_append, emitFive_length]; omega),
      List.getElem_append_right (by omega)]
    simp
  · intro op hop
    exact emitFive_noJump op (List.mem_of_mem_take hop)

theorem emitFive_word_run (rom : PhysicalROM) (left right : List PackingOp)
    (bits : Nat) (state : NatState) (hpc : state.pc = 5 * left.length)
    (hactive : state.halted = false) (hfit : RegistersFit bits state)
    (haddress : Fits bits (state.register .address + 5))
    (hend : Fits bits (5 * (left.length + 11)))
    (hwords : WordsFit bits (packingCode (left ++ emitFive ++ right)))
    (count : Nat) (hc : count ≤ 11) :
    packingRun rom (left ++ emitFive ++ right) count (state.toWord bits) =
      (runOps rom (emitFive.take count) state).toWord bits := by
  rw [← emitFive_prefix_run rom left right state hpc hactive count hc]
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  rw [emitFive_prefix_run rom left right state hpc hactive k (by omega)]
  constructor
  · exact emitFive_prefix_registersFit rom bits state hfit haddress k (by omega)
  · rw [runOps_pc _ _ _ (fun op hop => emitFive_noJump op (List.mem_of_mem_take hop)),
      List.length_take_of_le (by change k ≤ 11; omega), hpc]
    exact lt_of_le_of_lt (by omega) hend

/-- Actual BitVec fetch/run produces the five input code words in physical heap. -/
theorem emitFive_word_value (rom : PhysicalROM) (left right : List PackingOp)
    (bits : Nat) (state : NatState) (hpc : state.pc = 5 * left.length)
    (hactive : state.halted = false) (hfit : RegistersFit bits state)
    (haddress : Fits bits (state.register .address + 5))
    (hend : Fits bits (5 * (left.length + 11)))
    (hwords : WordsFit bits (packingCode (left ++ emitFive ++ right))) (position : Fin 5) :
    (packingRun rom (left ++ emitFive ++ right) 11 (state.toWord bits)).heap
        (BitVec.ofNat bits (state.register .address + position.val)) =
      BitVec.ofNat bits ((sourceWords state).get position) := by
  rw [emitFive_word_run rom left right bits state hpc hactive hfit haddress hend hwords 11 le_rfl]
  have ha : Fits bits (state.register .address + position.val) :=
    lt_of_le_of_lt (by omega) haddress
  change BitVec.ofNat bits ((runOps rom (emitFive.take 11) state).heap
    (BitVec.ofNat bits (state.register .address + position.val)).toNat) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    List.take_of_length_le (by change 11 ≤ 11; rfl), emitFive_value]

def dimensionROM (N q t : Nat) : PhysicalROM := ⟨[N, q, t], [], []⟩

/-- A fixed program reading only [N,q,t] and emitting an actual opcode and
its encoded HALT. It is a small use of the emitter, not A17's six-program generator. -/
def dimensionGenerator : List PackingOp :=
  [.base (.base (.constant .index 2)),
   .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .old 0)),
   .base (.base (.constant .fresh 2)),
   .base (.base (.constant .flag 0)),
   .base (.base (.constant .value 0)),
   .base (.base (.constant .address 0))] ++ emitFive ++
  [.base (.base (.constant .old 7)),
   .base (.base (.constant .fresh 0)),
   .base (.base (.constant .total 0))] ++ emitFive

def dimensionCode (t : Nat) : List Nat := haltingWords [.base (.constant .value t)]

theorem dimensionGenerator_length : dimensionGenerator.length = 32 := rfl

theorem dimensionGenerator_noJump : ∀ op ∈ dimensionGenerator, NoJump op := by
  simp [dimensionGenerator, emitFive, NoJump]

theorem dimensionGenerator_run (N q t : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false) :
    natRun (dimensionROM N q t) dimensionGenerator 32 state =
      runOps (dimensionROM N q t) dimensionGenerator state := by
  apply natRun_of_straight_segment _ dimensionGenerator dimensionGenerator 0
    (by omega) (by intro position hp; simp) dimensionGenerator_noJump state hpc hactive

theorem dimensionGenerator_value (N q t : Nat) (state : NatState) (position : Nat)
    (hp : position < 10) :
    (runOps (dimensionROM N q t) dimensionGenerator state).heap position =
      (dimensionCode t)[position]'(by change position < 10; exact hp) := by
  interval_cases position <;>
    simp [dimensionGenerator, emitFive, runOps, natExecuteOp, Op.execute, Instruction.execute,
      dimensionROM, PhysicalROM.semantic, PhysicalROM.words, dimensionCode, haltingWords,
      IndexedClosureRAM.programWords, Op.encodeWords, Instruction.encodeWords, Register.word,
      haltWords, Nat.add_assoc]

theorem dimensionGenerator_frame (N q t : Nat) (state : NatState) (address : Nat)
    (ha : 10 ≤ address) :
    (runOps (dimensionROM N q t) dimensionGenerator state).heap address = state.heap address := by
  have hn (n : Nat) (hn : n < 10) : address ≠ n := by omega
  simp [dimensionGenerator, emitFive, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Nat.add_assoc, hn]

theorem dimensionGenerator_pc (N q t : Nat) (state : NatState) :
    (runOps (dimensionROM N q t) dimensionGenerator state).pc = state.pc + 160 := by
  simpa only [dimensionGenerator_length] using
    runOps_pc (dimensionROM N q t) dimensionGenerator state dimensionGenerator_noJump

theorem dimensionGenerator_halts (N q t : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false) :
    natRun (dimensionROM N q t) dimensionGenerator 33 state =
      { runOps (dimensionROM N q t) dimensionGenerator state with halted := true } := by
  rw [show 33 = 32 + 1 by decide, natRun_succ, dimensionGenerator_run N q t state hpc hactive]
  apply natStep_halt
  · rw [dimensionGenerator_pc, hpc, dimensionGenerator_length]
  · rw [runOps_halted, hactive]

theorem dimensionGenerator_prefix_registersFit (N q t bits : Nat) (state : NatState)
    (hfit : RegistersFit bits state) (ht : Fits bits t) (h160 : Fits bits 160)
    (count : Nat) (hc : count ≤ 32) :
    RegistersFit bits (runOps (dimensionROM N q t) (dimensionGenerator.take count) state) := by
  have hsmall (n : Nat) (hn : n ≤ 160) : Fits bits n := lt_of_le_of_lt hn h160
  induction count with
  | zero => exact hfit
  | succ count ih =>
    have hn : count < 32 := by omega
    have hprev := ih hn.le
    rw [List.take_succ_eq_append_getElem (by change count < 32; exact hn), runOps_append]
    change RegistersFit bits (natExecuteOp _
      (dimensionGenerator[count]'(by change count < 32; exact hn))
      (runOps _ (dimensionGenerator.take count) state))
    interval_cases count <;>
      simp only [dimensionGenerator, emitFive, List.getElem_cons_zero, List.getElem_cons_succ,
        List.cons_append, List.nil_append, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hprev | apply fits_update hprev
    all_goals try simp +decide [runOps, natExecuteOp, Op.execute, Instruction.execute,
      dimensionROM, PhysicalROM.semantic, PhysicalROM.words]
    all_goals first | exact ht | exact hsmall _ (by omega)

theorem dimensionGenerator_prefix_accessFits (N q t : Nat) (state : NatState)
    (count : Nat) (hc : count < 32) :
    NatAccessFits (dimensionROM N q t) 10
      (runOps (dimensionROM N q t) (dimensionGenerator.take count) state)
      (dimensionGenerator.getD count (.base (.base (.constant .value 0)))) := by
  interval_cases count <;>
    simp +decide [dimensionGenerator, emitFive, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, dimensionROM, PhysicalROM.words]

theorem dimensionGenerator_code_fit (bits : Nat) (h160 : Fits bits 160) :
    WordsFit bits (packingCode dimensionGenerator) := by
  have hb : ∀ word ∈ packingCode dimensionGenerator, word ≤ 7 := by decide
  intro word hw
  exact lt_of_le_of_lt ((hb word hw).trans (by decide)) h160

theorem dimensionGenerator_prefix_run (N q t : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false) (count : Nat) (hc : count ≤ 32) :
    natRun (dimensionROM N q t) dimensionGenerator count state =
      runOps (dimensionROM N q t) (dimensionGenerator.take count) state := by
  have hlen : (dimensionGenerator.take count).length = count :=
    List.length_take_of_le (by change count ≤ 32; exact hc)
  conv_lhs => rw [← hlen]
  apply natRun_of_straight_segment _ dimensionGenerator (dimensionGenerator.take count) 0
    (by change 0 + _ ≤ 32; rw [hlen]; omega) ?_ ?_ state hpc hactive
  · intro position hp
    simp
  · intro op hop
    exact dimensionGenerator_noJump op (List.mem_of_mem_take hop)

theorem dimensionGenerator_word_eq_nat (N q t bits : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hfit : RegistersFit bits state) (ht : Fits bits t) (h160 : Fits bits 160)
    (count : Nat) (hc : count ≤ 33) :
    packingRun (dimensionROM N q t) dimensionGenerator count (state.toWord bits) =
      (natRun (dimensionROM N q t) dimensionGenerator count state).toWord bits := by
  apply natRun_toWord _ _ _ count (dimensionGenerator_code_fit bits h160)
  intro k hk
  have hk32 : k ≤ 32 := by omega
  rw [dimensionGenerator_prefix_run N q t state hpc hactive k hk32]
  constructor
  · exact dimensionGenerator_prefix_registersFit N q t bits state hfit ht h160 k hk32
  · rw [runOps_pc _ _ _ (fun op hop => dimensionGenerator_noJump op (List.mem_of_mem_take hop)),
      List.length_take_of_le (by change k ≤ 32; exact hk32), hpc, Nat.zero_add]
    exact lt_of_le_of_lt (by omega) h160

/-- From the original three-word input, true physical fetched execution
materializes a complete opcode+HALT. The input heap need not be zero. -/
theorem dimensionGenerator_word_output (N q t bits : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hfit : RegistersFit bits state) (ht : Fits bits t) (h160 : Fits bits 160) :
    let result := packingRun (dimensionROM N q t) dimensionGenerator 33 (state.toWord bits)
    result.halted = true ∧
      ∀ position (hp : position < 10),
        (result.heap (BitVec.ofNat bits position)).toNat =
          (dimensionCode t)[position]'(by change position < 10; exact hp) := by
  dsimp only
  rw [dimensionGenerator_word_eq_nat N q t bits state hpc hactive hfit ht h160 33 le_rfl,
    dimensionGenerator_halts N q t state hpc hactive]
  refine ⟨rfl, ?_⟩
  intro position hp
  have hpos : Fits bits position := lt_of_le_of_lt (by omega) h160
  change (BitVec.ofNat bits ((runOps (dimensionROM N q t) dimensionGenerator state).heap
    (BitVec.ofNat bits position).toNat)).toNat = _
  have hpNat : (BitVec.ofNat bits position).toNat = position := Nat.mod_eq_of_lt hpos
  rw [hpNat, dimensionGenerator_value N q t state position hp, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  interval_cases position <;>
    simp only [dimensionCode, haltingWords, IndexedClosureRAM.programWords, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, Op.encodeWords,
      Instruction.encodeWords, Register.word, haltWords, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals first | exact ht | exact lt_of_le_of_lt (by omega) h160

theorem dimensionGenerator_trace_length : (packingTrace dimensionGenerator).length = 325 := by decide

theorem dimensionGenerator_dynamic_cost (N q t bits : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false) (h160 : Fits bits 160) :
    (packingDynamicTrace (dimensionROM N q t) dimensionGenerator 33 (state.toWord bits)).length = 325 := by
  rw [show 33 = dimensionGenerator.length + 1 by rfl,
    packingDynamicTrace_eq_packingTrace (dimensionROM N q t) dimensionGenerator (state.toWord bits)
      dimensionGenerator_noJump (dimensionGenerator_code_fit bits h160) h160
      (by change BitVec.ofNat bits state.pc = BitVec.ofNat bits 0; rw [hpc]) hactive,
    dimensionGenerator_trace_length]

theorem dimensionGenerator_total_cost (N q t bits : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false) (h160 : Fits bits 160) :
    (dimensionROM N q t).size + (packingCode dimensionGenerator).length + 10 + 8 +
      (packingDynamicTrace (dimensionROM N q t) dimensionGenerator 33 (state.toWord bits)).length = 511 := by
  rw [dimensionGenerator_dynamic_cost N q t bits state hpc hactive h160]
  rfl

theorem dimensionGenerator_word_prefix_safe (N q t bits : Nat) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hfit : RegistersFit bits state) (ht : Fits bits t) (h160 : Fits bits 160)
    (count : Nat) (hc : count < 33) :
    let after := packingRun (dimensionROM N q t) dimensionGenerator count (state.toWord bits)
    after.halted = false ∧ after.pc.toNat = 5 * count ∧
      after.pc.toNat + 4 < (packingCode dimensionGenerator).length ∧
      (match PackingOp.decode (physicalFetch bits (packingCode dimensionGenerator) after.pc.toNat) with
       | none => physicalFetch bits (packingCode dimensionGenerator) after.pc.toNat = haltWords
       | some op => packingAccessFits (dimensionROM N q t) 10 after op) := by
  have hc32 : count ≤ 32 := by omega
  have heq := dimensionGenerator_word_eq_nat N q t bits state hpc hactive hfit ht h160 count (by omega)
  rw [dimensionGenerator_prefix_run N q t state hpc hactive count hc32] at heq
  have hpcNat : (runOps (dimensionROM N q t) (dimensionGenerator.take count) state).pc = 5 * count := by
    rw [runOps_pc _ _ _ (fun op hop => dimensionGenerator_noJump op (List.mem_of_mem_take hop)),
      List.length_take_of_le (by change count ≤ 32; exact hc32), hpc, Nat.zero_add]
  have hpcfit : Fits bits (5 * count) := lt_of_le_of_lt (by omega) h160
  dsimp only
  rw [heq]
  have hpcWord : ((runOps (dimensionROM N q t) (dimensionGenerator.take count) state).toWord bits).pc.toNat =
      5 * count := by
    change (BitVec.ofNat bits _).toNat = _
    rw [hpcNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcfit]
  refine ⟨?_, hpcWord, ?_, ?_⟩
  · change (runOps _ _ state).halted = false
    rw [runOps_halted, hactive]
  · rw [hpcWord, packingCode_length, dimensionGenerator_length]
    omega
  · rw [hpcWord, physicalFetch_eq bits _ _ (dimensionGenerator_code_fit bits h160)]
    by_cases hb : count < 32
    · change (match PackingOp.decode (natFetch dimensionGenerator (5 * count)) with
        | none => natFetch dimensionGenerator (5 * count) = haltWords
        | some op => packingAccessFits _ 10 _ op)
      rw [natFetch_body dimensionGenerator count (by change count < 32; exact hb), decode_encode]
      apply physical_access_of_nat _ 10 _ _
        (dimensionGenerator_prefix_registersFit N q t bits state hfit ht h160 count hc32)
      have ha := dimensionGenerator_prefix_accessFits N q t state count hb
      rw [List.getD_eq_getElem _ _ (by change count < 32; exact hb)] at ha
      exact ha
    · have he : count = 32 := by omega
      subst count
      change (match PackingOp.decode (natFetch dimensionGenerator (5 * dimensionGenerator.length)) with
        | none => natFetch dimensionGenerator (5 * dimensionGenerator.length) = haltWords
        | some op => packingAccessFits (dimensionROM N q t) 10
            ((runOps (dimensionROM N q t) (dimensionGenerator.take 32) state).toWord bits) op)
      rw [natFetch_halt, decode_halt]

end PaperProofs.Structure.LaminarTree.PA17Generator

