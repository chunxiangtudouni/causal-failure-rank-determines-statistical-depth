module

public import Structure.PA06_A19Prepare_ROM_001
public import Structure.PA06_A19Prepare_CompactCandidates007
public import Structure.PA06_A19Prepare_BankNodeBit022_Raw
public import Structure.PA06_A19Prepare_ControlBank017
public import PaperProofs.Structure.PA17_WordBounds_023
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Real fixed node-incidence getter from the raw ROM and actual compact
ord cache. All paths preserve runtime hardware.address. No heap store, header stash or supplied node-incidence ROM is
used. The old register is a node on entry and the actually loaded candidate
on exit. Other incoming registers may use the WHOLE selected word width. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankNodeBit022

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareBankNodeBit022Raw (header headerLead classify classifyLead singletonTest singletonLead stageRead)
open PA06A19PrepareBankNodeBit022Raw (pathOps pathIndices steps stage_pointer_bound pathOps_length
  path_index_le path_index_lt path_op_matches path_prefix_pc path_prefix_accessFits path_prefix_frame
  path_prefix_registersFit_wide)

def prefix14 : List PackingOp :=
  [.base (.base (.constant .index 0)),
   .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .index 1)),
   .base (.base (.loadROM .input .value .index)),
   .base (.base (.add .total .total .value)),
   .base (.base (.constant .value 1)),
   .base (.base (.add .total .total .value)),
   .base (.base (.constant .value 2)),
   .arithmetic .multiply .total .total .value,
   .base (.base (.constant .value 532)),
   .base (.base (.add .total .total .value)),
   .base (.base (.add .index .address .total)),
   .base (.base (.add .index .index .old)),
   .base (.base (.loadHeap .old .index))]

def programAt (start : Nat) : List PackingOp :=
  prefix14 ++ PA06A19PrepareBankNodeBit022Raw.programAt (start + 14)

theorem prefix14_length : prefix14.length = 14 := rfl

theorem programAt_length (start : Nat) : (programAt start).length = 46 := rfl

theorem prefix14_noJump : ∀ op ∈ prefix14, NoJump op := by simp [prefix14, NoJump]

def ordAddress (N q base node : Nat) : Nat := base + 532 + 2 * (N + q + 1) + node

/-- Exactly one actual ord word and its independent candidate support;
no bit, query answer or performance conclusion is a premise. base means the runtime controlBase. -/
def CachedNode (q : Nat) (full : List (Finset (Fin q))) (base : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (state : NatState) : Prop :=
  ∃ candidate : Fin (full.length + q + 1),
    state.heap (ordAddress full.length q base node.val) = candidate.val ∧
      RawCandidateParents.candidateSupport q full candidate.val =
        (prepareNormalization q full).indexed.decode node

private theorem prefix14_effect (q : Nat) (full : List (Finset (Fin q)))
    (base node candidate : Nat) (state : NatState)
    (hold : state.register .old = node) (hbase : state.register .address = base)
    (hcache : state.heap (ordAddress full.length q base node) = candidate) :
    let after := runOps (rawIncidenceROM q full) prefix14 state
    after.heap = state.heap ∧ after.register .old = candidate ∧
      after.register .fresh = state.register .fresh ∧
      after.pc = state.pc + 70 ∧ after.halted = state.halted := by
  simp [prefix14, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    raw_header_N, raw_header_q, hold, hbase, ordAddress, Nat.mul_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hcache ⊢
  exact hcache

theorem prefix14_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom prefix14 state).register .address = state.register .address := rfl

theorem prefix14_address_take (rom : PhysicalROM) (state : NatState) (count : Nat) (hc : count ≤ 14) :
    (runOps rom (prefix14.take count) state).register .address = state.register .address := by
  interval_cases count <;> simp [prefix14, runOps, natExecuteOp, Op.execute, Instruction.execute]

private theorem prefix14_registersFit (factor q : Nat) (full : List (Finset (Fin q)))
    (base node heapWords : Nat) (candidate : Fin (full.length + q + 1)) (state : NatState)
    (hfit : RegistersFit (indexWidth factor full.length q) state)
    (hold : state.register .old = node) (hbase : state.register .address = base)
    (hcache : state.heap (ordAddress full.length q base node) = candidate.val)
    (hroom : ordAddress full.length q base node < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords) :
    ∀ count ≤ 14, RegistersFit (indexWidth factor full.length q)
      (runOps (rawIncidenceROM q full) (prefix14.take count) state) := by
  have ha := hfit .address
  have hi := hfit .index
  have hv := hfit .value
  have ht := hfit .total
  have ho := hfit .old
  have hfresh := hfit .fresh
  have hflag := hfit .flag
  have hc := candidate.isLt
  intro count hcount
  interval_cases count <;> intro register <;> cases register <;>
    simp [prefix14, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      raw_header_N, raw_header_q, hold, hbase, ordAddress, Nat.mul_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hcache ⊢
  all_goals
    dsimp only [Fits, ordAddress] at *
    omega

private theorem prefix14_accessFits (q : Nat) (full : List (Finset (Fin q)))
    (base node heapWords : Nat) (state : NatState)
    (hold : state.register .old = node) (hbase : state.register .address = base)
    (hroom : ordAddress full.length q base node < heapWords) :
    ∀ count (hc : count < 14),
      NatAccessFits (rawIncidenceROM q full) heapWords
        (runOps (rawIncidenceROM q full) (prefix14.take count) state) (prefix14[count]) := by
  intro count hc
  interval_cases count <;>
    simp [prefix14, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      hold, hbase, NatAccessFits, AccessFits,
      rawIncidenceROM, PhysicalROM.words, PhysicalROM.semantic, incidence_length]
  all_goals
    dsimp only [ordAddress] at hroom
    omega


/-- A concrete instruction slice, discharged by a fixed append layout. -/
def CodeAt (containing : List PackingOp) (start : Nat) : Prop :=
  start + 46 ≤ containing.length ∧ ∀ position < 46,
    containing.getD (start + position) PA06A19PrepareBankNodeBit022Raw.paddingOp =
      (programAt start).getD position PA06A19PrepareBankNodeBit022Raw.paddingOp

/-- No code oracle is needed at the fixed append layout. -/
theorem append_code (left right : List PackingOp) :
    CodeAt (left ++ programAt left.length ++ right) left.length := by
  constructor
  · simp only [List.length_append, programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right PA06A19PrepareBankNodeBit022Raw.paddingOp _
      (by simp only [List.length_append, programAt_length]; omega),
      List.getD_append_right left (programAt left.length) PA06A19PrepareBankNodeBit022Raw.paddingOp _ (by omega),
      Nat.add_sub_cancel_left]

private theorem header_code (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (position : Nat) (hp : position < 14) :
    containing.getD (start + position) PA06A19PrepareBankNodeBit022Raw.paddingOp =
      prefix14.getD position PA06A19PrepareBankNodeBit022Raw.paddingOp := by
  have hh := code.2 position (by omega)
  rw [programAt, List.getD_append _ _ _ _ (by rw [prefix14_length]; exact hp)] at hh
  exact hh

private theorem query_code (containing : List PackingOp) (start : Nat) (code : CodeAt containing start) :
    start + 14 + 32 ≤ containing.length ∧ ∀ position < 32,
      containing.getD (start + 14 + position) PA06A19PrepareBankNodeBit022Raw.paddingOp =
        (PA06A19PrepareBankNodeBit022Raw.programAt (start + 14)).getD position PA06A19PrepareBankNodeBit022Raw.paddingOp := by
  refine ⟨by have hh := code.1; omega, ?_⟩
  intro position hp
  have hh := code.2 (14 + position) (by omega)
  rw [programAt, List.getD_append_right _ _ _ _ (by rw [prefix14_length]; omega), prefix14_length] at hh
  simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using hh

private theorem header_run_prefix (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (before : NatState) (hpc : before.pc = 5 * start) (hactive : before.halted = false)
    (count : Nat) (hc : count ≤ 14) :
    natRun (rawIncidenceROM q full) containing count before =
      runOps (rawIncidenceROM q full) (prefix14.take count) before := by
  have hlen : (prefix14.take count).length = count := List.length_take_of_le (by rw [prefix14_length]; exact hc)
  conv_lhs => rw [← hlen]
  apply natRun_of_straight_segment _ containing (prefix14.take count) start (by have hh := code.1; omega)
    ?_ (fun op hop => prefix14_noJump op (List.mem_of_mem_take hop)) before hpc hactive
  intro position hp
  have hi : position < 14 := by rw [hlen] at hp; omega
  have hh := header_code containing start code position hi
  rw [List.getD_eq_getElem _ _ (by have hx := code.1; omega),
    List.getD_eq_getElem _ _ (by rw [prefix14_length]; exact hi)] at hh
  simpa only [List.getElem_take] using hh


/-- A proved execution result. This structure is never a caller premise. -/
structure NatResult (factor q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start heapWords : Nat) (before : NatState)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) (count : Nat) : Prop where
  value : (natRun (rawIncidenceROM q full) containing count before).register .value =
    bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node))
  fresh : (natRun (rawIncidenceROM q full) containing count before).register .fresh = before.register .fresh
  heap : (natRun (rawIncidenceROM q full) containing count before).heap = before.heap
  pc : (natRun (rawIncidenceROM q full) containing count before).pc = 5 * (start + 46)
  active : (natRun (rawIncidenceROM q full) containing count before).halted = false
  address : (natRun (rawIncidenceROM q full) containing count before).register .address = before.register .address
  prefix_safe : ∀ k ≤ count,
    let state := natRun (rawIncidenceROM q full) containing k before
    RegistersFit (indexWidth factor full.length q) state ∧
      Fits (indexWidth factor full.length q) state.pc ∧ state.halted = false ∧
      (k < count → ∃ (index : Nat) (hi : index < containing.length), state.pc = 5 * index ∧
        NatAccessFits (rawIncidenceROM q full) heapWords state (containing[index]))
  prefix_address : ∀ k ≤ count,
    (natRun (rawIncidenceROM q full) containing k before).register .address = before.register .address

/-- Actual 14+32 body on raw ROM, from one materialized ord cache word.
The only width assumption uses the full selected factor, not 16. -/
theorem nat_query (factor q : Nat) (full : List (Finset (Fin q))) (hf : 16 ≤ factor)
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (base heapWords : Nat) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : NatState) (hpc : before.pc = 5 * start) (hactive : before.halted = false)
    (hnode : before.register .old = node.val) (htool : before.register .fresh = tool.val)
    (hbase : before.register .address = base) (cached : CachedNode q full base node before)
    (hfit : RegistersFit (indexWidth factor full.length q) before)
    (hroom : ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords)
    (hend : Fits (indexWidth factor full.length q) (5 * (start + 46))) :
    ∃ count ≤ 35, NatResult factor q full containing start heapWords before node tool count := by
  obtain ⟨candidate, cache, support⟩ := cached
  let mid := runOps (rawIncidenceROM q full) prefix14 before
  have hm := prefix14_effect q full base node.val candidate.val before hnode hbase cache
  change mid.heap = before.heap ∧ mid.register .old = candidate.val ∧
    mid.register .fresh = before.register .fresh ∧ mid.pc = before.pc + 70 ∧ mid.halted = before.halted at hm
  have hmPC : mid.pc = 5 * (start + 14) := by rw [hm.2.2.2.1, hpc]; omega
  have hmActive : mid.halted = false := hm.2.2.2.2.trans hactive
  have hmTool : mid.register .fresh = tool.val := hm.2.2.1.trans htool
  have hmFit : RegistersFit (indexWidth factor full.length q) mid :=
    prefix14_registersFit factor q full base node.val heapWords candidate before hfit hnode hbase cache hroom hheap 14 le_rfl
  have qcode := query_code containing start code
  have returned := PA06A19PrepareBankNodeBit022Raw.query q full containing (start + 14)
    qcode.1 qcode.2 candidate tool mid hmPC hmActive hm.2.1 hmTool
  let n := steps full.length candidate.val tool.val
  change PA06A19PrepareBankNodeBit022Raw.ReturnedActive (start + 14) mid
    (natRun (rawIncidenceROM q full) containing n mid)
    (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) at returned
  have hn : n ≤ 19 := PA06A19PrepareBankNodeBit022Raw.steps_le full.length candidate.val tool.val
  have hbit : bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅)) =
      bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
    change bit (decide (tool ∈ RawCandidateParents.candidateSupport q full candidate.val)) = _
    rw [support]
  have headerRun : natRun (rawIncidenceROM q full) containing 14 before = mid := by
    exact header_run_prefix q full containing start code before hpc hactive 14 le_rfl
  have runTail (k : Nat) : natRun (rawIncidenceROM q full) containing (14 + k) before =
      natRun (rawIncidenceROM q full) containing k mid := by rw [natRun_add, headerRun]
  have pathEq (k : Nat) (hk : k ≤ n) :
      natRun (rawIncidenceROM q full) containing k mid =
        runOps (rawIncidenceROM q full) ((pathOps (start + 14) full.length candidate.val tool.val).take k) mid :=
    PA06A19PrepareBankNodeBit022Raw.natRun_prefix_eq q full containing (start + 14) qcode.1 qcode.2
      candidate tool mid hmPC hmActive hm.2.1 hmTool k hk
  refine ⟨14 + n, by omega, ?_⟩
  constructor
  · rw [runTail, returned.1, hbit]
  · rw [runTail, returned.2.2.1, hm.2.2.1]
  · rw [runTail, returned.2.2.2.2.1, hm.1]
  · rw [runTail, returned.2.2.2.2.2.1]
  · rw [runTail]
    exact returned.2.2.2.2.2.2
  · rw [runTail, returned.2.2.2.1, prefix14_address]
  · intro k hk
    by_cases kh : k < 14
    · rw [header_run_prefix q full containing start code before hpc hactive k kh.le]
      have hp : (runOps (rawIncidenceROM q full) (prefix14.take k) before).pc = 5 * (start + k) := by
        rw [runOps_pc _ _ _ (fun op hop => prefix14_noJump op (List.mem_of_mem_take hop)),
          List.length_take_of_le (by rw [prefix14_length]; exact kh.le), hpc]
        omega
      refine ⟨prefix14_registersFit factor q full base node.val heapWords candidate before hfit hnode hbase cache hroom hheap k kh.le,
        ?_, (runOps_halted _ _ _).trans hactive, ?_⟩
      · rw [hp]
        exact lt_of_le_of_lt (by omega) hend
      · intro _
        refine ⟨start + k, by have hb := code.1; omega, hp, ?_⟩
        have hh := header_code containing start code k kh
        rw [List.getD_eq_getElem _ _ (by have hb := code.1; omega),
          List.getD_eq_getElem _ _ (by rw [prefix14_length]; exact kh)] at hh
        rw [hh]
        exact prefix14_accessFits q full base node.val heapWords before hnode hbase hroom k kh
    · have hlarge : 14 ≤ k := by omega
      have kr : k = 14 + (k - 14) := by omega
      have kk : k - 14 ≤ n := by omega
      have stateEq : natRun (rawIncidenceROM q full) containing k before =
          runOps (rawIncidenceROM q full) ((pathOps (start + 14) full.length candidate.val tool.val).take (k - 14)) mid := by
        conv_lhs => rw [kr, runTail, pathEq (k - 14) kk]
      rw [stateEq]
      have hp := path_prefix_pc q full (start + 14) candidate tool mid hmPC hm.2.1 hmTool (k - 14) kk
      have hi := path_index_le full.length candidate.val tool.val (k - 14) kk
      refine ⟨path_prefix_registersFit_wide factor q full hf (start + 14) candidate tool mid hmFit
        (by simpa only [Nat.add_assoc] using hend) hm.2.1 hmTool (k - 14) kk, ?_,
        (runOps_halted _ _ _).trans hmActive, ?_⟩
      · rw [hp]
        exact lt_of_le_of_lt (by omega) hend
      · intro kstrict
        have kc : k - 14 < n := by omega
        let index := (pathIndices full.length candidate.val tool.val).getD (k - 14) 32
        have i32 : index < 32 := path_index_lt _ _ _ _ kc
        refine ⟨start + 14 + index, by have hb := qcode.1; omega, hp, ?_⟩
        have hh := (qcode.2 index i32).trans (path_op_matches (start + 14) full.length candidate.val tool.val (k - 14) kc)
        rw [List.getD_eq_getElem containing PA06A19PrepareBankNodeBit022Raw.paddingOp (by have hb := qcode.1; omega)] at hh
        rw [hh]
        exact path_prefix_accessFits q full (start + 14) heapWords candidate tool mid hm.2.1 hmTool (k - 14) kc

  · intro k hk
    by_cases kh : k ≤ 14
    · rw [header_run_prefix q full containing start code before hpc hactive k kh]
      exact prefix14_address_take (rawIncidenceROM q full) before k kh
    · have kr : k = 14 + (k - 14) := by omega
      rw [kr, runTail, pathEq (k - 14) (by omega)]
      exact ((path_prefix_frame q full (start + 14) candidate.val tool.val mid (k - 14)
        (by omega)).2.2.2).trans (prefix14_address (rawIncidenceROM q full) before)

private theorem input_prefix (q : Nat) (full : List (Finset (Fin q))) (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

/-- The old-range access proof is enough for the actual tail-bearing input;
no hypothesis of equal runs or a correct bit is introduced. -/
private theorem transport_nat (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (containing : List PackingOp) (start heapWords : Nat)
    (before : NatState) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (count : Nat) (result : NatResult factor q full containing start heapWords before node tool count)
    (k : Nat) (hk : k ≤ count) :
    natRun (CompactControllerClaims.controllerInput q full initialUsed) containing k before =
      natRun (rawIncidenceROM q full) containing k before := by
  apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed) heapWords
  intro clock hclock _active op hd
  obtain ⟨index, hi, pc, access⟩ := (result.prefix_safe clock (by omega)).2.2.2 (by omega)
  have actualDecode : PackingOp.decode (natFetch containing
      (natRun (rawIncidenceROM q full) containing clock before).pc) = some (containing[index]) := by
    rw [pc, natFetch_body containing index hi, decode_encode]
  have hop : op = containing[index] := Option.some.inj (hd.symm.trans actualDecode)
  subst op
  exact access

/-- Natural view of an arbitrary full-width caller, not a small-register
restriction. It is reconstructed exactly by toWord at the same width. -/
def wordView {bits : Nat} (state : WordState bits) : NatState :=
  ⟨fun register => (state.register register).toNat,
    fun address => (state.heap (BitVec.ofNat bits address)).toNat, state.pc.toNat, state.halted⟩

theorem wordView_toWord {bits : Nat} (state : WordState bits) : (wordView state).toWord bits = state := by
  apply wordState_ext
  · funext register
    simp only [wordView, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · funext address
    simp only [wordView, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [wordView, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

/-- Physical representation of the single ord word used by this call. -/
def CachedWordNode {bits q : Nat} (full : List (Finset (Fin q))) (base : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (heap : BitVec bits → BitVec bits) : Prop :=
  ∃ candidate : Fin (full.length + q + 1),
    (heap (BitVec.ofNat bits (ordAddress full.length q base node.val))).toNat = candidate.val ∧
      RawCandidateParents.candidateSupport q full candidate.val =
        (prepareNormalization q full).indexed.decode node

/-- Real factor-width call on the original tail-bearing controllerInput.
The arbitrary caller registers are represented at their FULL selected width.
Every clock up to return remains active; all actual fetched accesses are
proved from raw old-range bounds and the one actual ord-cache word. -/
theorem word_query (factor q : Nat) (full : List (Finset (Fin q))) (hf : 16 ≤ factor)
    (initialUsed : Finset (Fin q)) (containing : List PackingOp) (start : Nat)
    (code : CodeAt containing start) (base heapWords : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : WordState (indexWidth factor full.length q))
    (hpc : before.pc.toNat = 5 * start) (hactive : before.halted = false)
    (hnode : (before.register .old).toNat = node.val)
    (htool : (before.register .fresh).toNat = tool.val)
    (hbase : (before.register .address).toNat = base)
    (cached : CachedWordNode full base node before.heap)
    (hroom : ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords)
    (hend : Fits (indexWidth factor full.length q) (5 * (start + 46)))
    (hcode : WordsFit (indexWidth factor full.length q) (packingCode containing)) :
    ∃ count ≤ 35,
      let runtime := CompactControllerClaims.controllerInput q full initialUsed
      let after := packingRun runtime containing count before
      (after.register .value).toNat = bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) ∧
      after.register .fresh = before.register .fresh ∧ after.register .address = before.register .address ∧ after.heap = before.heap ∧
      after.pc.toNat = 5 * (start + 46) ∧ after.halted = false ∧
      ∀ k < count,
        let state := packingRun runtime containing k before
        state.halted = false ∧ state.register .address = before.register .address ∧
        state.pc.toNat + 4 < (packingCode containing).length ∧
        ∃ op, PackingOp.decode (fetch containing state) = some op ∧ packingAccessFits runtime heapWords state op := by
  let bits := indexWidth factor full.length q
  let runtime := CompactControllerClaims.controllerInput q full initialUsed
  let initial := wordView before
  have regs : RegistersFit bits initial := fun register => (before.register register).isLt
  obtain ⟨count, bound, result⟩ := nat_query factor q full hf containing start code base heapWords node tool initial
    hpc hactive hnode htool hbase cached regs hroom hheap hend
  have eq (k : Nat) (hk : k ≤ count) :=
    transport_nat factor q full initialUsed containing start heapWords initial node tool count result k hk
  have word (k : Nat) (hk : k ≤ count) : packingRun runtime containing k before =
      (natRun (rawIncidenceROM q full) containing k initial).toWord bits := by
    rw [← wordView_toWord before]
    have hrun := natRun_toWord runtime containing initial k hcode (by
      intro c hc
      rw [eq c (by omega)]
      exact ⟨(result.prefix_safe c (by omega)).1, (result.prefix_safe c (by omega)).2.1⟩)
    exact hrun.trans (congrArg (NatState.toWord bits) (eq k hk))
  refine ⟨count, bound, ?_⟩
  dsimp only
  rw [word count le_rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, result.active, ?_⟩
  · change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((result.prefix_safe count le_rfl).1 .value), result.value]
  · change BitVec.ofNat bits _ = _
    rw [result.fresh]
    simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat bits _ = _
    rw [result.address]
    simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · funext address
    change BitVec.ofNat bits ((natRun (rawIncidenceROM q full) containing count initial).heap address.toNat) = before.heap address
    rw [result.heap]
    simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (result.prefix_safe count le_rfl).2.1, result.pc]
  · intro k hk
    obtain ⟨index, hi, pc, access⟩ := (result.prefix_safe k hk.le).2.2.2 hk
    rw [word k hk.le]
    have pcWord : ((natRun (rawIncidenceROM q full) containing k initial).toWord bits).pc.toNat = 5 * index := by
      change (BitVec.ofNat bits _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (result.prefix_safe k hk.le).2.1, pc]
    refine ⟨(result.prefix_safe k hk.le).2.2.1, ?_, ?_, containing[index], ?_, ?_⟩
    · change BitVec.ofNat bits _ = _
      rw [result.prefix_address k hk.le]
      simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [pcWord, packingCode_length]
      omega
    · change PackingOp.decode (physicalFetch bits (packingCode containing)
        ((natRun (rawIncidenceROM q full) containing k initial).toWord bits).pc.toNat) = _
      rw [pcWord, physicalFetch_eq _ _ _ hcode]
      change PackingOp.decode (natFetch containing (5 * index)) = _
      rw [natFetch_body containing index hi, decode_encode]
    · apply physical_access_of_nat runtime heapWords _ _ (result.prefix_safe k hk.le).1
      cases hop : containing[index] with
      | base op =>
        exact PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed) heapWords _ op
          (by simpa only [hop, NatAccessFits] using access)
      | arithmetic operation target left right => trivial
      | jumpIfZero condition target => trivial

/-- Representation-only adapter from the exact actual copy output. No bit
answer, supplied tree or safe-prefix result is an input. The copy equality
is supplied by ControlBank017.copy_values_frame/compact_cache_copy. -/
theorem cachedNode_of_copiedCache {q : Nat} {full : List (Finset (Fin q))}
    {before after : NatState} (entry : PA06A19PrepareCompactCandidates007.ParentEntry q full before)
    (hq : 0 < q) (CB : Nat)
    (copied : ∀ address < PA06A19PrepareControlBank017.cacheLength full.length q,
      after.heap (CB + 512 + address) = before.heap address)
    (node : (prepareNormalization q full).indexed.NodeId) : CachedNode q full CB node after := by
  obtain ⟨order, inverse, tables, support⟩ := entry.tables
  have hn : node.val < (RawCandidateOrder.retainedCandidateIndices q full).length := by
    rw [← RawCandidateParentRAM.prepared_nodes_eq_retained q full hq]
    exact node.isLt
  have hbound := prepared_indexed_size_le q full
  have hnode := node.isLt
  let source := RawCandidateOrderingRAM.arraySlot 16 (full.length + q + 1) 2 node.val
  have hs : source < PA06A19PrepareControlBank017.cacheLength full.length q := by
    unfold source RawCandidateOrderingRAM.arraySlot PA06A19PrepareControlBank017.cacheLength
      PA06A19PrepareControlBank017.mass
    omega
  have he : ordAddress full.length q CB node.val = CB + 512 + source := by
    unfold ordAddress source RawCandidateOrderingRAM.arraySlot
    omega
  refine ⟨⟨order node.val, tables.order_valid node.val hn⟩, ?_, support node⟩
  rw [he, copied source hs]
  exact tables.ordered node.val hn

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankNodeBit022
