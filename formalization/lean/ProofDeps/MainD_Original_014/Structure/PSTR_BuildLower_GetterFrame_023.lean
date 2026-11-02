module

public import Structure.PSTR_BuildLower_NodeCall_022

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

/-! Strengthened actual raw-getter execution. The fixed fourteen-instruction
head and the REAL selected raw path prove every-prefix heap/fresh/base frames.
No frame or supplied run equality is a premise. Frozen A06 sources are unchanged. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput.GetterFrame
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareBankNodeBit022
open PA06A19PrepareBankNodeBit022Raw (pathOps pathIndices steps path_prefix_pc
  path_index_le path_index_lt path_op_matches path_prefix_accessFits path_prefix_frame
  path_prefix_registersFit_wide)

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


private theorem prefix14_frame (rom : PhysicalROM) (state : NatState)
    (count : Nat) (hc : count ≤ 14) :
    let after := runOps rom (prefix14.take count) state
    after.heap = state.heap ∧ after.register .fresh = state.register .fresh ∧
      after.register .address = state.register .address := by
  interval_cases count <;> simp [prefix14, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]

theorem nat_query_framed (factor q : Nat) (full : List (Finset (Fin q))) (hf : 16 ≤ factor)
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (base heapWords : Nat) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : NatState) (hpc : before.pc = 5 * start) (hactive : before.halted = false)
    (hnode : before.register .old = node.val) (htool : before.register .fresh = tool.val)
    (hbase : before.register .address = base) (cached : CachedNode q full base node before)
    (hfit : RegistersFit (indexWidth factor full.length q) before)
    (hroom : ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords)
    (hend : Fits (indexWidth factor full.length q) (5 * (start + 46))) :
    ∃ count ≤ 35,
      NatResult factor q full containing start heapWords before node tool count ∧
      ∀ k ≤ count,
        let current := natRun (rawIncidenceROM q full) containing k before
        current.heap = before.heap ∧ current.register .fresh = before.register .fresh ∧
          current.register .address = before.register .address := by
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
  refine ⟨14 + n, by omega, ?_, ?_⟩
  · constructor
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
  
  · intro k hk
    by_cases kh : k ≤ 14
    · rw [header_run_prefix q full containing start code before hpc hactive k kh]
      exact prefix14_frame (rawIncidenceROM q full) before k kh
    · have kr : k = 14 + (k - 14) := by omega
      rw [kr, runTail, pathEq (k - 14) (by omega)]
      have hh := path_prefix_frame q full (start + 14) candidate.val tool.val mid (k - 14) (by omega)
      exact ⟨hh.1.trans hm.1, hh.2.2.1.trans hm.2.2.1,
        hh.2.2.2.trans (prefix14_address (rawIncidenceROM q full) before)⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput.GetterFrame
