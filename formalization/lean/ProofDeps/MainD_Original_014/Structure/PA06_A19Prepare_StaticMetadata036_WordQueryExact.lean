module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordQuery

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED exact-clock adapter for the actual frozen022 query.
The original Nat scanner uses nodeReadClock, not an arbitrary returning
clock. Raw.steps is exactly5/19/17/19, so the complete14+raw clock is
19/33/31/33. No Nat instruction, loop budget or caller model changes.
Frozen022 exposes Raw.path safety, but its14-op header numeric lemmas
are private; only those small local adapters are restated below. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (preparedSize mass actualControlBase actualAllocation RunFacts)
open PA06A19PrepareBankNodeBit022
  (prefix14 prefix14_length prefix14_noJump prefix14_address prefix14_address_take
    ordAddress CodeAt CachedNode NatResult)
open PA06A19PrepareBankNodeBit022Raw
  (steps pathOps pathIndices path_index_le path_index_lt path_op_matches
    path_prefix_pc path_prefix_accessFits path_prefix_frame path_prefix_registersFit_wide)

theorem nodeReadClock_exact_cases (N : Nat) (heap : Nat → Nat) (CB M node tool : Nat) :
    nodeReadClock N heap CB M node tool =
      if heap (rawOrdAddress CB M node) = 0 then 19
      else if heap (rawOrdAddress CB M node) ≤ N then 33
      else if heap (rawOrdAddress CB M node) - N - 1 = tool then 31 else 33 := by
  unfold nodeReadClock steps
  split_ifs <;> rfl

private theorem exactQuery_prefix14_registersFit (factor q : Nat) (full : List (Finset (Fin q)))
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

private theorem exactQuery_prefix14_accessFits (q : Nat) (full : List (Finset (Fin q)))
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


private theorem exactQuery_header_code (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (position : Nat) (hp : position < 14) :
    containing.getD (start + position) PA06A19PrepareBankNodeBit022Raw.paddingOp =
      prefix14.getD position PA06A19PrepareBankNodeBit022Raw.paddingOp := by
  have hh := code.2 position (by omega)
  rw [PA06A19PrepareBankNodeBit022.programAt,
    List.getD_append _ _ _ _ (by rw [prefix14_length]; exact hp)] at hh
  exact hh

private theorem exactQuery_query_code (containing : List PackingOp) (start : Nat) (code : CodeAt containing start) :
    start + 14 + 32 ≤ containing.length ∧ ∀ position < 32,
      containing.getD (start + 14 + position) PA06A19PrepareBankNodeBit022Raw.paddingOp =
        (PA06A19PrepareBankNodeBit022Raw.programAt (start + 14)).getD position PA06A19PrepareBankNodeBit022Raw.paddingOp := by
  refine ⟨by have hh := code.1; omega, ?_⟩
  intro position hp
  have hh := code.2 (14 + position) (by omega)
  rw [PA06A19PrepareBankNodeBit022.programAt,
    List.getD_append_right _ _ _ _ (by rw [prefix14_length]; omega), prefix14_length] at hh
  simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using hh

private theorem exactQuery_header_run_prefix (q : Nat) (full : List (Finset (Fin q)))
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
  have hh := exactQuery_header_code containing start code position hi
  rw [List.getD_eq_getElem _ _ (by have hx := code.1; omega),
    List.getD_eq_getElem _ _ (by rw [prefix14_length]; exact hi)] at hh
  simpa only [List.getElem_take] using hh


/-- The same real prefix14 and Raw.path at the Nat scanner's named clock.
All proper prefixes get actual fetched-instruction access, rather than a
final-output-only statement or a supplied whole-run safety premise. -/
private theorem nodeBit_exact_nat_result (factor q : Nat) (full : List (Finset (Fin q))) (hf : 16 ≤ factor)
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (base heapWords : Nat) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : NatState) (hpc : before.pc = 5 * start) (hactive : before.halted = false)
    (hnode : before.register .old = node.val) (htool : before.register .fresh = tool.val)
    (hbase : before.register .address = base) (cached : CachedNode q full base node before)
    (hfit : RegistersFit (indexWidth factor full.length q) before)
    (hroom : ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords)
    (hend : Fits (indexWidth factor full.length q) (5 * (start + 46))) :
    NatResult factor q full containing start heapWords before node tool
      (nodeReadClock full.length before.heap base (mass q full) node.val tool.val) := by
  obtain ⟨candidate, cache, support⟩ := cached
  let mid := runOps (rawIncidenceROM q full) prefix14 before
  have fetched := nodeBit_prefix_effect q full base node.val candidate.val before hnode hbase cache
  have hm : mid.heap = before.heap ∧ mid.register .old = candidate.val ∧
      mid.register .fresh = before.register .fresh ∧ mid.pc = before.pc + 70 ∧
      mid.halted = before.halted :=
    ⟨fetched.2.2.2.1, fetched.1, fetched.2.1, fetched.2.2.2.2.1, fetched.2.2.2.2.2⟩
  change mid.heap = before.heap ∧ mid.register .old = candidate.val ∧
    mid.register .fresh = before.register .fresh ∧ mid.pc = before.pc + 70 ∧ mid.halted = before.halted at hm
  have hmPC : mid.pc = 5 * (start + 14) := by rw [hm.2.2.2.1, hpc]; omega
  have hmActive : mid.halted = false := hm.2.2.2.2.trans hactive
  have hmTool : mid.register .fresh = tool.val := hm.2.2.1.trans htool
  have hmFit : RegistersFit (indexWidth factor full.length q) mid :=
    exactQuery_prefix14_registersFit factor q full base node.val heapWords candidate before hfit hnode hbase cache hroom hheap 14 le_rfl
  have qcode := exactQuery_query_code containing start code
  have returned := PA06A19PrepareBankNodeBit022Raw.query q full containing (start + 14)
    qcode.1 qcode.2 candidate tool mid hmPC hmActive hm.2.1 hmTool
  let n := steps full.length candidate.val tool.val
  change PA06A19PrepareBankNodeBit022Raw.ReturnedActive (start + 14) mid
    (natRun (rawIncidenceROM q full) containing n mid)
    (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) at returned
  have hbit : bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅)) =
      bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
    change bit (decide (tool ∈ RawCandidateParents.candidateSupport q full candidate.val)) = _
    rw [support]
  have headerRun : natRun (rawIncidenceROM q full) containing 14 before = mid := by
    exact exactQuery_header_run_prefix q full containing start code before hpc hactive 14 le_rfl
  have runTail (k : Nat) : natRun (rawIncidenceROM q full) containing (14 + k) before =
      natRun (rawIncidenceROM q full) containing k mid := by rw [natRun_add, headerRun]
  have pathEq (k : Nat) (hk : k ≤ n) :
      natRun (rawIncidenceROM q full) containing k mid =
        runOps (rawIncidenceROM q full) ((pathOps (start + 14) full.length candidate.val tool.val).take k) mid :=
    PA06A19PrepareBankNodeBit022Raw.natRun_prefix_eq q full containing (start + 14) qcode.1 qcode.2
      candidate tool mid hmPC hmActive hm.2.1 hmTool k hk
  have exactClock : nodeReadClock full.length before.heap base (mass q full) node.val tool.val = 14 + n := by
    unfold nodeReadClock
    change 14 + steps full.length (before.heap (ordAddress full.length q base node.val)) tool.val = 14 + n
    rw [cache]
  rw [exactClock]
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
    · rw [exactQuery_header_run_prefix q full containing start code before hpc hactive k kh.le]
      have hp : (runOps (rawIncidenceROM q full) (prefix14.take k) before).pc = 5 * (start + k) := by
        rw [runOps_pc _ _ _ (fun op hop => prefix14_noJump op (List.mem_of_mem_take hop)),
          List.length_take_of_le (by rw [prefix14_length]; exact kh.le), hpc]
        omega
      refine ⟨exactQuery_prefix14_registersFit factor q full base node.val heapWords candidate before hfit hnode hbase cache hroom hheap k kh.le,
        ?_, (runOps_halted _ _ _).trans hactive, ?_⟩
      · rw [hp]
        exact lt_of_le_of_lt (by omega) hend
      · intro _
        refine ⟨start + k, by have hb := code.1; omega, hp, ?_⟩
        have hh := exactQuery_header_code containing start code k kh
        rw [List.getD_eq_getElem _ _ (by have hb := code.1; omega),
          List.getD_eq_getElem _ _ (by rw [prefix14_length]; exact kh)] at hh
        rw [hh]
        exact exactQuery_prefix14_accessFits q full base node.val heapWords before hnode hbase hroom k kh
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
    · rw [exactQuery_header_run_prefix q full containing start code before hpc hactive k kh]
      exact prefix14_address_take (rawIncidenceROM q full) before k kh
    · have kr : k = 14 + (k - 14) := by omega
      rw [kr, runTail, pathEq (k - 14) (by omega)]
      exact ((path_prefix_frame q full (start + 14) candidate.val tool.val mid (k - 14)
        (by omega)).2.2.2).trans (prefix14_address (rawIncidenceROM q full) before)

/-- Exact-clock query safety on the SAME original common32/8192 allocation.
The returned clock is definitionally the one consumed by ScanIteration and
StageIteration. All source ord-room and heap-width obligations are internal. -/
theorem nodeBit_actual_exact_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : ScanQueryCodeAt containing start)
    (before : NatState) (data : RawCardData q full (actualControlBase q full) before)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hpc : before.pc = 5 * start) (ha : before.halted = false)
    (hn : before.register .old = node.val) (ht : before.register .fresh = tool.val)
    (hCB : before.register .address = actualControlBase q full)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 46))) :
    let clock := nodeReadClock full.length before.heap (actualControlBase q full) (mass q full) node.val tool.val
    PA06A19PrepareBankNodeBit022.NatResult 32 q full containing start (actualAllocation q full) before node tool clock ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have htM := prepared_indexed_size_le q full
  have hnM : node.val < preparedSize q full := node.isLt
  have hord : PA06A19PrepareBankNodeBit022.ordAddress full.length q (actualControlBase q full) node.val < actualAllocation q full := by
    have h := room.1
    unfold PA06A19PrepareBankNodeBit022.ordAddress PA06A19PrepareChildrenCache023.highCacheEnd at *
    change preparedSize q full ≤ mass q full at htM
    unfold mass at *
    omega
  have result := nodeBit_exact_nat_result 32 q full (by decide)
    containing start code (actualControlBase q full) (actualAllocation q full) node tool before
    hpc ha hn ht hCB (rawCardData_cachedNode q full _ before data node) hr hord room.2.1 hend
  let clock := nodeReadClock full.length before.heap (actualControlBase q full) (mass q full) node.val tool.val
  refine ⟨result, ?_, result.prefix_address⟩
  constructor
  · intro count hc
    have h := result.prefix_safe count hc
    refine ⟨fun reg => metadata_le_wordLimit (h.1 reg), h.2.2.1, ?_⟩
    by_cases hlt : count < clock
    · obtain ⟨index, hi, hp, _access⟩ := h.2.2.2 hlt
      exact ⟨index, hi.le, hp⟩
    · have he : count = clock := by omega
      subst count
      exact ⟨start + 46, code.1, result.pc⟩
  · intro count hc
    obtain ⟨index, hi, hp, access⟩ := (result.prefix_safe count hc.le).2.2.2 hc
    exact ⟨index, hi, hp, access⟩


end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
