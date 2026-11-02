module

public import Structure.PA06_A19Prepare_CompactRetention030Loop
public import Structure.PA06_A19Prepare_CompactRetention030InitBounds
public import PaperProofs.Structure.PA17_UniformGenerator_035l

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! SAME raw/controllerInput Word run: checker, true dispatcher gate,
actual006 compact initialization and the original398-op retention loop.
No halted-state restart, supplied tables, fit16 caller restriction or
complete hSafe premise is used. Sort and parent phases are separate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Entry

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareCompactRetention030InitBounds (checker_active_point checker_active_registersFit init_prefix_registersFit)

abbrev program := PA06A19PrepareCompactCandidates007.Metadata.program
abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

def constructor (tail : List PackingOp) : List PackingOp :=
  PA06A19PrepareCompactInit006.initProgram ++
    (RawCandidateRetentionRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.retentionStart ++ tail)

def initFront (tail : List PackingOp) : List PackingOp := checker ++ dispatcherGate (constructor tail).length

theorem program_dispatcher (tail : List PackingOp) : program tail = dispatcherProgram (constructor tail) := rfl

theorem initFront_length (tail : List PackingOp) : (initFront tail).length = checker.length + 2 := by
  simp only [initFront, List.length_append, dispatcherGate_length]

theorem program_init_slice (tail : List PackingOp) :
    checker.length + 2 + 16 ≤ (program tail).length ∧
      ∀ position < 16, (program tail).getD (checker.length + 2 + position) PA06A19PrepareCompactInit006.paddingOp =
        PA06A19PrepareCompactInit006.initProgram.getD position PA06A19PrepareCompactInit006.paddingOp := by
  have same : initFront tail ++ PA06A19PrepareCompactInit006.initProgram ++
      (RawCandidateRetentionRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.retentionStart ++ tail) = program tail := by
    simp only [initFront, program_dispatcher, dispatcherProgram, constructor, List.append_assoc]
  have slice := PA06A19PrepareCompactInit006.append_slice (initFront tail)
    (RawCandidateRetentionRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.retentionStart ++ tail)
  rw [same, initFront_length] at slice
  exact slice

def Point (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp) (state : NatState) : Prop :=
  RegistersFit (indexWidth 32 full.length q) state ∧ Fits (indexWidth 32 full.length q) state.pc ∧
    state.halted = false ∧ ∃ (index : Nat) (hi : index < (program tail).length),
      state.pc = 5 * index ∧ NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state (program tail)[index]

private theorem access_mono (rom : PhysicalROM) (small large : Nat) (state : NatState) (op : PackingOp)
    (hroom : small ≤ large) (access : NatAccessFits rom small state op) : NatAccessFits rom large state op := by
  cases op with
  | base op =>
    cases op with
    | subtract target left right => trivial
    | base instruction =>
      cases instruction <;> simp only [NatAccessFits, AccessFits] at access ⊢
      all_goals first | exact access | exact access.trans_le hroom
  | arithmetic operation target left right => trivial
  | jumpIfZero condition target => trivial

private theorem gate_prefix_run (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (state : NatState) (hpc : state.pc = 5 * checker.length) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 2) :
    natRun (rawIncidenceROM q full) (program tail) count state =
      runOps (rawIncidenceROM q full) ((dispatcherGate (constructor tail).length).take count) state := by
  have run := PA17UniformGenerator035l.branch_segment_prefix (rawIncidenceROM q full) checker
    [.base (.base (.constant .index (5 * (checker.length + 2 + (constructor tail).length))))]
    (constructor tail) (.jumpIfZero .value .index) (by simp [NoJump]) state hpc ha count hc
  simpa only [program_dispatcher, dispatcherProgram, dispatcherGate,
    List.cons_append, List.nil_append] using run

private theorem gate_registersFit (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (state : NatState) (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (count : Nat) (hc : count ≤ 2) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((dispatcherGate (constructor tail).length).take count) state) := by
  have exitFit : Fits (indexWidth 32 full.length q) (5 * (checker.length + 2 + (constructor tail).length)) := by
    simpa only [program_dispatcher, dispatcherProgram_length] using hend
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [dispatcherGate, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hr _ | exact exitFit

private theorem checker_point (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp) (count : Nat)
    (active : (natRun (rawIncidenceROM q full) checker count natInitial).halted = false)
    (index : Nat) (hi : index < checker.length)
    (pc : (natRun (rawIncidenceROM q full) checker count natInitial).pc = 5 * index) :
    Point q full tail (natRun (rawIncidenceROM q full) checker count natInitial) := by
  let state := natRun (rawIncidenceROM q full) checker count natInitial
  have point := checker_active_point q full count active
  have regs := checker_active_registersFit q full count active
  have fits := PA06A19PrepareCompactWord008.fits_width32_of_width16 full.length q _
    (safePoint_pcFit q full state point)
  obtain ⟨_oldIndex, _bound, _oldPC, guard⟩ := point.2.2
  have access : NatAccessFits (rawIncidenceROM q full) 8 state checker[index] := by
    have guarded := guard active
    rw [pc, natFetch_body checker index hi, decode_encode] at guarded
    exact guarded
  have hindex : index < (program tail).length := by
    rw [program_dispatcher, dispatcherProgram_length]
    omega
  refine ⟨regs, fits, active, index, hindex, pc, ?_⟩
  have wide := access_mono (rawIncidenceROM q full) 8 (linearLimit full.length q) state checker[index]
    (by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega) access
  have sameOp : (program tail).getD index PA06A19PrepareCompactInit006.paddingOp = checker.getD index PA06A19PrepareCompactInit006.paddingOp := by
    rw [program_dispatcher, dispatcherProgram,
      List.getD_append (checker ++ dispatcherGate (constructor tail).length) (constructor tail) PA06A19PrepareCompactInit006.paddingOp index
        (by simp only [List.length_append]; omega),
      List.getD_append checker (dispatcherGate (constructor tail).length) PA06A19PrepareCompactInit006.paddingOp index hi]
  rw [List.getD_eq_getElem _ PA06A19PrepareCompactInit006.paddingOp hindex, List.getD_eq_getElem _ PA06A19PrepareCompactInit006.paddingOp hi] at sameOp
  rw [sameOp]
  exact wide

private theorem gate_point (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (state : NatState) (hpc : state.pc = 5 * checker.length) (ha : state.halted = false)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (count : Nat) (hc : count < 2) :
    Point q full tail (natRun (rawIncidenceROM q full) (program tail) count state) := by
  rw [gate_prefix_run q full tail state hpc ha count hc.le]
  have regs := gate_registersFit q full tail state hr hend count hc.le
  have active := (runOps_halted (rawIncidenceROM q full) ((dispatcherGate (constructor tail).length).take count) state).trans ha
  have pc : (runOps (rawIncidenceROM q full) ((dispatcherGate (constructor tail).length).take count) state).pc =
      5 * (checker.length + count) := by
    interval_cases count <;> simp [dispatcherGate, runOps, natExecuteOp, Op.execute, Instruction.execute, hpc]
    omega
  have hindex : checker.length + count < (program tail).length := by
    rw [program_dispatcher, dispatcherProgram_length]
    omega
  refine ⟨regs, ?_, active, checker.length + count, hindex, pc, ?_⟩
  · rw [pc]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 5 hindex.le) hend
  · have sameOp : (program tail)[checker.length + count]'hindex =
        (dispatcherGate (constructor tail).length).getD count PA06A19PrepareCompactInit006.paddingOp := by
      rw [← List.getD_eq_getElem _ PA06A19PrepareCompactInit006.paddingOp hindex, program_dispatcher, dispatcherProgram,
        List.getD_append (checker ++ dispatcherGate (constructor tail).length) (constructor tail)
          PA06A19PrepareCompactInit006.paddingOp (checker.length + count)
          (by simp only [List.length_append, dispatcherGate_length]; omega),
        List.getD_append_right checker (dispatcherGate (constructor tail).length) PA06A19PrepareCompactInit006.paddingOp
          (checker.length + count) (by omega), Nat.add_sub_cancel_left]
    rw [sameOp]
    interval_cases count <;> trivial

private theorem init_point (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (state : NatState) (hpc : state.pc = 5 * (checker.length + 2)) (ha : state.halted = false)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (count : Nat) (hc : count < 16) :
    Point q full tail (natRun (rawIncidenceROM q full) (program tail) count state) := by
  have slice := program_init_slice tail
  have run := PA06A19PrepareCompactInit006.natRun_prefix_eq q full (program tail) (checker.length + 2) slice.1 slice.2
    state hpc ha count hc.le
  have pc := PA06A19PrepareCompactInit006.natRun_prefix_pc q full (program tail) (checker.length + 2) slice.1 slice.2
    state hpc ha count hc.le
  have active : (natRun (rawIncidenceROM q full) (program tail) count state).halted = false := by
    rw [run, runOps_halted, ha]
  have hindex : checker.length + 2 + count < (program tail).length := by omega
  refine ⟨?_, ?_, active, checker.length + 2 + count, hindex, pc, ?_⟩
  · rw [run]
    exact init_prefix_registersFit q full state hr count hc.le
  · rw [pc]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 5 hindex.le) hend
  · have access := PA06A19PrepareCompactInit006.runOps_prefix_accessFits q full state count hc
    have wide := access_mono (rawIncidenceROM q full) 17 (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) (PA06A19PrepareCompactInit006.initProgram.take count) state)
      (PA06A19PrepareCompactInit006.initProgram.getD count PA06A19PrepareCompactInit006.paddingOp)
      (by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega) access
    rw [run]
    have op := slice.2 count hc
    rw [List.getD_eq_getElem _ _ hindex] at op
    rw [op]
    exact wide

structure Front (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp) (clock : Nat) : Prop where
  before_points : ∀ count < clock, Point q full tail (natRun (rawIncidenceROM q full) (program tail) count natInitial)
  registers : RegistersFit (indexWidth 32 full.length q)
    (natRun (rawIncidenceROM q full) (program tail) clock natInitial)
  pc : (natRun (rawIncidenceROM q full) (program tail) clock natInitial).pc =
    5 * PA06A19PrepareCompactCandidates007.Metadata.retentionStart
  active : (natRun (rawIncidenceROM q full) (program tail) clock natInitial).halted = false
  pointer : (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap 8 = 16
  header : (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap 16 = full.length + q + 1
  zero : ∀ address, 8 ≤ address → address ≠ 8 → address ≠ 16 →
    (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap address = 0

/-- Every prefix of the actual checker/gate/init front, and its real
materialized compact workspace. The checker boundary is before HALT. -/
theorem initialized_front (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length)) :
    ∃ clock ≤ checkerSteps full.length q + 17, Front q full tail clock := by
  obtain ⟨checked, checkedBound, checkedActive, checkedPC, _flagBound, accepted, _halt, body, preserved⟩ :=
    checker_before_first_halt q full
  let boundary := natRun (rawIncidenceROM q full) checker checked natInitial
  have boundaryValue : boundary.register .value = 1 := accepted.mpr hlaminar
  have boundaryRegs := checker_active_registersFit q full checked checkedActive
  have prefixRun (count : Nat) (hc : count ≤ checked) :
      natRun (rawIncidenceROM q full) (program tail) count natInitial =
        natRun (rawIncidenceROM q full) checker count natInitial := by
    simpa only [program_dispatcher, dispatcherProgram, List.append_assoc] using
      preserved (dispatcherGate (constructor tail).length ++ constructor tail) count hc
  let entered := natRun (rawIncidenceROM q full) (program tail) (checked + 2) natInitial
  have enterRun : entered = natRun (rawIncidenceROM q full) (program tail) 2 boundary := by
    dsimp only [entered]
    rw [natRun_add, prefixRun checked le_rfl]
  have gate := dispatcher_gate_run (constructor tail) (rawIncidenceROM q full) boundary checkedPC checkedActive
  have enterEffect : entered = { boundary with
      register := Function.update boundary.register .index (5 * (checker.length + 2 + (constructor tail).length))
      pc := 5 * (checker.length + 2) } := by
    rw [enterRun]
    change natRun (rawIncidenceROM q full) (dispatcherProgram (constructor tail)) 2 boundary = _
    rw [gate]
    simp only [boundaryValue, Nat.one_ne_zero, ite_false]
  have enterPC : entered.pc = 5 * (checker.length + 2) := by rw [enterEffect]
  have enterActive : entered.halted = false := by rw [enterEffect]; exact checkedActive
  have enterHeap : entered.heap = boundary.heap := by rw [enterEffect]
  have enterRegs : RegistersFit (indexWidth 32 full.length q) entered := by
    rw [enterRun, gate_prefix_run q full tail boundary checkedPC checkedActive 2 le_rfl]
    exact gate_registersFit q full tail boundary boundaryRegs hend 2 le_rfl
  let clock := (checked + 2) + 16
  let prepared := natRun (rawIncidenceROM q full) (program tail) clock natInitial
  have prepareRun : natRun (rawIncidenceROM q full) (program tail) 16 entered = prepared :=
    (natRun_add _ _ _ _ _).symm
  have slice := program_init_slice tail
  have initialized := PA06A19PrepareCompactInit006.initialize_workspace q full (program tail) (checker.length + 2)
    slice.1 slice.2 entered enterPC enterActive
  rw [prepareRun] at initialized
  have preparedRegs : RegistersFit (indexWidth 32 full.length q) prepared := by
    rw [← prepareRun, PA06A19PrepareCompactInit006.natRun_prefix_eq q full (program tail) (checker.length + 2)
      slice.1 slice.2 entered enterPC enterActive 16 le_rfl]
    exact init_prefix_registersFit q full entered enterRegs 16 le_rfl
  refine ⟨clock, by dsimp only [clock]; omega, ?_⟩
  refine ⟨?_, preparedRegs, ?_, initialized.active, initialized.base_cell, initialized.count_cell, ?_⟩
  · intro count hc
    by_cases checking : count < checked
    · rw [prefixRun count checking.le]
      obtain ⟨active, _pcBound, index, hi, pc⟩ := body count checking
      exact checker_point q full tail count active index hi pc
    · by_cases gating : count < checked + 2
      · have clockEq : count = checked + (count - checked) := by omega
        have run : natRun (rawIncidenceROM q full) (program tail) count natInitial =
            natRun (rawIncidenceROM q full) (program tail) (count - checked) boundary := by
          conv_lhs => rw [clockEq, natRun_add, prefixRun checked le_rfl]
        rw [run]
        exact gate_point q full tail boundary checkedPC checkedActive boundaryRegs hend (count - checked) (by omega)
      · have clockEq : count = (checked + 2) + (count - (checked + 2)) := by omega
        have run : natRun (rawIncidenceROM q full) (program tail) count natInitial =
            natRun (rawIncidenceROM q full) (program tail) (count - (checked + 2)) entered := by
          conv_lhs => rw [clockEq, natRun_add]
        rw [run]
        exact init_point q full tail entered enterPC enterActive enterRegs hend (count - (checked + 2)) (by
          dsimp only [clock] at hc
          omega)
  · have pc := initialized.pc
    change prepared.pc = _ at pc
    change prepared.pc = _
    unfold PA06A19PrepareCompactCandidates007.Metadata.retentionStart
    omega
  · intro address haddress h8 h16
    rw [initialized.heap_frame address h8 h16, enterHeap]
    exact checker_active_heap_frame q full checked checkedActive address haddress

def Retained (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop :=
  state.halted = false ∧ state.pc.toNat = 5 * (PA06A19PrepareCompactCandidates007.Metadata.retentionStart + 398) ∧
    (state.heap (BitVec.ofNat _ 8)).toNat = 16 ∧
    (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1 ∧
    (∀ index < full.length + q + 1,
      (state.heap (BitVec.ofNat _ (RawCandidateRetentionRAM.cardAddress 16 index))).toNat =
        ((RawCandidateOrder.candidateSupports q full).getD index ∅).card ∧
      (state.heap (BitVec.ofNat _ (RawCandidateRetentionRAM.keepAddress 16 (full.length + q + 1) index))).toNat =
        bit (RawCandidateOrder.keepCandidate q full index)) ∧
    ∀ point, 16 + 4 + 2 * (full.length + q + 1) ≤ point.toNat → state.heap point = 0

private theorem input_prefix (q : Nat) (full : List (Finset (Fin q))) (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

/-- Complete real Word front through retained card/keep tables. Every
prefix belongs to ONE run from the original initial heap. No caller
initialization, hSafe, oldFit16 or supplied retained data remains. -/
theorem retained_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (initialUsed : Finset (Fin q)) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (program tail))) :
    ∃ steps ≤ checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q,
      let bits := indexWidth 32 full.length q
      let runtime := CompactControllerClaims.controllerInput q full initialUsed
      let initial := natInitial.toWord bits
      Retained q full (packingRun runtime (program tail) steps initial) ∧
        (∀ count ≤ steps, packingRun runtime (program tail) count initial =
          (natRun (rawIncidenceROM q full) (program tail) count natInitial).toWord bits) ∧
        ∀ count < steps,
          let actual := packingRun runtime (program tail) count initial
          actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) actual) = some op ∧
              packingAccessFits runtime (linearLimit full.length q) actual op := by
  let start := PA06A19PrepareCompactCandidates007.Metadata.retentionStart
  let duration := RawCandidateRetentionRAM.totalSteps full.length q
  let bits := indexWidth 32 full.length q
  let runtime := CompactControllerClaims.controllerInput q full initialUsed
  obtain ⟨first, bound, front⟩ := initialized_front q full tail hlaminar hend
  let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
  have slice : start + 398 ≤ (program tail).length ∧
      ∀ position < 398, (program tail).getD (start + position) RawCandidateRetentionRAM.paddingOp =
        (RawCandidateRetentionRAM.programAt start).getD position RawCandidateRetentionRAM.paddingOp := by
    have h := RawCandidateRetentionRAM.append_slice (PA06A19PrepareCompactCandidates007.Metadata.front tail) tail
    rw [PA06A19PrepareCompactCandidates007.Metadata.program_eq tail] at h
    simpa only [PA06A19PrepareCompactCandidates007.Metadata.front_length] using h
  have retEndFit : Fits bits (5 * (start + 398)) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 5 slice.1) hend
  have safe := PA06A19PrepareCompactRetention030Loop.retention_nat_safe q full (program tail) start slice.1 slice.2
    before front.pointer front.header front.pc front.active front.registers retEndFit
  have native := PA06A19PrepareCompactRetention030Loop.retention_native_output q full (program tail) start slice.1 slice.2
    before front.pointer front.header front.pc front.active
  have finalRun : natRun (rawIncidenceROM q full) (program tail) (first + duration) natInitial =
      natRun (rawIncidenceROM q full) (program tail) duration before := natRun_add _ _ _ _ _
  have allPoints (count : Nat) (hc : count < first + duration) :
      Point q full tail (natRun (rawIncidenceROM q full) (program tail) count natInitial) := by
    by_cases early : count < first
    · exact front.before_points count early
    · have after : count - first < duration := by omega
      have point := safe.1 (count - first) after
      have pcFit := PA06A19PrepareCompactRetention030Parts.point_pcFits point retEndFit
      obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
      have indexBound : start + offset < (program tail).length := by omega
      have actualDecode : PackingOp.decode (natFetch (program tail)
          (natRun (rawIncidenceROM q full) (program tail) (count - first) before).pc) =
          some ((program tail)[start + offset]'indexBound) := by
        rw [pc, natFetch_body (program tail) (start + offset) indexBound, decode_encode]
      have opEq : op = (program tail)[start + offset]'indexBound := Option.some.inj (decoded.symm.trans actualDecode)
      have run : natRun (rawIncidenceROM q full) (program tail) count natInitial =
          natRun (rawIncidenceROM q full) (program tail) (count - first) before := by
        conv_lhs => rw [show count = first + (count - first) by omega, natRun_add]
      rw [run]
      refine ⟨registers, pcFit, active, start + offset, indexBound, pc, ?_⟩
      simpa only [opEq] using access
  have runEq (count : Nat) (hc : count ≤ first + duration) :
      natRun runtime (program tail) count natInitial = natRun (rawIncidenceROM q full) (program tail) count natInitial := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed) (linearLimit full.length q)
    intro clock hclock _active op decoded
    obtain ⟨_registers, _pcFit, _active, index, hi, pc, access⟩ := allPoints clock (by omega)
    have actualDecode : PackingOp.decode (natFetch (program tail)
        (natRun (rawIncidenceROM q full) (program tail) clock natInitial).pc) = some ((program tail)[index]) := by
      rw [pc, natFetch_body (program tail) index hi, decode_encode]
    have opEq : op = (program tail)[index] := Option.some.inj (decoded.symm.trans actualDecode)
    subst op
    exact access
  have word (count : Nat) (hc : count ≤ first + duration) :
      packingRun runtime (program tail) count (natInitial.toWord bits) =
        (natRun (rawIncidenceROM q full) (program tail) count natInitial).toWord bits := by
    have h := natRun_toWord runtime (program tail) natInitial count hwords (by
      intro k hk
      rw [runEq k (by omega)]
      have point := allPoints k (by omega)
      exact ⟨point.1, point.2.1⟩)
    exact h.trans (congrArg (NatState.toWord bits) (runEq count hc))
  have heapWord (address value : Nat) (ha : Fits bits address) (hv : Fits bits value)
      (heq : (natRun (rawIncidenceROM q full) (program tail) (first + duration) natInitial).heap address = value) :
      (((natRun (rawIncidenceROM q full) (program tail) (first + duration) natInitial).toWord bits).heap
        (BitVec.ofNat bits address)).toNat = value := by
    change (BitVec.ofNat bits ((natRun (rawIncidenceROM q full) (program tail) (first + duration) natInitial).heap
      (BitVec.ofNat bits address).toNat)).toNat = value
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, heq, Nat.mod_eq_of_lt hv]
  have addressFits (address : Nat) (haddress : address ≤ linearLimit full.length q) : Fits bits address :=
    haddress.trans_lt (PA06A19PrepareCompactArrays018.linearLimit_fits full.length q)
  have small (value : Nat) (hvalue : value ≤ 16) : Fits bits value :=
    PA06A19PrepareCompactMacros014.small_constant_fits full.length q value hvalue
  have countFit : Fits bits (full.length + q + 1) :=
    PA06A19PrepareCompactArrays018.value_le_count_fits full.length q _ le_rfl
  dsimp only at native
  rw [← finalRun] at native
  refine ⟨first + duration, by omega, ?_⟩
  dsimp only
  refine ⟨?_, word, ?_⟩
  · rw [word _ le_rfl]
    refine ⟨native.2.2.2.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
    · change (BitVec.ofNat bits _).toNat = _
      rw [BitVec.toNat_ofNat, native.2.2.2.2.2.1, Nat.mod_eq_of_lt retEndFit]
    · exact heapWord 8 16 (small 8 (by decide)) (small 16 le_rfl) native.1
    · exact heapWord 16 (full.length + q + 1) (small 16 le_rfl) countFit native.2.1
    · intro index hi
      have cardFit : Fits bits (((RawCandidateOrder.candidateSupports q full).getD index ∅).card) := by
        have bound : ((RawCandidateOrder.candidateSupports q full).getD index ∅).card ≤ q := by
          simpa only [Fintype.card_fin] using Finset.card_le_univ ((RawCandidateOrder.candidateSupports q full).getD index ∅)
        exact (by omega : ((RawCandidateOrder.candidateSupports q full).getD index ∅).card ≤ full.length + q + 1).trans_lt countFit
      have bitFit : Fits bits (bit (RawCandidateOrder.keepCandidate q full index)) := by
        have bound : bit (RawCandidateOrder.keepCandidate q full index) ≤ 1 := by
          cases RawCandidateOrder.keepCandidate q full index <;> decide
        exact bound.trans_lt (small 1 (by decide))
      exact ⟨heapWord _ _ (addressFits _ (by
        unfold RawCandidateRetentionRAM.cardAddress linearLimit PA06A19PrepareCompactWord008.linearLimit
        omega)) cardFit ((native.2.2.2.1 index hi).1),
        heapWord _ _ (addressFits _ (by
          unfold RawCandidateRetentionRAM.keepAddress linearLimit PA06A19PrepareCompactWord008.linearLimit
          omega)) bitFit ((native.2.2.2.1 index hi).2)⟩
    · intro point above
      change BitVec.ofNat bits ((natRun (rawIncidenceROM q full) (program tail) (first + duration) natInitial).heap point.toNat) = 0
      have outside : RawCandidateRetentionRAM.OutsideWorkspace 16 (full.length + q + 1) point.toNat :=
        ⟨by omega, by omega, by omega, by omega, Or.inr above⟩
      have zero : (natRun (rawIncidenceROM q full) (program tail) (first + duration) natInitial).heap point.toNat = 0 :=
        (native.2.2.2.2.1 point.toNat outside).trans (front.zero point.toNat (by omega) (by omega) (by omega))
      exact congrArg (BitVec.ofNat bits) zero
  · intro count hc
    have point := allPoints count hc
    obtain ⟨registers, pcFit, active, index, hi, pc, access⟩ := point
    rw [word count hc.le]
    have wordPC : ((natRun (rawIncidenceROM q full) (program tail) count natInitial).toWord bits).pc.toNat = 5 * index := by
      change (BitVec.ofNat bits _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pc]
    refine ⟨active, ?_, (program tail)[index], ?_, ?_⟩
    · rw [wordPC, packingCode_length]
      omega
    · change PackingOp.decode (physicalFetch bits (packingCode (program tail))
        ((natRun (rawIncidenceROM q full) (program tail) count natInitial).toWord bits).pc.toNat) = _
      rw [wordPC, physicalFetch_eq _ _ _ hwords]
      change PackingOp.decode (natFetch (program tail) (5 * index)) = _
      rw [natFetch_body (program tail) index hi, decode_encode]
    · apply physical_access_of_nat runtime (linearLimit full.length q) _ _ registers
      cases hop : (program tail)[index] with
      | base instruction =>
        exact PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed) (linearLimit full.length q) _ instruction
          (by simpa only [hop, NatAccessFits] using access)
      | arithmetic operation target left right => trivial
      | jumpIfZero condition target => trivial

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Entry

