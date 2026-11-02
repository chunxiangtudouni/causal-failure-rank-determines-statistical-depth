module

public import PaperProofs.Structure.RawTreePreprocessingWordInterface
public import PaperProofs.Structure.RawCandidateWorkspaceInitWord
import Mathlib.Tactic.IntervalCases

/-! The actual raw program's checker, dispatcher, and initializer prefix.
The constructor after initialization is not assumed safe or correct here. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingStartWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open RawIncidenceScanSafety (NatAccessFits)
open RawTreePreprocessingNat (program)
open RawTreePreprocessingCostBounds (heapWords)
open RawTreePreprocessingWordInterface (SafePoint)

def constructor : List PackingOp := RawCandidateWorkspaceInit.program ++ RawTreePreprocessingNat.constructorTail

theorem program_eq_dispatcher : program = dispatcherProgram constructor := by
  rw [RawTreePreprocessingNat.program_eq_constructor]
  rfl

theorem program_eq_checker : program = checker ++ (dispatcherGate constructor.length ++ constructor) := by
  rw [program_eq_dispatcher, dispatcherProgram, List.append_assoc]

theorem terminal_pc : 5 * (checker.length + 2 + constructor.length) = 10445 := by
  rw [← dispatcherProgram_length, ← program_eq_dispatcher, RawTreePreprocessingCostBounds.program_length]

theorem heapWords_ge_eight (N q : Nat) : 8 ≤ heapWords N q := by
  unfold heapWords RawCandidateWorkspaceBounds.workspaceLimit
  omega

theorem natAccessFits_mono (rom : PhysicalROM) (small large : Nat) (hsize : small ≤ large)
    (state : NatState) (op : PackingOp) (ha : NatAccessFits rom small state op) :
    NatAccessFits rom large state op := by
  cases op with
  | base op =>
    cases op with
    | base instruction =>
      cases instruction <;> simp only [NatAccessFits, AccessFits] at ha ⊢
      all_goals first | exact ha | exact ha.trans_le hsize
    | subtract _ _ _ => trivial
  | arithmetic _ _ _ _ => trivial
  | jumpIfZero _ _ => trivial

theorem safePoint_of_decoded (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (index : Nat) (hi : index ≤ program.length) (hp : state.pc = 5 * index)
    (hr : RegistersFit (indexWidth 16 full.length q) state) (op : PackingOp)
    (hd : PackingOp.decode (natFetch program state.pc) = some op)
    (ha : NatAccessFits (rawIncidenceROM q full) (heapWords full.length q) state op) :
    SafePoint q full state := by
  refine ⟨hr, index, hi, hp, ?_⟩
  intro _
  simpa only [hd] using ha

theorem checker_active_safe (q : Nat) (full : List (Finset (Fin q))) (clock : Nat)
    (hactive : (natRun (rawIncidenceROM q full) checker clock natInitial).halted = false) :
    RawIncidenceScanSafety.SafePoint q full (natRun (rawIncidenceROM q full) checker clock natInitial) := by
  obtain ⟨steps, _hsteps, hsafe, hhalt⟩ := checker_has_safe_halt q full
  have hc : clock < steps := by
    by_contra hn
    have heq : clock = steps + (clock - steps) := by omega
    have hsame : natRun (rawIncidenceROM q full) checker clock natInitial =
        natRun (rawIncidenceROM q full) checker steps natInitial := by
      rw [heq, natRun_after_halt _ _ _ steps hhalt]
    rw [hsame, hhalt] at hactive
    cases hactive
  exact hsafe clock hc.le

theorem checker_body_safePoint (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : RawIncidenceScanSafety.SafePoint q full state) (hactive : state.halted = false)
    (index : Nat) (hi : index < checker.length) (hp : state.pc = 5 * index) :
    SafePoint q full state := by
  have hd : PackingOp.decode (natFetch checker state.pc) = some (checker[index]'hi) := by
    rw [hp, natFetch_body checker index hi, decode_encode]
  obtain ⟨_oldIndex, _oldHi, _oldPc, ha⟩ := hs.2.2
  have haccess := ha hactive
  rw [hd] at haccess
  apply safePoint_of_decoded q full state index ?_ hp (safePoint_registersFit q full state hs)
    (checker[index]'hi) ?_ (natAccessFits_mono _ 8 _ (heapWords_ge_eight _ _) state _ haccess)
  · rw [RawTreePreprocessingCostBounds.program_length]
    rw [checker_length] at hi
    omega
  · rw [hp, program_eq_checker, ProgramPrefix.natFetch_append_left checker _ index hi,
      natFetch_body checker index hi, decode_encode]

private theorem fits_update (bits : Nat) (state : NatState) (hr : RegistersFit bits state)
    (value : Nat) (hv : Fits bits value) :
    RegistersFit bits { state with register := Function.update state.register .index value } := by
  intro register
  by_cases heq : register = .index
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hr register

theorem gate_first (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 5 * checker.length) (hactive : state.halted = false) :
    natRun rom program 1 state =
      { state with
        register := Function.update state.register .index 10445
        pc := 5 * (checker.length + 1) } := by
  change natStep rom program state = _
  rw [program_eq_dispatcher, natStep_of_index rom (dispatcherProgram constructor) state checker.length
    (by rw [dispatcherProgram_length]; omega) hpc hactive, dispatcherProgram_first, terminal_pc]
  simp only [natExecuteOp, Op.execute, Instruction.execute]
  congr 1
  omega

theorem gate_zero_safePoint (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * checker.length) (hr : RegistersFit (indexWidth 16 full.length q) state) :
    SafePoint q full state := by
  apply safePoint_of_decoded q full state checker.length ?_ hpc hr
    (.base (.base (.constant .index 10445))) ?_ trivial
  · rw [RawTreePreprocessingCostBounds.program_length, checker_length]; omega
  · rw [hpc, program_eq_dispatcher, natFetch_body _ checker.length (by rw [dispatcherProgram_length]; omega),
      dispatcherProgram_first, terminal_pc, decode_encode]

theorem gate_one_safePoint (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * checker.length) (hactive : state.halted = false)
    (hr : RegistersFit (indexWidth 16 full.length q) state) :
    SafePoint q full (natRun (rawIncidenceROM q full) program 1 state) := by
  rw [gate_first _ state hpc hactive]
  let one : NatState := { state with
    register := Function.update state.register .index 10445
    pc := 5 * (checker.length + 1) }
  have hfit : RegistersFit (indexWidth 16 full.length q) one :=
    fits_update _ state hr 10445 (RawTreePreprocessingCodeBounds.constant_fits _ _ _ (by decide))
  change SafePoint q full one
  apply safePoint_of_decoded q full one (checker.length + 1) ?_ rfl hfit
    (.jumpIfZero .value .index) ?_ trivial
  · rw [RawTreePreprocessingCostBounds.program_length, checker_length]; omega
  · change PackingOp.decode (natFetch program (5 * (checker.length + 1))) = _
    rw [program_eq_dispatcher, natFetch_body _ (checker.length + 1) (by rw [dispatcherProgram_length]; omega),
      dispatcherProgram_second, decode_encode]

theorem gate_prefix (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * checker.length) (hactive : state.halted = false)
    (hr : RegistersFit (indexWidth 16 full.length q) state) :
    PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program state 2 := by
  intro count hc
  interval_cases count
  · exact gate_zero_safePoint q full state hpc hr
  · exact gate_one_safePoint q full state hpc hactive hr

theorem gate_after_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * checker.length) (hactive : state.halted = false)
    (hr : RegistersFit (indexWidth 16 full.length q) state) :
    RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) program 2 state) := by
  rw [program_eq_dispatcher, dispatcher_gate_run constructor _ state hpc hactive, terminal_pc]
  exact fits_update _ state hr 10445 (RawTreePreprocessingCodeBounds.constant_fits _ _ _ (by decide))

structure GateEntry (q : Nat) (full : List (Finset (Fin q))) (clock : Nat) : Prop where
  safe : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial clock
  fit : RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) program clock natInitial)
  active : (natRun (rawIncidenceROM q full) program clock natInitial).halted = false
  accepts : LaminarSchedule full →
    (natRun (rawIncidenceROM q full) program clock natInitial).pc = 5 * (checker.length + 2) ∧
    (natRun (rawIncidenceROM q full) program clock natInitial).register .value = 1
  rejects : ¬ LaminarSchedule full →
    (natRun (rawIncidenceROM q full) program clock natInitial).pc = 5 * program.length ∧
    (natRun (rawIncidenceROM q full) program clock natInitial).register .value = 0
  untouched : ∀ address, 8 ≤ address →
    (natRun (rawIncidenceROM q full) program clock natInitial).heap address = 0

/-- This actual raw-input prefix establishes its safety from the checker
invariants and the two executed gate instructions, without a safety premise. -/
theorem gate_entry (q : Nat) (full : List (Finset (Fin q))) :
    ∃ clock ≤ checkerSteps full.length q + 1, GateEntry q full clock := by
  obtain ⟨count, hcount, hactive, hpc, hflag, hcorrect, _hterminal, hbody, hprefix⟩ :=
    checker_before_first_halt q full
  have hsame (clock : Nat) (hc : clock ≤ count) :
      natRun (rawIncidenceROM q full) program clock natInitial =
        natRun (rawIncidenceROM q full) checker clock natInitial := by
    rw [program_eq_checker]
    exact hprefix _ clock hc
  let before := natRun (rawIncidenceROM q full) program count natInitial
  have hbpc : before.pc = 5 * checker.length := by
    dsimp only [before]; rw [hsame count le_rfl]; exact hpc
  have hbactive : before.halted = false := by
    dsimp only [before]; rw [hsame count le_rfl]; exact hactive
  have hfit : RegistersFit (indexWidth 16 full.length q) before := by
    dsimp only [before]; rw [hsame count le_rfl]
    exact safePoint_registersFit q full _ (checker_active_safe q full count hactive)
  have hchecked : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial count := by
    intro clock hc
    rw [hsame clock hc.le]
    obtain ⟨ha, _hbound, index, hi, hp⟩ := hbody clock hc
    exact checker_body_safePoint q full _ (checker_active_safe q full clock ha) ha index hi hp
  have hgate := gate_prefix q full before hbpc hbactive hfit
  have hafter : natRun (rawIncidenceROM q full) program (count + 2) natInitial =
      { before with
        register := Function.update before.register .index 10445
        pc := if before.register .value = 0 then 10445 else 5 * (checker.length + 2) } := by
    rw [natRun_add]
    change natRun (rawIncidenceROM q full) program 2 before = _
    have h := dispatcher_gate_run constructor (rawIncidenceROM q full) before hbpc hbactive
    rw [terminal_pc] at h
    exact (congrArg (fun code => natRun (rawIncidenceROM q full) code 2 before) program_eq_dispatcher).trans h
  refine ⟨count + 2, by omega, ?_⟩
  constructor
  · exact PrefixSafe.add _ _ _ _ count 2 hchecked hgate
  · rw [natRun_add]
    exact gate_after_fit q full before hbpc hbactive hfit
  · rw [hafter]
    exact hbactive
  · intro hl
    have hv : before.register .value = 1 := by
      dsimp only [before]; rw [hsame count le_rfl]; exact hcorrect.mpr hl
    rw [hafter]
    simp only [hv, Nat.one_ne_zero, ite_false, Function.update_of_ne (by decide : Register.value ≠ .index)]
    exact ⟨trivial, trivial⟩
  · intro hl
    have hv : before.register .value = 0 := by
      have hn : before.register .value ≠ 1 := by
        intro hone
        apply hl
        apply hcorrect.mp
        dsimp only [before] at hone
        rwa [hsame count le_rfl] at hone
      have hb : before.register .value ≤ 1 := by
        dsimp only [before]; rw [hsame count le_rfl]; exact hflag
      omega
    rw [hafter]
    simp only [hv, ite_true, Function.update_of_ne (by decide : Register.value ≠ .index)]
    exact ⟨by rw [RawTreePreprocessingCostBounds.program_length], trivial⟩
  · intro address ha
    rw [hafter]
    change before.heap address = 0
    dsimp only [before]
    rw [hsame count le_rfl]
    exact checker_active_heap_frame q full count hactive address ha

def initFront : List PackingOp := checker ++ dispatcherGate constructor.length

theorem initFront_length : initFront.length = 128 := by
  simp only [initFront, List.length_append, checker_length, dispatcherGate_length]

theorem init_program : initFront ++ RawCandidateWorkspaceInit.program ++
    RawTreePreprocessingNat.constructorTail = program := by
  rw [program_eq_dispatcher]
  simp only [initFront, constructor, dispatcherProgram, List.append_assoc]

theorem init_slice :
    128 + 16 ≤ program.length ∧
      ∀ position < 16, program.getD (128 + position) RawCandidateWorkspaceInitWord.paddingOp =
        RawCandidateWorkspaceInitWord.body.getD position RawCandidateWorkspaceInitWord.paddingOp := by
  have h := RawCandidateWorkspaceInit.append_slice initFront RawTreePreprocessingNat.constructorTail
  rw [init_program, initFront_length] at h
  exact h

theorem init_prefix (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * 128) (hactive : state.halted = false)
    (hr : RegistersFit (indexWidth 16 full.length q) state) :
    PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program state 16 := by
  intro count hc
  have hend : Fits (indexWidth 16 full.length q) (5 * (128 + 16)) :=
    RawTreePreprocessingCodeBounds.constant_fits full.length q _ (by decide)
  have hs := RawCandidateWorkspaceInitWord.natRun_prefix_safe q full program 128
    init_slice.1 init_slice.2 state hpc hactive hr hend count hc.le
  have hp := RawCandidateWorkspaceInitWord.natRun_prefix_pc q full program 128
    init_slice.1 init_slice.2 state hpc hactive count hc.le
  apply safePoint_of_decoded q full _ (128 + count) (by have h := init_slice.1; omega) hp hs.1
    (RawCandidateWorkspaceInitWord.body.getD count RawCandidateWorkspaceInitWord.paddingOp)
  · rw [hp, natFetch_body program (128 + count) (by have h := init_slice.1; omega), decode_encode]
    apply congrArg some
    have h := init_slice.2 count hc
    rw [List.getD_eq_getElem _ _ (by have h := init_slice.1; omega)] at h
    exact h
  · change NatAccessFits (rawIncidenceROM q full) (RawCandidateWorkspaceBounds.workspaceLimit full.length q) _ _
    rw [RawCandidateWorkspaceInitWord.natRun_prefix_eq q full program 128
      init_slice.1 init_slice.2 state hpc hactive count hc.le]
    exact RawCandidateWorkspaceInitWord.runOps_prefix_accessFits q full state count hc

structure StartReady (q : Nat) (full : List (Finset (Fin q))) (result : NatState) : Prop where
  fit : RegistersFit (indexWidth 16 full.length q) result
  active : result.halted = false
  pc : result.pc = 5 * 144
  accepted : result.register .value = 1
  base : result.heap 8 = RawCandidateWorkspaceInit.workspaceBase full.length q
  count : result.heap (RawCandidateWorkspaceInit.workspaceBase full.length q) =
    RawCandidateWorkspaceInit.candidateCount full.length q
  untouched : ∀ address, 8 ≤ address → address ≠ 8 →
    address ≠ RawCandidateWorkspaceInit.workspaceBase full.length q → result.heap address = 0

theorem prefix_word_eq (q : Nat) (full : List (Finset (Fin q))) (steps : Nat)
    (hs : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial steps) :
    packingRun (rawIncidenceROM q full) program steps
      (packingInitial (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0)) =
        (natRun (rawIncidenceROM q full) program steps natInitial).toWord (indexWidth 16 full.length q) := by
  change packingRun _ _ steps (natInitial.toWord _) = _
  apply natRun_toWord _ _ _ steps (RawTreePreprocessingCostBounds.code_wordsFit full.length q)
  intro count hc
  exact ⟨(hs count hc).1, RawTreePreprocessingWordInterface.safePoint_pcFit q full _ (hs count hc)⟩

/-- The raw checker and gate establish all initializer calling conditions.
The same physical program now reaches the candidate-loop entry safely.
Nothing about the candidate loop or later phases is assumed. -/
theorem initialized_entry (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full) :
    ∃ clock ≤ checkerSteps full.length q + 17,
      PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial clock ∧
      StartReady q full (natRun (rawIncidenceROM q full) program clock natInitial) ∧
      packingRun (rawIncidenceROM q full) program clock
        (packingInitial (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0)) =
          (natRun (rawIncidenceROM q full) program clock natInitial).toWord (indexWidth 16 full.length q) := by
  obtain ⟨first, hfirst, entry⟩ := gate_entry q full
  let before := natRun (rawIncidenceROM q full) program first natInitial
  have hpc : before.pc = 5 * 128 := by
    have h := (entry.accepts hl).1
    simpa only [checker_length] using h
  have hv : before.register .value = 1 := (entry.accepts hl).2
  have hinit := RawCandidateWorkspaceInit.initialize_workspace q full program 128
    init_slice.1 init_slice.2 before hpc entry.active
  have hs := RawCandidateWorkspaceInitWord.natRun_prefix_safe q full program 128
    init_slice.1 init_slice.2 before hpc entry.active entry.fit
      (RawTreePreprocessingCodeBounds.constant_fits full.length q _ (by decide)) 16 le_rfl
  have hstart : StartReady q full (natRun (rawIncidenceROM q full) program 16 before) := by
    refine ⟨hs.1, hinit.active, hinit.pc, hinit.value.trans hv, hinit.base_cell, hinit.count_cell, ?_⟩
    intro address ha h8 hB
    rw [hinit.heap_frame address h8 hB]
    exact entry.untouched address ha
  have hsafe : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial (first + 16) :=
    PrefixSafe.add _ _ _ _ first 16 entry.safe (init_prefix q full before hpc entry.active entry.fit)
  refine ⟨first + 16, by omega, hsafe, ?_, prefix_word_eq q full (first + 16) hsafe⟩
  rwa [natRun_add]

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingStartWord
