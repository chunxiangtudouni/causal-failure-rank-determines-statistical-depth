module

public import PaperProofs.Structure.RawIncidenceOuterSafety
public import PaperProofs.Structure.RawIncidenceScanRunSafety
public import PaperProofs.Structure.RawIncidenceMacroRunSafety
public import PaperProofs.Structure.RawIncidenceInitSafety
public import PaperProofs.Structure.RawIncidenceDecisionSafety

/-! Closed physical laminarity-checking phase on the original raw ROM.
Local instruction bounds are composed along the actual two outer loops.
The serialized inclusion tree remains outside this checking phase. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceScanSafety RawIncidenceMacroSafety

abbrev SafeRun (q : Nat) (full : List (Finset (Fin q))) (state : NatState) (steps : Nat) : Prop :=
  ThroughSafe (SafePoint q full) (rawIncidenceROM q full) checker state steps

theorem SafeRun.add (q : Nat) (full : List (Finset (Fin q))) (state : NatState) (left right : Nat)
    (hl : SafeRun q full state left)
    (hr : SafeRun q full (natRun (rawIncidenceROM q full) checker left state) right) :
    SafeRun q full state (left + right) :=
  ThroughSafe.add _ _ _ _ _ _ hl hr

def SafeRowExit {q : Nat} (full : List (Finset (Fin q))) (i : Nat) (state : NatState) (steps : Nat) : Prop :=
  SafeRun q full state steps ∧
    ((natRun (rawIncidenceROM q full) checker steps state).halted = true ∨
      Ready full.length q i full.length 585 (natRun (rawIncidenceROM q full) checker steps state))

theorem checker_safe_row (q : Nat) (full : List (Finset (Fin q))) (i : Nat)
    (hi : i < full.length) (j : Nat) (hj : j ≤ full.length) (state : NatState)
    (ready : Ready full.length q i j 100 state) (hr : RegistersBound full.length q state) :
    ∃ steps : Nat, steps ≤ (full.length - j) * (53 * q + 47) + 7 ∧ SafeRowExit full i state steps := by
  have solve : ∀ remaining : Nat, ∀ j : Nat, full.length - j = remaining → j ≤ full.length →
      ∀ state : NatState, Ready full.length q i j 100 state → RegistersBound full.length q state →
        ∃ steps : Nat, steps ≤ remaining * (53 * q + 47) + 7 ∧ SafeRowExit full i state steps := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro j hsize hj state ready hr
      let rom := rawIncidenceROM q full
      by_cases hlast : j = full.length
      · subst j
        have hz : remaining = 0 := by omega
        refine ⟨7, by rw [hz]; simp, checker_pair_terminal_safe q full i state ready hi hr,
          Or.inr (checker_pair_terminal rom ready)⟩
      · have hjlive : j < full.length := by omega
        let base := 53 * q + 26
        let scanning := natRun rom checker 19 state
        have hsetup := checker_pair_setup rom ready hjlive
        have setupSafe := checker_pair_setup_safe q full i j state ready hi hjlive hr
        have scanningRegs : RegistersBound full.length q scanning := (setupSafe 19 le_rfl).1
        have scanSafe := checker_pairScan_safe q full ⟨i, hi⟩ ⟨j, hjlive⟩ scanning
          hsetup.1.pc hsetup.1.active hsetup.1.dimension hsetup.1.tools hsetup.1.left hsetup.1.right
          hsetup.2.1 hsetup.2.2.1 hsetup.2.2.2.1 hsetup.2.2.2.2 scanningRegs
        have baseSafe : SafeRun q full state base := by
          have h := SafeRun.add q full state 19 (53 * q + 7) setupSafe scanSafe
          simpa only [show 19 + (53 * q + 7) = base from by dsimp [base]; omega] using h
        let scanned := natRun rom checker base state
        have hscan := checker_pair_scan full i j hi hjlive state ready
        have hcounts := checker_pair_scan_bounds full i j hi hjlive state ready
        have scannedRegs : RegistersBound full.length q scanned := (baseSafe base le_rfl).1
        obtain ⟨decision, hdecisionBound, decisionSafe, hdecision⟩ :=
          checker_pair_decision_safe q full i j scanned hscan.1 hi hjlive
            hcounts.1 hcounts.2.1 hcounts.2.2 scannedRegs
        rcases hdecision with hpass | hfail
        · rcases hpass with ⟨hpassBound, rpass⟩
          let decided := natRun rom checker decision scanned
          have decidedRegs : RegistersBound full.length q decided := (decisionSafe decision le_rfl).1
          have nextSafe := checker_nextPair_safe q full i j decided rpass hi hjlive decidedRegs
          let next := natRun rom checker 9 decided
          have rnext : Ready full.length q i (j + 1) 100 next := by
            dsimp only [next, decided]
            rw [natRun_checker_nextPair rom _ rpass.pc rpass.active]
            exact ready_nextPair rom rpass
          have nextRegs : RegistersBound full.length q next := (nextSafe 9 le_rfl).1
          have hsmall : full.length - (j + 1) < remaining := by omega
          obtain ⟨rest, hrest, hresult⟩ := ih _ hsmall (j + 1) rfl (by omega) next rnext nextRegs
          have hnextRun : natRun rom checker (base + decision + 9) state = next := by
            rw [natRun_add, natRun_add]
          have prefixSafe : SafeRun q full state (base + decision + 9) :=
            SafeRun.add q full state (base + decision) 9
              (SafeRun.add q full state base decision baseSafe decisionSafe)
              (by rw [natRun_add]; exact nextSafe)
          have tailSafe : SafeRun q full (natRun rom checker (base + decision + 9) state) rest := by
            rw [hnextRun]
            exact hresult.1
          have hremaining : remaining = (full.length - (j + 1)) + 1 := by omega
          have hprefix : base + decision + 9 ≤ 53 * q + 47 := by dsimp [base]; omega
          refine ⟨base + decision + 9 + rest, ?_, SafeRun.add q full state _ _ prefixSafe tailSafe, ?_⟩
          · rw [hremaining, Nat.add_mul, Nat.one_mul]
            omega
          · rw [natRun_add, hnextRun]
            exact hresult.2
        · have hwork : 53 * q + 47 ≤ remaining * (53 * q + 47) := by
            simpa only [Nat.one_mul] using Nat.mul_le_mul_right (53 * q + 47) (by omega : 1 ≤ remaining)
          refine ⟨base + decision, ?_, SafeRun.add q full state base decision baseSafe decisionSafe, Or.inl ?_⟩
          · dsimp [base]
            omega
          · rw [natRun_add]
            exact hfail
  exact solve (full.length - j) j rfl hj state ready hr

theorem checker_safe_rows (q : Nat) (full : List (Finset (Fin q))) (i : Nat)
    (hi : i ≤ full.length) (j : Nat) (hj : j ≤ full.length) (state : NatState)
    (ready : Ready full.length q i j 50 state) (hr : RegistersBound full.length q state) :
    ∃ steps : Nat, steps ≤ (full.length - i) * (full.length * (53 * q + 47) + 26) + 8 ∧
      SafeRun q full state steps ∧ (natRun (rawIncidenceROM q full) checker steps state).halted = true := by
  have solve : ∀ remaining : Nat, ∀ i : Nat, full.length - i = remaining → i ≤ full.length →
      ∀ j : Nat, j ≤ full.length → ∀ state : NatState, Ready full.length q i j 50 state →
        RegistersBound full.length q state →
        ∃ steps : Nat, steps ≤ remaining * (full.length * (53 * q + 47) + 26) + 8 ∧
          SafeRun q full state steps ∧ (natRun (rawIncidenceROM q full) checker steps state).halted = true := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro i hsize hi j hj state ready hr
      let rom := rawIncidenceROM q full
      by_cases hlast : i = full.length
      · subst i
        have hz : remaining = 0 := by omega
        exact ⟨8, by rw [hz]; simp, checker_outer_terminal_safe q full j state ready hj hr,
          (checker_outer_terminal rom ready).1⟩
      · have hilive : i < full.length := by omega
        let pairs := natRun rom checker 10 state
        have pairSafe := checker_outer_setup_safe q full i j state ready hilive hj hr
        have rpairs : Ready full.length q i 0 100 pairs := checker_outer_setup rom ready hilive
        have pairRegs : RegistersBound full.length q pairs := (pairSafe 10 le_rfl).1
        obtain ⟨rowSteps, hrowBound, hrowResult⟩ :=
          checker_safe_row q full i hilive 0 (Nat.zero_le _) pairs rpairs pairRegs
        rcases hrowResult with ⟨rowSafe, hrowExit⟩
        rcases hrowExit with hhalt | rrow
        · have hwork : full.length * (53 * q + 47) + 26 ≤ remaining * (full.length * (53 * q + 47) + 26) := by
            simpa only [Nat.one_mul] using Nat.mul_le_mul_right (full.length * (53 * q + 47) + 26)
              (by omega : 1 ≤ remaining)
          refine ⟨10 + rowSteps, ?_, SafeRun.add q full state 10 rowSteps pairSafe rowSafe, ?_⟩
          · simp only [Nat.sub_zero] at hrowBound
            omega
          · rw [natRun_add]
            exact hhalt
        · let rowEnd := natRun rom checker rowSteps pairs
          have rowRegs : RegistersBound full.length q rowEnd := (rowSafe rowSteps le_rfl).1
          have nextSafe := checker_nextRow_safe q full i full.length rowEnd rrow hilive le_rfl rowRegs
          let next := natRun rom checker 9 rowEnd
          have rnext : Ready full.length q (i + 1) full.length 50 next := by
            dsimp only [next, rowEnd]
            rw [natRun_checker_nextRow rom _ rrow.pc rrow.active]
            exact ready_nextRow rom rrow
          have nextRegs : RegistersBound full.length q next := (nextSafe 9 le_rfl).1
          have hsmall : full.length - (i + 1) < remaining := by omega
          obtain ⟨rest, hrest, restSafe, hrestHalt⟩ :=
            ih _ hsmall (i + 1) rfl (by omega) full.length le_rfl next rnext nextRegs
          have hnextRun : natRun rom checker (10 + rowSteps + 9) state = next := by
            rw [natRun_add, natRun_add]
          have prefixSafe : SafeRun q full state (10 + rowSteps + 9) :=
            SafeRun.add q full state (10 + rowSteps) 9
              (SafeRun.add q full state 10 rowSteps pairSafe rowSafe)
              (by rw [natRun_add]; exact nextSafe)
          have tailSafe : SafeRun q full (natRun rom checker (10 + rowSteps + 9) state) rest := by
            rw [hnextRun]
            exact restSafe
          have hremaining : remaining = (full.length - (i + 1)) + 1 := by omega
          have hrowBound' : rowSteps ≤ full.length * (53 * q + 47) + 7 := by
            simpa only [Nat.sub_zero] using hrowBound
          have hprefix : 10 + rowSteps + 9 ≤ full.length * (53 * q + 47) + 26 := by omega
          refine ⟨10 + rowSteps + 9 + rest, ?_, SafeRun.add q full state _ _ prefixSafe tailSafe, ?_⟩
          · rw [hremaining, Nat.add_mul, Nat.one_mul]
            omega
          · rw [natRun_add, hnextRun]
            exact hrestHalt
  exact solve (full.length - i) i rfl hi j hj state ready hr

theorem checker_has_safe_halt (q : Nat) (full : List (Finset (Fin q))) :
    ∃ steps : Nat, steps ≤ checkerSteps full.length q ∧ SafeRun q full natInitial steps ∧
      (natRun (rawIncidenceROM q full) checker steps natInitial).halted = true := by
  have initSafe := checker_init_safe q full
  have initRegs : RegistersBound full.length q (natRun (rawIncidenceROM q full) checker 10 natInitial) :=
    (initSafe 10 le_rfl).1
  obtain ⟨rest, hrest, restSafe, hhalt⟩ := checker_safe_rows q full 0 (Nat.zero_le _) 0 (Nat.zero_le _)
    (natRun (rawIncidenceROM q full) checker 10 natInitial) (natRun_checker_init q full) initRegs
  refine ⟨10 + rest, ?_, SafeRun.add q full natInitial 10 rest initSafe restSafe, ?_⟩
  · simp only [Nat.sub_zero] at hrest
    calc
      10 + rest ≤ 10 + (full.length * (full.length * (53 * q + 47) + 26) + 8) := Nat.add_le_add_left hrest 10
      _ = checkerSteps full.length q := by simp only [checkerSteps, pow_two]; ring
  · rw [natRun_add]
    exact hhalt

/-- One fixed program, eight actual heap words, and the original physical
execution/cost predicates. This is the checking phase, not tree construction. -/
theorem checker_laminarity_phase (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    let bits := indexWidth 16 full.length q
    let heap := fun _ => BitVec.ofNat bits 0
    ∃ steps : Nat, DynamicRunCorrect 8 (rawIncidenceROM q full) checker steps heap ∧
      totalCost 8 (rawIncidenceROM q full) checker steps heap ≤ 4096 * treeWork full.length q ∧
      (((packingRun (rawIncidenceROM q full) checker steps (packingInitial heap)).register .value).toNat ≤ 1) ∧
      (((packingRun (rawIncidenceROM q full) checker steps (packingInitial heap)).register .value).toNat = 1 ↔ LaminarSchedule full) := by
  obtain ⟨steps, hsteps, hsafe, hhalt⟩ := checker_has_safe_halt q full
  obtain ⟨semanticSteps, _hsemanticBound, hsemanticHalt, hflag, hcorrect⟩ := nat_checker_correct q full
  have heq := natRun_halted_eq (rawIncidenceROM q full) checker natInitial steps semanticSteps hhalt hsemanticHalt
  apply checker_word_of_prefix_safety q full hq steps hsteps hhalt
  · simpa only [heq] using hflag
  · simpa only [heq] using hcorrect
  · exact ThroughSafe.prefix _ _ _ _ _ hsafe

/-- Uniform quantifier order of A06 for the checking portion: the fixed
program and constants precede every dimension and raw incidence instance.
No serialized-tree conclusion is included in this phase theorem. -/
theorem rawLaminarity_phase_uniform :
    ∃ (constant wordFactor : Nat) (program : List PackingOp),
      0 < constant ∧ 0 < wordFactor ∧
      ∀ (q : Nat) (full : List (Finset (Fin q))), 0 < q →
        let bits := indexWidth wordFactor full.length q
        let heap := fun _ => BitVec.ofNat bits 0
        ∃ (steps heapWords : Nat), DynamicRunCorrect heapWords (rawIncidenceROM q full) program steps heap ∧
          totalCost heapWords (rawIncidenceROM q full) program steps heap ≤ constant * treeWork full.length q ∧
          (((packingRun (rawIncidenceROM q full) program steps (packingInitial heap)).register .value).toNat ≤ 1) ∧
          (((packingRun (rawIncidenceROM q full) program steps (packingInitial heap)).register .value).toNat = 1 ↔ LaminarSchedule full) := by
  refine ⟨4096, 16, checker, by decide, by decide, ?_⟩
  intro q full hq
  obtain ⟨steps, hrun, hcost, hflag, hcorrect⟩ := checker_laminarity_phase q full hq
  exact ⟨steps, 8, hrun, hcost, hflag, hcorrect⟩

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM
