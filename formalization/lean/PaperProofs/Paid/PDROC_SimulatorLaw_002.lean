module

public import PaperProofs.Paid.PDROC_Simulator_004
public import PaperProofs.Paid.PDROC_SimulatorProjection_001
public import PaperProofs.Common.NativeCausality

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- A before-birth history has not written the target and has not halted.
Consequently its replay has never queried the target's auxiliary tape. -/
theorem simulatorStep_eq_off_target {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seedA seedB : SimSeed) (target : I.Stage) (cache : SimulatorCache I) (event : VisibleEvent I)
    (hdraw : ∀ stage : I.Stage, stage ≠ target → ∀ entry, draw seedA stage entry = draw seedB stage entry)
    (hwrite : historyWritten [event] target = none) (hhalt : historyHalted [event] = false) :
    simulatorStep draw seedA cache event = simulatorStep draw seedB cache event := by
  cases event with
  | wrote stage bit serial =>
    have hne : stage ≠ target := by
      intro heq
      subst stage
      simp [historyWritten, historyWrite, eventWrite] at hwrite
    simp only [simulatorStep, hdraw stage hne cache.shadow]
  | stopped => simp [historyHalted, historyActions, eventAction] at hhalt
  | abandoned => simp [historyHalted, historyActions, eventAction] at hhalt
  | observation | report | committed | executed | advanced => rfl

theorem simulatorReplay_eq_off_target {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seedA seedB : SimSeed) (target : I.Stage) (history : List (VisibleEvent I))
    (hdraw : ∀ stage : I.Stage, stage ≠ target → ∀ entry, draw seedA stage entry = draw seedB stage entry)
    (hwrite : historyWritten history target = none) (hhalt : historyHalted history = false) :
    simulatorReplay draw seedA history = simulatorReplay draw seedB history := by
  induction history using List.reverseRecOn with
  | nil => rfl
  | @append_singleton history event ih =>
    have hw := (historyWritten_none_append history [event] target).mp hwrite
    have hh : historyHalted history = false ∧ historyHalted [event] = false := by
      simpa only [historyHalted_append, Bool.or_eq_false_eq_eq_false_and_eq_false] using hhalt
    have hi := ih hw.1 hh.1
    simp only [simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change simulatorStep draw seedA (simulatorReplay draw seedA history) event =
      simulatorStep draw seedB (simulatorReplay draw seedB history) event
    rw [hi]
    exact simulatorStep_eq_off_target draw seedA seedB target _ event hdraw hw.2 hh.2

def SimulatorSeedAgreeOff {Seed : Type*} (P : PaperProofs.Paid.Parameters) (target : P.sharedInstance.Stage)
    (seedA seedB : SimulatorSeed P Seed) : Prop :=
  seedA.1 = seedB.1 ∧ ∀ stage : P.sharedInstance.Stage, stage ≠ target →
    seedA.2.1 stage = seedB.2.1 stage ∧ seedA.2.2 stage = seedB.2.2 stage

theorem simulatorSeedDraw_eq_off_target {Seed : Type*} [MeasurableSpace Seed]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : SimulatorSeed P Seed) (hseed : SimulatorSeedAgreeOff P target seedA seedB)
    (stage : P.sharedInstance.Stage) (hne : stage ≠ target) (entry : List (VisibleEvent P.sharedInstance)) :
    simulatorSeedDraw P fee hfee source seedA stage entry = simulatorSeedDraw P fee hfee source seedB stage entry := by
  simp only [simulatorSeedDraw, hseed.1, (hseed.2 stage hne).1]

theorem simulatorCandidateFromData_eq_off_target (history : List (VisibleEvent I)) (target : I.Stage)
    (hcursor : historyCursor history < target.val) (actionA actionB : Action I)
    (drawA drawB : I.Stage → Option (SimulatorDraw I)) (coinA coinB : I.Stage → Bool)
    (haction : actionA = actionB) (hdraw : ∀ stage : I.Stage, stage ≠ target → drawA stage = drawB stage)
    (hcoin : ∀ stage : I.Stage, stage ≠ target → coinA stage = coinB stage) :
    simulatorCandidateFromData history actionA drawA coinA = simulatorCandidateFromData history actionB drawB coinB := by
  by_cases hh : historyHalted history = true
  · simp only [simulatorCandidateFromData, hh, ↓reduceIte]
  · by_cases hs : historyCursor history < I.compatibility.length
    · let stage : I.Stage := ⟨historyCursor history, hs⟩
      have hne : stage ≠ target := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp only [stage] at hv
        omega
      have hstageAt : simulatorStageAt history = some stage := by
        simp only [simulatorStageAt, dite_eq_left hs]
        rfl
      simp only [simulatorCandidateFromData, hh, Bool.false_eq_true, ↓reduceIte, hstageAt, haction]
      rw [hdraw stage hne, hcoin stage hne]
    · have hstageAt : simulatorStageAt history = none := by simp only [simulatorStageAt, dite_eq_right hs]
      simp only [simulatorCandidateFromData, hh, Bool.false_eq_true, ↓reduceIte, hstageAt, haction]

theorem simulatorCandidate_eq_off_target {Seed : Type*} [MeasurableSpace Seed]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : SimulatorSeed P Seed) (hseed : SimulatorSeedAgreeOff P target seedA seedB)
    (history : List (VisibleEvent P.sharedInstance)) (hcursor : historyCursor history < target.val)
    (hwrite : historyWritten history target = none) (hhalt : historyHalted history = false) :
    simulatorCandidate P fee hfee source seedA history = simulatorCandidate P fee hfee source seedB history := by
  have hcache := simulatorReplay_eq_off_target (simulatorSeedDraw P fee hfee source) seedA seedB target history
    (simulatorSeedDraw_eq_off_target P fee hfee source target seedA seedB hseed) hwrite hhalt
  unfold simulatorCandidate simulatorCandidateAtCache
  rw [hcache]
  apply simulatorCandidateFromData_eq_off_target history target hcursor
  · rw [hseed.1]
  · intro stage hne
    exact simulatorSeedDraw_eq_off_target P fee hfee source target seedA seedB hseed stage hne _
  · intro stage hne
    exact (hseed.2 stage hne).2

theorem simulatorRule_eq_off_target {Seed : Type*} [MeasurableSpace Seed]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : SimulatorSeed P Seed) (hseed : SimulatorSeedAgreeOff P target seedA seedB)
    (history : List (VisibleEvent P.sharedInstance)) (hcursor : historyCursor history < target.val)
    (hwrite : historyWritten history target = none) (hhalt : historyHalted history = false) :
    simulatorRule P fee hfee source seedA history = simulatorRule P fee hfee source seedB history := by
  simp only [simulatorRule, simulatorCandidate_eq_off_target P fee hfee source target seedA seedB hseed history hcursor hwrite hhalt]

/-- Closed true-prefix non-interference: changing only the target's fresh
auxiliary tape/coin cannot change any action strictly before its birth. -/
theorem simulatorRule_eq_off_target_prefix {Seed : Type*} [MeasurableSpace Seed]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : SimulatorSeed P Seed) (hseed : SimulatorSeedAgreeOff P target seedA seedB)
    {PrefixSeed : Type*} (actualRule : PolicyRule P.sharedInstance PrefixSeed)
    (actualSeed : PrefixSeed) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val mode accounting actualRule actualSeed truth tapes n s)
    (ha : s.halted = false) (hcursor : s.cursor < target.val) :
    simulatorRule P fee hfee source seedA s.history = simulatorRule P fee hfee source seedB s.history := by
  have hc := prefix_historyCursor (P.input fee hfee) C.val mode accounting actualRule actualSeed truth tapes hp
  have hw := prefix_historyWritten (P.input fee hfee) C.val mode accounting actualRule actualSeed truth tapes hp target
  have hh := prefix_historyHalted (P.input fee hfee) C.val mode accounting actualRule actualSeed truth tapes hp
  apply simulatorRule_eq_off_target P fee hfee source target seedA seedB hseed s.history
  · simpa only [hc] using hcursor
  · exact hw.trans ((prefix_cursorInvariant (P.input fee hfee) C.val mode accounting actualRule actualSeed truth tapes hp).future_written target hcursor)
  · exact hh.trans ha





theorem SimulatorSeedAgreeOff.symm {Seed : Type*} {P : PaperProofs.Paid.Parameters}
    {target : P.sharedInstance.Stage} {seedA seedB : SimulatorSeed P Seed}
    (h : SimulatorSeedAgreeOff P target seedA seedB) : SimulatorSeedAgreeOff P target seedB seedA :=
  ⟨h.1.symm, fun stage hs => ⟨(h.2 stage hs).1.symm, (h.2 stage hs).2.symm⟩⟩

/-- The actual interpreter states agree through the first target birth;
only actions strictly before the target are compared. -/
theorem simulatorRun_eq_before_target {Seed : Type*} [MeasurableSpace Seed]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : SimulatorSeed P Seed)
    (hseed : SimulatorSeedAgreeOff P target seedA seedB) (world : (P.input fee hfee).World) (n : ℕ)
    (hbefore : ∀ k < n, (run (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (seedA, world) k).cursor < target.val) :
    run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seedA, world) n =
      run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seedB, world) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
    by_cases hh : (run (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) (seedA, world) n).halted = true
    · rw [run_succ_of_halted (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seedA, world) n hh,
        run_succ_of_halted (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seedB, world) n (heq ▸ hh), heq]
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) (simulatorRule_legal P fee hfee C accounting source) (seedA, world) n
      have haction := simulatorRule_eq_off_target_prefix P fee hfee C .uncapped accounting source target
        seedA seedB hseed (simulatorRule P fee hfee source) seedA (P.input fee hfee |>.truthAt world)
        (worldTapes (P.input fee hfee) world) hp ha (hbefore n (Nat.lt_succ_self n))
      simp only [run, ← heq, haction]

theorem simulatorFirstEntry_transport_off_target {Seed : Type*} [MeasurableSpace Seed]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : SimulatorSeed P Seed)
    (hseed : SimulatorSeedAgreeOff P target seedA seedB) (world : (P.input fee hfee).World) (n : ℕ)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) target.val n (seedA, world)) :
    FirstEntryAt (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) target.val n (seedB, world) ∧
      run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seedA, world) n =
        run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seedB, world) n := by
  have hbefore := firstEntryAt_strictly_before (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) (simulatorRule_legal P fee hfee C accounting source) (seedA, world) target.val n hentry
  have heq := simulatorRun_eq_before_target P fee hfee C accounting source target seedA seedB hseed world n hbefore
  refine ⟨⟨?_, ?_⟩, heq⟩
  · simpa only [← heq] using hentry.1
  · intro k hk
    have hkEq := simulatorRun_eq_before_target P fee hfee C accounting source target seedA seedB hseed world k
      (fun j hj => hbefore j (lt_trans hj hk))
    simpa only [← hkEq] using hentry.2 k hk

theorem simulatorEntryStartup_eq_off_target {Seed : Type*} [MeasurableSpace Seed]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : SimulatorSeed P Seed)
    (hseed : SimulatorSeedAgreeOff P target seedA seedB) (world : (P.input fee hfee).World) (n : ℕ) :
    entryStartupAt (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) target n (seedA, world) =
      entryStartupAt (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) target n (seedB, world) := by
  classical
  by_cases he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) target.val n (seedA, world)
  · obtain ⟨he', hs⟩ := simulatorFirstEntry_transport_off_target P fee hfee C accounting source target seedA seedB hseed world n he
    simp only [entryStartupAt, he, he', ↓reduceIte, hs]
  · have he' : ¬ FirstEntryAt (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) target.val n (seedB, world) := by
      intro h
      exact he (simulatorFirstEntry_transport_off_target P fee hfee C accounting source target seedB seedA hseed.symm world n h).1
    simp only [entryStartupAt, he, he', ↓reduceIte]

end PDROC
