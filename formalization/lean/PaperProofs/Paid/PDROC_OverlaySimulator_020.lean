module

public import PaperProofs.Paid.PDROC_OverlaySimulator_009
public import PaperProofs.Paid.PDROC_OverlayInterface_001
public import PaperProofs.Paid.PDROC_OverlayTermination_001
public import PaperProofs.Paid.PDROC_Simulator_009
public import PaperProofs.Paid.PDROC_Simulator_012
public import PaperProofs.Paid.PDROC_Simulator_014
public import PaperProofs.Paid.PDROC_StageObservables_002
public import PaperProofs.Common.HistorySuffixRun
public import PaperProofs.Statistics.PDROC_Attainment_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

section Native010

variable {I : Instance}

/-- A checked virtual-only call really extends the original SOURCE Native
prefix. This produces no physical step and makes no use of a virtual handle
as an actual handle. -/
theorem overlayGhostCall_source_step
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting source seed truth tapes n s) (ha : s.halted = false)
    (call : OverlayGhostCall I) (hc : source seed s.history = overlayGhostAction call)
    (hallow : historyAllowsAction s.history (source seed s.history)) :
    ∃ next : State I,
      Step input C .uncapped accounting tapes s (source seed s.history) next ∧
      next.history = s.history ++ overlayGhostEvents [call] ∧ next.halted = false := by
  obtain ⟨next, hs⟩ := historyAllowsAction_sound input C hearly accounting source seed truth tapes hp ha _ hallow
  refine ⟨next, hs, ?_, ?_⟩
  all_goals
    rw [hc] at hs
    rcases call with ⟨reserve, handle, tool⟩
    cases reserve <;> simp only [overlayGhostAction, Bool.false_eq_true, ite_false, ite_true] at hs
    all_goals cases hs; simp [record, overlayGhostEvents]

/-- The complete ghost packet is a genuine source execution segment, with
its exact history and clock. Failed-path virtual reservations are retained;
the actual execution remains separate and its payments cannot be supplied
by this theorem. -/
theorem overlayGhostTrace_source_prefix
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting source seed truth tapes n s) (ha : s.halted = false)
    (calls : List (OverlayGhostCall I)) (htrace : OverlayGhostTrace source seed s.history calls) :
    ∃ final : State I,
      Prefix input C .uncapped accounting source seed truth tapes (n + calls.length) final ∧
      final.history = s.history ++ overlayGhostEvents calls ∧ final.halted = false := by
  induction calls generalizing n s with
  | nil => exact ⟨s, by simpa using hp, by simp [overlayGhostEvents], ha⟩
  | cons call rest ih =>
    rcases htrace with ⟨hc, hallow, hrest⟩
    obtain ⟨next, hs, hh, hn⟩ := overlayGhostCall_source_step input C hearly accounting source seed truth tapes hp ha call hc hallow
    have hp' : Prefix input C .uncapped accounting source seed truth tapes (n + 1) next := .next hp hs
    have hrest' : OverlayGhostTrace source seed next.history rest := by rw [hh]; exact hrest
    obtain ⟨final, hf, hfh, hhalt⟩ := ih hp' hn hrest'
    refine ⟨final, ?_, ?_, hhalt⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
    · simpa [hh, overlayGhostEvents, List.append_assoc] using hfh


end Native010

section Native011

variable {Seed : Type u} [MeasurableSpace Seed]

/-- Candidate D14 data for the concrete controller. The old D06 coin fields
are unused constants; the new record-aware selectors read exactly the
pre-sampled row at the selected auxiliary record. -/
noncomputable def overlayData (P : Parameters) (source : PolicyRule P.sharedInstance Seed) :
    OverlayDraft.OverlaySimulatorData P.sharedInstance Seed (OverlaySeed P Seed) where
  sourceSeed := Prod.fst
  shadow := overlayShadow P source
  record := fun seed stage entry => simulatorDrawRecord
    (overlaySeedDraw P source seed stage (overlayShadow P source seed entry))
  endpointCoin := fun _ _ => false
  mixtureCoins := fun _ _ => (false, false)
  falsePositiveCoin := fun _ _ => false
  mixtureCoinsAtRecord := overlaySeedCoins P
  falsePositiveCoinAtRecord := overlaySeedMark P

theorem overlayData_measurable (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) : OverlayDraft.OverlaySimulatorMeasurable (overlayData P source) := by
  have hs := measurable_overlayShadow P source hm
  refine ⟨?_, measurable_overlaySeedCoins P, measurable_overlaySeedMark P⟩
  refine ⟨measurable_fst, hs, ?_, fun _ => measurable_const,
    fun _ => measurable_const, fun _ => measurable_const⟩
  intro stage
  exact (measurable_of_countable simulatorDrawRecord).comp
    ((measurable_overlaySeedDraw P source hm stage).comp (measurable_fst.prodMk hs))

omit [MeasurableSpace Seed] in
theorem overlayData_shadowCausal (P : Parameters) (source : PolicyRule P.sharedInstance Seed) :
    P.ShadowCausal (overlayData P source).toRecordSimulatorData := by
  refine ⟨fun _ => rfl, ?_⟩
  exact overlayReplay_shadow_causal (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)

omit [MeasurableSpace Seed] in
/-- The full physical-subsequence part of the D14 path target holds at every
actual prefix, including failure and abandonment. No probabilistic or
nonbinding-guard premise is used. -/
theorem overlayData_physical_subsequences (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) (n : ℕ) :
    let actual := (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history
    let virtual := (overlayData P source).shadow sample.1 actual
    (reservedPairs actual).Sublist (reservedPairs virtual) ∧
      (executedPairs actual).Sublist (executedPairs virtual) ∧ historyUsed actual ⊆ historyUsed virtual := by
  dsimp only
  exact ⟨(overlayReplay_pair_sublists (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) _ _).1,
    (overlayReplay_pair_sublists (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) _ _).2,
    overlayReplay_used_subset (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) _ _⟩

omit [MeasurableSpace Seed] in
theorem overlayData_report_not_early (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) :
    (historyReport ((overlayData P source).shadow seed history) stage).isSome = true ↔
      (historyReport history stage).isSome = true :=
  overlayReplay_report_isSome (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed history stage

omit [MeasurableSpace Seed] in
theorem overlayPolicy_execution_count (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) (n : ℕ) :
    (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.executions.length ≤
      min P.certificate.stages P.tools := by
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
    (overlayRule_legal P fee hfee C accounting source) sample n
  have htools : P.sharedInstance.toolCount = P.tools := rfl
  simpa only [P.stageCount_eq, htools] using Ledger.execution_count_le
    (prefix_ledgerWellFormed (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) sample.1 _ _ hp)


end Native011

section Native012

variable {I : Instance} {SimSeed : Type u}

theorem overlayFold_observations
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (stage : I.Stage) (letters : List (Fin 2)) (cache : SimulatorCache I) :
    ((letters.map (fun symbol => VisibleEvent.observation stage symbol.val)).foldl
      (overlayStep draw mark ghost seed) cache) =
      {cache with seen := cache.seen ++ letters.map (fun symbol => .observation stage symbol.val)} := by
  induction letters generalizing cache with
  | nil => simp
  | cons letter rest ih =>
    simp only [List.map_cons, List.foldl_cons, overlayStep, simulatorStep, simulatorAppend, List.append_nil,
      ih, List.append_assoc, List.singleton_append]

theorem overlayReplay_append_observations
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (entry : List (VisibleEvent I)) (stage : I.Stage) (letters : List (Fin 2)) :
    overlayReplay draw mark ghost seed (entry ++ letters.map (fun symbol => .observation stage symbol.val)) =
      {overlayReplay draw mark ghost seed entry with
        seen := entry ++ letters.map (fun symbol => .observation stage symbol.val)} := by
  simp only [overlayReplay, List.foldl_append, overlayFold_observations]
  rw [← overlayReplay, overlayReplay_seen]

theorem overlayMixtureAction_allowed {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (m : ℕ) (coins : Bool × Bool)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage = none) :
    historyAllowsAction history (overlayMixtureAction history stage m coins) :=
  simulatorBoundaryAction_allowed history stage (overlayMAPEndpointRecord (overlayMixtureEndpoint m coins))
    coins.2 true rfl hc hw

variable {Seed : Type u}

theorem overlayShadow_append_observations (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (entry : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (letters : List (Fin 2)) :
    overlayShadow P source seed (entry ++ letters.map (fun symbol => .observation stage symbol.val)) =
      overlayShadow P source seed entry := by
  unfold overlayShadow overlaySeedReplay
  rw [overlayReplay_append_observations]

theorem overlayCandidate_prewrite_some (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none)
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed history) = some draw)
    (hd : draw.record.decision = some decision) :
    overlayCandidate P fee hfee source seed history = overlayMixtureAction history stage
      (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee draw.record) (P.overlayRecordTarget_pos fee hfee draw.record))
      (overlaySeedCoins P seed stage draw.record) := by
  simp only [overlayCandidate, overlayCandidateAtCache, hh, Bool.false_eq_true, ite_false,
    simulatorStageAt_some history stage hc, hw, ite_true]
  change overlayDrawAction P fee hfee history stage (overlaySeedCoins P seed stage)
    (overlaySeedDraw P source seed stage (overlayShadow P source seed history)) = _
  simp only [hdraw, overlayDrawAction, hd]

theorem overlayRule_prewrite_some (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none)
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed history) = some draw)
    (hd : draw.record.decision = some decision) :
    overlayRule P fee hfee source seed history = overlayMixtureAction history stage
      (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee draw.record) (P.overlayRecordTarget_pos fee hfee draw.record))
      (overlaySeedCoins P seed stage draw.record) := by
  rw [overlayRule, overlayCandidate_prewrite_some P fee hfee source seed history stage draw decision hh hc hw hdraw hd]
  exact ite_eq_left (overlayMixtureAction_allowed history stage _ _ hc hw)


end Native012

section Native013

variable {Seed : Type u}

/-- The record and its selected private mixture stay fixed during physical
reviews. The guard is nonbinding on every such genuine prewrite word. -/
theorem overlayRule_on_mixture_word (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (entry : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted entry = false) (hc : historyCursor entry = stage.val)
    (hw : historyWritten entry stage = none)
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed entry) = some draw)
    (hd : draw.record.decision = some decision) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ) :
    overlayRule P fee hfee source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n) =
      overlayMixtureAction (entry ++ headReviewHistory (P.input fee hfee) stage tape n) stage
        (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee draw.record) (P.overlayRecordTarget_pos fee hfee draw.record))
        (overlaySeedCoins P seed stage draw.record) := by
  let history := entry ++ headReviewHistory (P.input fee hfee) stage tape n
  have heq : history = entry ++ (List.ofFn (fun k : Fin n => tape k.val)).map (fun symbol => .observation stage symbol.val) :=
    congrArg (List.append entry) (headReviewHistory_eq_simulatorObservations P fee hfee stage tape n)
  have hh' : historyHalted history = false := by
    rw [heq]
    exact (historyHalted_append_observations entry stage _).trans hh
  have hc' : historyCursor history = stage.val := by
    rw [heq]
    exact (historyCursor_append_observations entry stage _).trans hc
  have hw' : historyWritten history stage = none := by
    rw [heq]
    exact (historyWritten_append_observations entry stage stage _).trans hw
  have hshadow : overlayShadow P source seed history = overlayShadow P source seed entry := by
    rw [heq]
    exact overlayShadow_append_observations P source seed entry stage _
  have hdraw' : overlaySeedDraw P source seed stage (overlayShadow P source seed history) = some draw := by
    rw [hshadow]
    exact hdraw
  exact overlayRule_prewrite_some P fee hfee source seed history stage draw decision hh' hc' hw' hdraw' hd

theorem overlayRule_on_mixture_word_before (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (entry : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted entry = false) (hc : historyCursor entry = stage.val)
    (hw : historyWritten entry stage = none) (ho : historyObservations entry stage = [])
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed entry) = some draw)
    (hd : draw.record.decision = some decision) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hbefore : (n : ℕ∞) < (P.overlayRecordTest fee hfee draw.record).rule.stop
      (overlaySeedCoins P seed stage draw.record) tape) :
    overlayRule P fee hfee source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n) = .review stage := by
  rw [overlayRule_on_mixture_word P fee hfee source seed entry stage draw decision hh hc hw hdraw hd tape n]
  have hzero : simulatorObservedScore entry stage = 0 := by
    simp only [simulatorObservedScore, ho, List.map_nil, List.sum_nil]
  have hscore : simulatorObservedScore (entry ++ headReviewHistory (P.input fee hfee) stage tape n) stage =
      P.binarySymmetric.signedSum tape n := by
    simpa only [hzero, zero_add] using simulatorObservedScore_headReview P fee hfee entry stage tape n
  exact overlayMixtureAction_before_stop P _ stage _ _ tape n hscore hbefore

/-- At the actual adjacent-mixture stopping time the controller really
writes its MAP decision. This is a pointwise Native action identity; finite
stopping is not inserted as a new probabilistic assumption. -/
theorem overlayRule_on_mixture_word_at_stop (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (entry : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted entry = false) (hc : historyCursor entry = stage.val)
    (hw : historyWritten entry stage = none) (ho : historyObservations entry stage = [])
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed entry) = some draw)
    (hd : draw.record.decision = some decision) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hs : (P.overlayRecordTest fee hfee draw.record).rule.stop
      (overlaySeedCoins P seed stage draw.record) tape = (n : ℕ∞)) :
    overlayRule P fee hfee source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n) =
      .write stage ((P.overlayRecordTest fee hfee draw.record).rule.decision
        (overlaySeedCoins P seed stage draw.record) tape) := by
  rw [overlayRule_on_mixture_word P fee hfee source seed entry stage draw decision hh hc hw hdraw hd tape n]
  have hzero : simulatorObservedScore entry stage = 0 := by
    simp only [simulatorObservedScore, ho, List.map_nil, List.sum_nil]
  have hscore : simulatorObservedScore (entry ++ headReviewHistory (P.input fee hfee) stage tape n) stage =
      P.binarySymmetric.signedSum tape n := by
    simpa only [hzero, zero_add] using simulatorObservedScore_headReview P fee hfee entry stage tape n
  exact overlayMixtureAction_at_stop P _ stage _ _ tape n hscore hs


end Native013

section Native014

variable {Seed : Type u}

/-- The original Native run executes exactly the adjacent-mixture physical
review segment. This reuses the D06 review-state infrastructure and proves
the new actual controller identity rather than postulating a stage result. -/
theorem overlayRun_eq_reviewStateFrom (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage) (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start).ledger.written stage = none)
    (hr : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start).ledger.reviews stage = 0)
    (ho : historyObservations (run (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) (seed, world) start).history stage = [])
    (hdraw : overlaySeedDraw P source seed stage
      (overlayShadow P source seed (run (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) (seed, world) start).history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hn : (n : ℕ∞) ≤ (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record)
      (worldTapes (P.input fee hfee) world stage)) :
    run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) (start + n) =
      simulatorReviewStateFrom (P.input fee hfee) accounting stage (worldTapes (P.input fee hfee) world stage)
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start) n := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let s := run input C.val .uncapped accounting actual (seed, world) start
  let tape := worldTapes input world stage
  obtain ⟨k, _hk, hprefix⟩ := run_has_prefix input C.val .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) (seed, world) start
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
  induction n with
  | zero => rfl
  | succ n ih =>
    have hle : (n : ℕ∞) ≤ (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record) tape :=
      (show (n : ℕ∞) ≤ (n + 1 : ℕ∞) from by exact_mod_cast Nat.le_succ n).trans hn
    have hbefore : (n : ℕ∞) < (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record) tape :=
      (show (n : ℕ∞) < (n + 1 : ℕ∞) from by exact_mod_cast Nat.lt_succ_self n).trans_le hn
    have heq := ih hle
    let before := simulatorReviewStateFrom input accounting stage tape s n
    have heq' : run input C.val .uncapped accounting actual (seed, world) (start + n) = before := heq
    have hbactive : before.halted = false := simulatorReviewStateFrom_active input accounting stage tape s n ha
    have haction : actual seed before.history = .review stage := by
      rw [simulatorReviewStateFrom_history]
      exact overlayRule_on_mixture_word_before P fee hfee source seed s.history stage draw decision
        hhh hhc hhw ho hdraw hd tape n hbefore
    have hstep : Step input C.val .uncapped accounting (worldTapes input world) before (.review stage)
        (simulatorReviewStateFrom input accounting stage tape s (n + 1)) := by
      have hwb : before.ledger.written stage = none :=
        (congrFun (simulatorReviewStateFrom_written input accounting stage tape s n) stage).trans hw
      have h := Step.review (input := input) (C := C.val) (mode := ResourceMode.uncapped)
        (accounting := accounting) (tapes := worldTapes input world) before stage
        ⟨hbactive, (simulatorReviewStateFrom_cursor input accounting stage tape s n).trans hc⟩
        hwb (Or.inl rfl)
      have hcount : before.ledger.reviews stage = (n : ℕ∞) :=
        simulatorReviewStateFrom_reviews input accounting stage tape s n hr
      change Step input C.val .uncapped accounting (worldTapes input world) before (.review stage)
        (record accounting before (.review stage) [.observation stage (tape n).val]
          (reviewLedger before stage) before.cursor false)
      simpa only [hcount, ENat.toNat_natCast] using h
    rw [Nat.add_succ]
    apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) (start + n) _
    · exact (congrArg State.halted heq').trans hbactive
    · rw [heq', haction]
      exact hstep


end Native014

section Native015

variable {Seed : Type u}

/-- Exact actual write and genuine early report at a finite adjacent-mixture
stop. The original Native interpreter performs all physical reviews first. -/
theorem overlayRun_write_at_mixture (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    let tape := worldTapes (P.input fee hfee) world stage
    let before := simulatorReviewStateFrom (P.input fee hfee) accounting stage tape s n
    let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record) tape
    run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) (start + n + 1) =
      record accounting before (.write stage bit) (writeResponses C.val before stage bit)
        (reportedWriteLedger C.val before stage bit) before.cursor false := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record) tape
  obtain ⟨k, _hk, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) (seed, world) start
  have hprefix : Prefix input C.val .uncapped accounting actual seed (input.truthAt world) (worldTapes input world) k s := hs0 ▸ hp
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
  have ha0 : (run input C.val .uncapped accounting actual (seed, world) start).halted = false :=
    (congrArg State.halted hs0).trans ha
  have hc0 : (run input C.val .uncapped accounting actual (seed, world) start).cursor = stage.val :=
    (congrArg State.cursor hs0).trans hc
  have hw0 : (run input C.val .uncapped accounting actual (seed, world) start).ledger.written stage = none :=
    (congrArg (fun st => st.ledger.written stage) hs0).trans hw
  have hr0 : (run input C.val .uncapped accounting actual (seed, world) start).ledger.reviews stage = 0 :=
    (congrArg (fun st => st.ledger.reviews stage) hs0).trans hr
  have ho0 : historyObservations (run input C.val .uncapped accounting actual (seed, world) start).history stage = [] :=
    (congrArg (fun st => historyObservations st.history stage) hs0).trans ho
  have hdraw0 : overlaySeedDraw P source seed stage
      (overlayShadow P source seed (run input C.val .uncapped accounting actual (seed, world) start).history) = some draw :=
    (congrArg (fun st => overlaySeedDraw P source seed stage
      (overlayShadow P source seed st.history)) hs0).trans hdraw
  have hreview := overlayRun_eq_reviewStateFrom P fee hfee C accounting source seed world start stage draw decision
    ha0 hc0 hw0 hr0 ho0 hdraw0 hd n (by rw [hs])
  have heq : run input C.val .uncapped accounting actual (seed, world) (start + n) = before := by
    simpa only [hs0] using hreview
  have haction : actual seed before.history = .write stage bit :=
    (congrArg (actual seed) (simulatorReviewStateFrom_history input accounting stage tape s n)).trans
      (overlayRule_on_mixture_word_at_stop P fee hfee source seed s.history stage draw decision hhh hhc hhw ho hdraw hd tape n hs)
  have hbactive : before.halted = false := simulatorReviewStateFrom_active input accounting stage tape s n ha
  have hbw : before.ledger.written stage = none :=
    (congrFun (simulatorReviewStateFrom_written input accounting stage tape s n) stage).trans hw
  have hstep : Step input C.val .uncapped accounting (worldTapes input world) before (.write stage bit)
      (record accounting before (.write stage bit) (writeResponses C.val before stage bit)
        (reportedWriteLedger C.val before stage bit) before.cursor false) :=
    .write before stage bit ⟨hbactive, (simulatorReviewStateFrom_cursor input accounting stage tape s n).trans hc⟩ hbw (Or.inl rfl)
  apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) (start + n) _
  · exact (congrArg State.halted heq).trans hbactive
  · rw [heq, haction]
    exact hstep


end Native015

section Native016

variable {Seed : Type u} [MeasurableSpace Seed]

theorem overlay_writing_record_observables_at_stop (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    let tape := worldTapes (P.input fee hfee) world stage
    P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage =
      some ((P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record) tape) ∧
    P.paidRunReviewCount fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage = (n : ℕ∞) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record) tape
  have hstate := overlayRun_write_at_mixture P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hfields : (reportedWriteLedger C.val before stage bit).written stage = some bit ∧
      (reportedWriteLedger C.val before stage bit).reviews stage = (n : ℕ∞) := by
    have hreview : before.ledger.reviews stage = (n : ℕ∞) :=
      simulatorReviewStateFrom_reviews input accounting stage tape s n hr
    simp only [reportedWriteLedger]
    split_ifs <;> exact ⟨Function.update_self _ _ _, hreview⟩
  have hws : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.written stage = some bit := by
    rw [hstate]
    exact hfields.1
  have hrs : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.reviews stage = (n : ℕ∞) := by
    rw [hstate]
    exact hfields.2
  exact actualStageObservables_of_written P fee hfee C .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) (seed, world) (start + n + 1) stage bit n hws hrs

omit [MeasurableSpace Seed] in
theorem overlayCandidate_prewrite (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none) :
    overlayCandidate P fee hfee source seed history = overlayDrawAction P fee hfee history stage (overlaySeedCoins P seed stage)
      (overlaySeedDraw P source seed stage (overlayShadow P source seed history)) := by
  simp only [overlayCandidate, overlayCandidateAtCache, hh, Bool.false_eq_true, ite_false,
    simulatorStageAt_some history stage hc, hw, ite_true]
  rfl

omit [MeasurableSpace Seed] in
theorem overlaySeedDraw_some_spec (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (draw : SimulatorDraw P.sharedInstance) (hd : overlaySeedDraw P source seed stage entry = some draw) :
    draw.record.decision = optionWriteBit draw.action ∧ draw.action ≠ .review stage :=
  simulatorDrawAt_some_spec P 0 (by norm_num) source stage seed.1 entry (seed.2.1 stage) draw hd

omit [MeasurableSpace Seed] in
theorem overlayRule_prewrite_none_terminal (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none)
    (hnone : (simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed history))).decision = none) :
    overlayRule P fee hfee source seed history = .stop ∨
      overlayRule P fee hfee source seed history = .abandon := by
  have hraw := overlayCandidate_prewrite P fee hfee source seed history stage hh hc hw
  cases hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed history) with
  | none =>
    have hab : overlayCandidate P fee hfee source seed history = .abandon := by
      simpa only [hdraw, overlayDrawAction] using hraw
    exact Or.inr (by simp only [overlayRule, hab, historyAllowsAction, ↓reduceIte])
  | some draw =>
    have hd : draw.record.decision = none := by
      simpa only [hdraw, simulatorDrawRecord, Option.map_some, Option.getD_some] using hnone
    have hraw' : overlayCandidate P fee hfee source seed history =
        reserialAction history (fun _ bit => bit) draw.action := by
      simpa only [hdraw, overlayDrawAction, hd] using hraw
    by_cases hallow : historyAllowsAction history (reserialAction history (fun _ bit => bit) draw.action)
    · have hspec := overlaySeedDraw_some_spec P source seed stage _ draw hdraw
      have hwrite : optionWriteBit draw.action = none := hspec.1.symm.trans hd
      have hterminal := historyAllowsAction_unwritten_terminal history stage draw.action hc hw hspec.2 hwrite hallow
      rcases hterminal with hs | ha
      · exact Or.inl (by simp only [overlayRule, hraw', hs, reserialAction, historyAllowsAction, ↓reduceIte])
      · exact Or.inr (by simp only [overlayRule, hraw', ha, reserialAction, historyAllowsAction, ↓reduceIte])
    · exact Or.inr (by simp only [overlayRule, hraw', hallow, ↓reduceIte])

theorem overlay_none_record_observables (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0)
    (hnone : (simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed s.history))).decision = none) :
    P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage = none ∧
      P.paidRunReviewCount fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage = 0 := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  obtain ⟨k, _hk, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) (seed, world) start
  have hprefix : Prefix input C.val .uncapped accounting actual seed (input.truthAt world) (worldTapes input world) k s := hs0 ▸ hp
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
  have ht := overlayRule_prewrite_none_terminal P fee hfee source seed s.history stage hhh hhc hhw hnone
  have hwitness : ∃ abandon : Bool,
      run input C.val .uncapped accounting actual (seed, world) (start + 1) = stopState s abandon := by
    rcases ht with hstop | habandon
    · refine ⟨false, ?_⟩
      apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) start _
      · exact (congrArg State.halted hs0).trans ha
      · rw [hs0]
        have hsaction : actual seed s.history = .stop := hstop
        rw [hsaction]
        exact .stop s ha
    · refine ⟨true, ?_⟩
      apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) start _
      · exact (congrArg State.halted hs0).trans ha
      · rw [hs0]
        have hsaction : actual seed s.history = .abandon := habandon
        rw [hsaction]
        exact .abandon s ha
  obtain ⟨abandon, hhalt⟩ := hwitness
  apply actualStageObservables_of_halted_unwritten P fee hfee C .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) (seed, world) (start + 1) stage 0
  · rw [hhalt]; rfl
  · rw [hhalt]; exact hw
  · rw [hhalt]; exact hr


end Native016

section Native017

variable {Seed : Type u} [MeasurableSpace Seed]

/-- Every entered record is implemented by the actual Native MAP script.
The sole pointwise condition is the all-record finite-test event, which is
independently almost sure under every probability seed law. -/
theorem overlayStage_pointwise (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (coins : Bool × Bool), ∃ n : ℕ,
      (P.overlayRecordTest fee hfee record).rule.stop coins (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    ∀ stage entry,
      entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage (seed, world) = some entry →
      let record := (overlayData P source).record seed stage entry
      match record.decision with
      | none => P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage = none ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage = 0
      | some _ =>
          let test := P.overlayRecordTest fee hfee record
          let coins := overlaySeedCoins P seed stage record
          let tape := worldTapes (P.input fee hfee) world stage
          ∃ n : ℕ, test.rule.stop coins tape = (n : ℕ∞) ∧
            P.paidRunReviewCount fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage = (n : ℕ∞) ∧
            P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) (seed, world) stage =
              some (test.rule.decision coins tape) ∧
            (if test.rule.decision coins tape then 0 ≤ P.binarySymmetric.experiment.logOddsScore tape n
             else P.binarySymmetric.experiment.logOddsScore tape n ≤ 0) := by
  intro stage entry he
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨start, hc, hbefore, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage (seed, world) entry).mp he
  let s := run input C.val .uncapped accounting actual (seed, world) start
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start (seed, world) := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl (seed, world) stage.val start he'
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨k, _hk, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) start
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual seed _ _ hp stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  let record := (overlayData P source).record seed stage entry
  have hrecord : record = simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed s.history)) := by
    change simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed entry)) = _
    rw [hh]
  change match record.decision with | none => _ | some decision => _
  cases hd : record.decision with
  | none =>
    have hn : (simulatorDrawRecord (overlaySeedDraw P source seed stage
        (overlayShadow P source seed s.history))).decision = none := hrecord ▸ hd
    exact overlay_none_record_observables P fee hfee C accounting source seed world start s stage rfl ha hc hw hr hn
  | some decision =>
    cases hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed s.history) with
    | none =>
      have hnone : record.decision = none := by
        rw [hrecord, hdraw]
        rfl
      rw [hnone] at hd
      cases hd
    | some draw =>
      have hrec : record = draw.record := by
        rw [hrecord, hdraw]
        rfl
      have hd' : draw.record.decision = some decision := hrec ▸ hd
      obtain ⟨n, hn⟩ := hfinite stage draw.record (overlaySeedCoins P seed stage draw.record)
      have hobs := overlay_writing_record_observables_at_stop P fee hfee C accounting source seed world start s stage draw decision
        rfl ha hc hw hr ho hdraw hd' n hn
      have hmap := PaperProofs.Statistics.PDROC.adjacentMixtureTest_map P.binarySymmetric
        (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee draw.record) (P.overlayRecordTarget_pos fee hfee draw.record))
        (overlaySeedCoins P seed stage draw.record) (worldTapes input world stage) n hn
      change ∃ n : ℕ, (P.overlayRecordTest fee hfee record).rule.stop (overlaySeedCoins P seed stage record)
          (worldTapes input world stage) = (n : ℕ∞) ∧
        P.paidRunReviewCount fee hfee C .uncapped accounting actual (seed, world) stage = (n : ℕ∞) ∧
        P.actualOrdinaryDecision fee hfee C .uncapped accounting actual (seed, world) stage =
          some ((P.overlayRecordTest fee hfee record).rule.decision (overlaySeedCoins P seed stage record)
            (worldTapes input world stage)) ∧
        (if (P.overlayRecordTest fee hfee record).rule.decision (overlaySeedCoins P seed stage record)
            (worldTapes input world stage) then
          0 ≤ P.binarySymmetric.experiment.logOddsScore (worldTapes input world stage) n
         else P.binarySymmetric.experiment.logOddsScore (worldTapes input world stage) n ≤ 0)
      rw [hrec]
      exact ⟨n, hn, hobs.2, hobs.1, hmap⟩


end Native017

section Native018

variable {Seed : Type u} [MeasurableSpace Seed]

/-- Full record-aware D14 StageRealization for the actual controller, with
ANY source rule and ANY probability seed law. Neither finite source cost,
entry-law correctness, MAP source decisions nor finite-ET is assumed. -/
theorem overlayStageRealization (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure (OverlaySeed P Seed)) [IsProbabilityMeasure ν] :
    OverlayDraft.OverlayStageRealization P fee hfee C accounting ν (overlayRule P fee hfee source)
      (overlayData P source) := by
  filter_upwards [allOverlayTests_finite_seededWorld P fee hfee ν] with sample hs
  exact overlayStage_pointwise P fee hfee C accounting source sample.1 sample.2 hs


end Native018

end PDROC
