module

public import PaperProofs.Common.NativeObservedWords
public import PaperProofs.Common.NativeTestingKernel
public import PaperProofs.Statistics.ReferenceBudgets
public import PaperProofs.Structure.RankEvaluator
public import PaperProofs.Structure.UsedGame

/-!
Finite early-history replay for the original reference budget. The rank case is
computed on the tools present at stage entry. No correctness or performance
assertion is stored in the parser data. The complete reference rule, its Native
Prefix alignment, and its global risk theorem are separate obligations.
In particular, the global one-report-per-stage and entry-snapshot alignment
with real Native prefixes remain unproved. Bounds on histories accepted by
this finite grammar are not asserted as a realized controller guarantee.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

/-- The executable general-graph evaluator. No complexity claim is made here. -/
def referenceRankAt (I : Instance) (cursor : Fin (I.stageCount + 1)) (used : Finset I.Tool) : ℕ∞ :=
  genericRank (I.compatibility.drop cursor.val) (Finset.univ \ used)

def referenceRepairTool (I : Instance) (stage : I.Stage) (used : Finset I.Tool) : Option I.Tool :=
  pickGenericMaxRankTool I.toolCount (I.eligible stage)
    (I.compatibility.drop (stage.val + 1)) (Finset.univ \ used)

def referenceBadRank (I : Instance) (stage : I.Stage) (used : Finset I.Tool) : ℕ∞ :=
  match referenceRepairTool I stage used with
  | none => 0
  | some tool => referenceRankAt I
      ⟨stage.val + 1, by have h := stage.isLt; change stage.val + 1 < I.compatibility.length + 1; omega⟩ (insert tool used)

def referenceCaseOfRanks (current bad : ℕ∞) : Option ReferenceBudgetCase :=
  if current = ⊤ then some .infiniteRank else
  if bad = 0 then some .noTool else
  if hpos : 0 < bad.toNat then some (.finiteBad ⟨bad.toNat, hpos⟩) else none

def referenceRankCase (I : Instance) (stage : I.Stage) (entryUsed : Finset I.Tool) : Option ReferenceBudgetCase :=
  referenceCaseOfRanks
    (referenceRankAt I ⟨stage.val, by have h := stage.isLt; change stage.val < I.compatibility.length + 1; omega⟩ entryUsed)
    (referenceBadRank I stage entryUsed)

theorem referenceRankAt_eq (I : Instance) (cursor : Fin (I.stageCount + 1)) (used : Finset I.Tool) :
    referenceRankAt I cursor used = errorRank (I.compatibility.drop cursor.val) (Finset.univ \ used) :=
  genericRank_eq_errorRank _ _

theorem referenceBadRank_eq (I : Instance) (stage : I.Stage) (used : Finset I.Tool) :
    referenceBadRank I stage used =
      badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) (Finset.univ \ used) := by
  unfold referenceBadRank
  cases hpick : referenceRepairTool I stage used with
  | none =>
    have hempty := (pickGenericMaxRankTool_eq_none I.toolCount (I.eligible stage)
      (I.compatibility.drop (stage.val + 1)) (Finset.univ \ used)).mp hpick
    exact ((badChildRank_eq_zero_iff _ _ _).mpr hempty).symm
  | some tool =>
    dsimp only
    rw [referenceRankAt_eq I]
    simpa only [remaining_after_used_insert] using (pickGenericMaxRankTool_spec I.toolCount (I.eligible stage)
      (I.compatibility.drop (stage.val + 1)) (Finset.univ \ used) tool hpick).2

theorem referenceBadRank_top_implies_current_top (I : Instance)
    (stage : I.Stage) (used : Finset I.Tool)
    (hbad : referenceBadRank I stage used = ⊤) :
    referenceRankAt I ⟨stage.val, by have h := stage.isLt; change stage.val < I.compatibility.length + 1; omega⟩ used = ⊤ := by
  rw [referenceRankAt_eq I, referenceBadRank_eq I] at *
  have hgood : errorRank (I.compatibility.drop (stage.val + 1)) (Finset.univ \ used) = ⊤ := by
    apply top_le_iff.mp
    rw [← hbad]
    exact badChildRank_le_goodRank _ _ _
  rw [List.drop_eq_getElem_cons stage.isLt]
  exact (errorRank_cons_eq_top_iff _ _ _).mpr ⟨hgood, hbad⟩

theorem referenceCaseOfRanks_exists (current bad : ℕ∞) (htop : bad = ⊤ → current = ⊤) :
    ∃ kind, referenceCaseOfRanks current bad = some kind := by
  by_cases hc : current = ⊤
  · exact ⟨.infiniteRank, by simp [referenceCaseOfRanks, hc]⟩
  by_cases hb : bad = 0
  · exact ⟨.noTool, by simp [referenceCaseOfRanks, hc, hb]⟩
  have hfinite : bad ≠ ⊤ := fun h => hc (htop h)
  obtain ⟨depth, hdepth⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hpositive : 0 < depth := by
    have hne : depth ≠ 0 := by intro h; subst depth; exact hb hdepth.symm
    omega
  refine ⟨.finiteBad ⟨depth, hpositive⟩, ?_⟩
  rw [referenceCaseOfRanks, ite_eq_right hc, ite_eq_right hb]
  simp only [← hdepth, ENat.toNat_natCast, hpositive, dite_true]

theorem referenceRankCase_exists (I : Instance) (stage : I.Stage) (used : Finset I.Tool) :
    ∃ kind, referenceRankCase I stage used = some kind :=
  referenceCaseOfRanks_exists _ _ (referenceBadRank_top_implies_current_top I stage used)

theorem referenceCaseOfRanks_infinite_iff (current bad : ℕ∞) :
    referenceCaseOfRanks current bad = some .infiniteRank ↔ current = ⊤ := by
  unfold referenceCaseOfRanks
  split_ifs <;> simp_all

theorem referenceCaseOfRanks_noTool_iff (current bad : ℕ∞) :
    referenceCaseOfRanks current bad = some .noTool ↔ current ≠ ⊤ ∧ bad = 0 := by
  unfold referenceCaseOfRanks
  split_ifs <;> simp_all

theorem referenceCaseOfRanks_finite_spec (current bad : ℕ∞) (depth : ℕ+)
    (hcase : referenceCaseOfRanks current bad = some (.finiteBad depth)) :
    current ≠ ⊤ ∧ bad = (depth.val : ℕ∞) := by
  unfold referenceCaseOfRanks at hcase
  split_ifs at hcase with hc hb hp
  · cases hcase
  · cases hcase
  · have hdepth : (⟨bad.toNat, hp⟩ : ℕ+) = depth := ReferenceBudgetCase.finiteBad.inj (Option.some.inj hcase)
    have hfinite : bad ≠ ⊤ := by intro h; rw [h] at hp; simp at hp
    have hval : bad.toNat = depth.val := congrArg PNat.val hdepth
    refine ⟨hc, ?_⟩
    rw [← hval, ENat.natCast_toNat hfinite]

theorem referenceRankCase_semantics (I : Instance) (stage : I.Stage) (entryUsed : Finset I.Tool) (kind : ReferenceBudgetCase)
    (hcase : referenceRankCase I stage entryUsed = some kind) :
    match kind with
    | .infiniteRank => errorRank (I.compatibility.drop stage.val) (Finset.univ \ entryUsed) = ⊤
    | .noTool => errorRank (I.compatibility.drop stage.val) (Finset.univ \ entryUsed) ≠ ⊤ ∧
        I.eligible stage ∩ (Finset.univ \ entryUsed) = ∅
    | .finiteBad depth => errorRank (I.compatibility.drop stage.val) (Finset.univ \ entryUsed) ≠ ⊤ ∧
        badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) (Finset.univ \ entryUsed) = depth.val := by
  cases kind with
  | infiniteRank =>
    have h := (referenceCaseOfRanks_infinite_iff _ _).mp hcase
    simpa only [referenceRankAt_eq I] using h
  | noTool =>
    have h := (referenceCaseOfRanks_noTool_iff _ _).mp hcase
    refine ⟨?_, ?_⟩
    · simpa only [referenceRankAt_eq I] using h.1
    · apply (badChildRank_eq_zero_iff _ _ _).mp
      simpa only [referenceBadRank_eq I] using h.2
  | finiteBad depth =>
    have h := referenceCaseOfRanks_finite_spec _ _ depth hcase
    exact ⟨by simpa only [referenceRankAt_eq I] using h.1,
      by simpa only [referenceBadRank_eq I] using h.2⟩

inductive ReferenceReplayPhase (I : Instance) where
  | testing
  | written
  | reported
  | allocated (tool : I.Tool)
  | executed (tool : I.Tool)
  deriving DecidableEq

/-- Public computation data only. `entryHistory` is updated exclusively on an
accepted advanced event; an allocation never changes that snapshot. -/
structure ReferenceReplayCache (I : Instance) where
  seen : List (VisibleEvent I)
  entryHistory : List (VisibleEvent I)
  events : List ReferenceBudgetEvent
  phase : ReferenceReplayPhase I
  halted : Bool

def referenceReplayInitial (I : Instance) : ReferenceReplayCache I :=
  ⟨[], [], [], .testing, false⟩

def referenceReplayStage (I : Instance) (cache : ReferenceReplayCache I) : Option I.Stage :=
  if h : historyCursor cache.seen < I.stageCount then some ⟨historyCursor cache.seen, h⟩ else none

def referenceReplayKind (I : Instance) (cache : ReferenceReplayCache I) : Option ReferenceBudgetCase := do
  let stage ← referenceReplayStage I cache
  referenceRankCase I stage (historyUsed cache.entryHistory)

def referenceReplayRisk (risk : ℚ) (cache : ReferenceReplayCache I) : Option ℚ :=
  referenceBudgetPath (risk / 2) cache.events

def referenceCacheTarget (I : Instance) (risk : ℚ) (cache : ReferenceReplayCache I) : Option ℚ := do
  if cache.halted || decide (cache.phase ≠ .testing) then none else do
  let kind ← referenceReplayKind I cache
  let current ← referenceReplayRisk risk cache
  if 0 < current ∧ current ≤ 1 / 4 ∧ cache.events.length ≤ I.stageCount then
    referenceBudgetTarget kind current else none

def referenceReplayMismatch (cache : ReferenceReplayCache I) (stage : I.Stage) (handle : MismatchHandle I) : Bool :=
  match historyWrite cache.seen stage, historyReport cache.seen stage with
  | some (bit, serial), some (truth, reportedSerial) =>
    decide (bit ≠ truth ∧ handle.stage = stage ∧ handle.writeSerial = serial ∧ reportedSerial = serial)
  | _, _ => false

def referenceReplayCorrect (cache : ReferenceReplayCache I) (stage : I.Stage) : Bool :=
  match historyWrite cache.seen stage, historyReport cache.seen stage with
  | some (bit, serial), some (truth, reportedSerial) => decide (bit = truth ∧ reportedSerial = serial)
  | _, _ => false

def referenceReplayStep (input : StatisticalInput I) (risk : ℚ)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) : Option (ReferenceReplayCache I) :=
  if cache.halted then none else
  let recorded := { cache with seen := cache.seen ++ [event] }
  match event with
  | .observation i symbol => do
    let stage ← referenceReplayStage I cache
    if i = stage ∧ symbol < (input.experiment i).alphabetSize ∧ cache.phase = .testing ∧
        (referenceCacheTarget I risk cache).isSome then some recorded else none
  | .wrote i _ serial => do
    let stage ← referenceReplayStage I cache
    let _kind ← referenceReplayKind I cache
    let _current ← referenceReplayRisk risk cache
    if i = stage ∧ serial = (historyActions cache.seen).length ∧ cache.phase = .testing then
      some { recorded with phase := .written } else none
  | .report i truth serial => do
    let stage ← referenceReplayStage I cache
    let written ← historyWrite cache.seen stage
    let kind ← referenceReplayKind I cache
    let _current ← referenceReplayRisk risk cache
    if i = stage ∧ serial = written.2 ∧ cache.phase = .written ∧ cache.events.length < I.stageCount then
      some { recorded with events := cache.events ++ [(kind, decide (written.1 ≠ truth))], phase := .reported }
    else none
  | .committed handle tool => do
    let stage ← referenceReplayStage I cache
    let _current ← referenceReplayRisk risk cache
    if cache.phase = .reported ∧ referenceReplayMismatch cache stage handle ∧
        tool ∈ I.eligible stage ∧ tool ∉ historyUsed cache.seen ∧
        referenceRepairTool I stage (historyUsed cache.entryHistory) = some tool then
      some { recorded with phase := .allocated tool } else none
  | .executed handle tool => do
    let stage ← referenceReplayStage I cache
    if cache.phase = .allocated tool ∧ referenceReplayMismatch cache stage handle then
      some { recorded with phase := .executed tool } else none
  | .advanced i => do
    let stage ← referenceReplayStage I cache
    let _current ← referenceReplayRisk risk cache
    if i = stage ∧ ((cache.phase = .reported ∧ referenceReplayCorrect cache stage) ∨
        ∃ tool, cache.phase = .executed tool) then
      some { recorded with entryHistory := recorded.seen, phase := .testing } else none
  | .stopped =>
    if historyCursor cache.seen = I.stageCount ∧ cache.phase = .testing then
      some { recorded with halted := true } else none
  | .abandoned =>
    if cache.phase ≠ .written then some { recorded with halted := true } else none

/-- A finite syntax checker, including complete early-write/report packets.
The final bounds are executable checks on computed data, never input fields. -/
def referenceReplay (input : StatisticalInput I) (risk : ℚ) (history : List (VisibleEvent I)) :
    Option (ReferenceReplayCache I) := do
  if 0 < risk ∧ risk ≤ 1 / 2 then pure () else none
  let cache ← history.foldlM (referenceReplayStep input risk) (referenceReplayInitial I)
  if cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history then some cache else none

def referenceEntryTarget (input : StatisticalInput I) (risk : ℚ) (history : List (VisibleEvent I)) : Option ℚ := do
  let cache ← referenceReplay input risk history
  referenceCacheTarget I risk cache

theorem measurable_referenceEntryTarget (input : StatisticalInput I) (risk : ℚ) :
    Measurable (referenceEntryTarget input risk) :=
  measurable_of_countable _

theorem referenceCacheTarget_some_spec (I : Instance) (risk target : ℚ) (cache : ReferenceReplayCache I)
    (htarget : referenceCacheTarget I risk cache = some target) :
    ∃ kind current, referenceReplayKind I cache = some kind ∧
      referenceReplayRisk risk cache = some current ∧ ReferenceBudgetValid current ∧
      cache.events.length ≤ I.stageCount ∧ referenceBudgetTarget kind current = some target := by
  cases hblocked : cache.halted || decide (cache.phase ≠ .testing) with
  | true =>
    simp only [referenceCacheTarget, hblocked, ite_true] at htarget
    cases htarget
  | false =>
    simp only [referenceCacheTarget, hblocked, Bool.false_eq_true, ite_false] at htarget
    obtain ⟨kind, hkind, hrest⟩ := Option.bind_eq_some_iff.mp htarget
    obtain ⟨current, hcurrent, hrest⟩ := Option.bind_eq_some_iff.mp hrest
    by_cases hv : 0 < current ∧ current ≤ 1 / 4 ∧ cache.events.length ≤ I.stageCount
    · simp only [hv] at hrest
      exact ⟨kind, current, hkind, hcurrent, ⟨hv.1, hv.2.1⟩, hv.2.2, hrest⟩
    · simp only [hv, ite_false] at hrest
      cases hrest

theorem referenceCacheTarget_bounds (I : Instance) (risk target : ℚ) (hrisk : 0 < risk)
    (hsmall : risk ≤ 1 / 2) (cache : ReferenceReplayCache I)
    (htarget : referenceCacheTarget I risk cache = some target) :
    0 < target ∧ target ≤ 1 / 4 ∧ risk / referenceQuotaConstant I.stageCount ≤ target := by
  obtain ⟨kind, current, _, hpath, hv, hlen, ht⟩ := referenceCacheTarget_some_spec I risk target cache htarget
  have hvalid := referenceBudgetTarget_valid_floor kind current target hv ht
  refine ⟨hvalid.1, hvalid.2.1, ?_⟩
  exact referenceBudgetPath_original_target_floor risk hrisk hsmall cache.events I.stageCount hlen current target hpath kind ht

theorem referenceEntryTarget_bounds (input : StatisticalInput I) (risk target : ℚ) (hrisk : 0 < risk)
    (hsmall : risk ≤ 1 / 2) (history : List (VisibleEvent I))
    (htarget : referenceEntryTarget input risk history = some target) :
    0 < target ∧ target ≤ 1 / 4 ∧ risk / referenceQuotaConstant I.stageCount ≤ target := by
  obtain ⟨cache, _, ht⟩ := Option.bind_eq_some_iff.mp htarget
  exact referenceCacheTarget_bounds I risk target hrisk hsmall cache ht

theorem referenceReplay_some_spec (input : StatisticalInput I) (risk : ℚ) (history : List (VisibleEvent I))
    (cache : ReferenceReplayCache I) (hparse : referenceReplay input risk history = some cache) :
    (0 < risk ∧ risk ≤ 1 / 2) ∧
      history.foldlM (referenceReplayStep input risk) (referenceReplayInitial I) = some cache ∧
      cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history := by
  by_cases hr : 0 < risk ∧ risk ≤ 1 / 2
  · simp only [referenceReplay, hr] at hparse
    obtain ⟨result, hfold, hlast⟩ := Option.bind_eq_some_iff.mp hparse
    by_cases hg : result.phase ≠ .written ∧ result.events.length ≤ I.stageCount ∧
        historyCursor result.seen ≤ I.stageCount ∧ result.seen = history
    · rw [ite_eq_left hg] at hlast
      have heq := Option.some.inj hlast
      subst result
      exact ⟨hr, hfold, hg⟩
    · rw [ite_eq_right hg] at hlast
      cases hlast
  · simp only [referenceReplay, hr, ite_false] at hparse
    cases hparse

theorem referenceReplay_risk_bounds (input : StatisticalInput I) (risk current : ℚ)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : referenceReplay input risk history = some cache)
    (hcurrent : referenceReplayRisk risk cache = some current) :
    ReferenceBudgetValid current ∧ risk / (2 : ℚ) ^ (I.stageCount + 1) ≤ current := by
  have hs := referenceReplay_some_spec input risk history cache hparse
  have hv : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  exact ⟨(referenceBudgetPath_valid_floor cache.events (risk / 2) current hv hcurrent).1,
    referenceBudgetPath_original_floor risk hs.1.1 hs.1.2 cache.events I.stageCount hs.2.2.2.1 current hcurrent⟩

private theorem historyCursor_append_observation (history : List (VisibleEvent I)) (stage : I.Stage) (symbol : ℕ) :
    historyCursor (history ++ [.observation stage symbol]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, eventAdvance]

theorem referenceCacheTarget_observation_append (I : Instance) (risk : ℚ) (cache : ReferenceReplayCache I)
    (stage : I.Stage) (symbol : ℕ) :
    referenceCacheTarget I risk { cache with seen := cache.seen ++ [.observation stage symbol] } =
      referenceCacheTarget I risk cache := by
  simp only [referenceCacheTarget, referenceReplayKind, referenceReplayStage, referenceReplayRisk,
    historyCursor_append_observation]

theorem referenceReplayStep_observation_spec (input : StatisticalInput I) (risk : ℚ)
    (cache result : ReferenceReplayCache I) (stage : I.Stage) (symbol : ℕ)
    (hstep : referenceReplayStep input risk cache (.observation stage symbol) = some result) :
    result = { cache with seen := cache.seen ++ [.observation stage symbol] } ∧
      referenceCacheTarget I risk result = referenceCacheTarget I risk cache := by
  cases hh : cache.halted with
  | true =>
    simp only [referenceReplayStep, hh, ite_true] at hstep
    cases hstep
  | false =>
    simp only [referenceReplayStep, hh, Bool.false_eq_true, ite_false] at hstep
    obtain ⟨current, _, hguard⟩ := Option.bind_eq_some_iff.mp hstep
    by_cases hg : stage = current ∧ symbol < (input.experiment stage).alphabetSize ∧ cache.phase = .testing ∧
        (referenceCacheTarget I risk cache).isSome
    · rw [ite_eq_left hg] at hguard
      have heq := (Option.some.inj hguard).symm
      subst result
      exact ⟨rfl, by simpa only [hh] using referenceCacheTarget_observation_append I risk cache stage symbol⟩
    · rw [ite_eq_right hg] at hguard
      cases hguard

/-- An accepted budget event uses the visible ordinary write and matching old
serial. Its rank case is computed from the saved entry snapshot. -/
theorem referenceReplayStep_report_spec (input : StatisticalInput I) (risk : ℚ)
    (cache result : ReferenceReplayCache I) (i : I.Stage) (truth : Bool) (serial : ℕ)
    (hstep : referenceReplayStep input risk cache (.report i truth serial) = some result) :
    ∃ (stage : I.Stage) (written : Bool × ℕ) (kind : ReferenceBudgetCase) (current : ℚ),
      referenceReplayStage I cache = some stage ∧ historyWrite cache.seen stage = some written ∧
      referenceRankCase I stage (historyUsed cache.entryHistory) = some kind ∧
      referenceReplayRisk risk cache = some current ∧
      i = stage ∧ serial = written.2 ∧ cache.phase = .written ∧ cache.events.length < I.stageCount ∧
      result.events = cache.events ++ [(kind, decide (written.1 ≠ truth))] ∧
      result.entryHistory = cache.entryHistory ∧ result.phase = .reported := by
  cases hh : cache.halted with
  | true =>
    simp only [referenceReplayStep, hh, ite_true] at hstep
    cases hstep
  | false =>
    simp only [referenceReplayStep, hh, Bool.false_eq_true, ite_false] at hstep
    obtain ⟨stage, hstage, hrest⟩ := Option.bind_eq_some_iff.mp hstep
    obtain ⟨written, hwrite, hrest⟩ := Option.bind_eq_some_iff.mp hrest
    obtain ⟨kind, hkind, hrest⟩ := Option.bind_eq_some_iff.mp hrest
    obtain ⟨current, hcurrent, hrest⟩ := Option.bind_eq_some_iff.mp hrest
    by_cases hg : i = stage ∧ serial = written.2 ∧ cache.phase = .written ∧ cache.events.length < I.stageCount
    · rw [ite_eq_left hg] at hrest
      have heq := (Option.some.inj hrest).symm
      subst result
      have hk : referenceRankCase I stage (historyUsed cache.entryHistory) = some kind := by
        simpa [referenceReplayKind, hstage] using hkind
      exact ⟨stage, written, kind, current, hstage, hwrite, hk, hcurrent,
        hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, rfl, rfl, rfl⟩
    · rw [ite_eq_right hg] at hrest
      cases hrest

theorem referenceReplay_append_observation (input : StatisticalInput I) (risk : ℚ)
    (history : List (VisibleEvent I)) (cache result : ReferenceReplayCache I) (stage : I.Stage) (symbol : ℕ)
    (hparse : referenceReplay input risk history = some cache)
    (hstep : referenceReplayStep input risk cache (.observation stage symbol) = some result) :
    referenceReplay input risk (history ++ [.observation stage symbol]) = some result := by
  have hs := referenceReplay_some_spec input risk history cache hparse
  have hresult := (referenceReplayStep_observation_spec input risk cache result stage symbol hstep).1
  have hfold : (history ++ [VisibleEvent.observation stage symbol]).foldlM (referenceReplayStep input risk)
      (referenceReplayInitial I) = some result := by
    rw [List.foldlM_append, hs.2.1]
    simpa using hstep
  have hg : result.phase ≠ .written ∧ result.events.length ≤ I.stageCount ∧
      historyCursor result.seen ≤ I.stageCount ∧ result.seen = history ++ [.observation stage symbol] := by
    rw [hresult]
    exact ⟨hs.2.2.1, hs.2.2.2.1, by simpa only [historyCursor_append_observation] using hs.2.2.2.2.1,
      congrArg (fun seen => seen ++ [.observation stage symbol]) hs.2.2.2.2.2⟩
  simp only [referenceReplay, hs.1]
  rw [hfold]
  exact ite_eq_left hg

/-- An accepted review does not recalculate the entry rank, change the risk,
or move the chosen target. This is an equality of the actual history chooser. -/
theorem referenceEntryTarget_observation_invariant (input : StatisticalInput I) (risk : ℚ)
    (history : List (VisibleEvent I)) (cache result : ReferenceReplayCache I) (stage : I.Stage) (symbol : ℕ)
    (hparse : referenceReplay input risk history = some cache)
    (hstep : referenceReplayStep input risk cache (.observation stage symbol) = some result) :
    referenceEntryTarget input risk (history ++ [.observation stage symbol]) =
      referenceEntryTarget input risk history := by
  have hnext := referenceReplay_append_observation input risk history cache result stage symbol hparse hstep
  simp only [referenceEntryTarget, hnext, hparse]
  exact (referenceReplayStep_observation_spec input risk cache result stage symbol hstep).2

end PaperProofs.Common.Native
