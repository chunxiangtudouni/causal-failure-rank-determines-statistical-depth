module
public import PaperProofs.Paid.PDROC_OverlayEntry_001
public import PaperProofs.Paid.PDROC_OverlayFresh_002
public import PaperProofs.Paid.PDROC_OverlayFresh_003
public import PaperProofs.Paid.PDROC_OverlaySimulator_009
public import PaperProofs.Common.NativeCausality
public import PaperProofs.Common.HistorySuffixRun
public import PaperProofs.Paid.PDROC_SimulatorLaw_004
set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
namespace PDROC

section EntryPart2


universe u
variable {Seed : Type u}

/-- Current-stage replacement preserves only the old seed and off-target
auxiliary tapes and mark rows; the target tape and row may both vary. -/
def OverlaySeedAgreeOff (P : Parameters) (target : P.sharedInstance.Stage)
    (seedA seedB : OverlaySeed P Seed) : Prop :=
  seedA.1 = seedB.1 ∧ ∀ stage : P.sharedInstance.Stage, stage ≠ target →
    seedA.2.1 stage = seedB.2.1 stage ∧ seedA.2.2 stage = seedB.2.2 stage

theorem OverlaySeedAgreeOff.symm {P : Parameters} {target : P.sharedInstance.Stage}
    {seedA seedB : OverlaySeed P Seed} (h : OverlaySeedAgreeOff P target seedA seedB) :
    OverlaySeedAgreeOff P target seedB seedA :=
  ⟨h.1.symm, fun stage hs => ⟨(h.2 stage hs).1.symm, (h.2 stage hs).2.symm⟩⟩

theorem overlaySeedDraw_eq_seed_off (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : OverlaySeed P Seed)
    (hseed : OverlaySeedAgreeOff P target seedA seedB) (stage : P.sharedInstance.Stage)
    (hne : stage ≠ target) (entry : List (VisibleEvent P.sharedInstance)) :
    overlaySeedDraw P source seedA stage entry = overlaySeedDraw P source seedB stage entry := by
  simp only [overlaySeedDraw, hseed.1, (hseed.2 stage hne).1]

theorem overlaySeedMark_eq_seed_off (P : Parameters) (target : P.sharedInstance.Stage)
    (seedA seedB : OverlaySeed P Seed) (hseed : OverlaySeedAgreeOff P target seedA seedB)
    (stage : P.sharedInstance.Stage) (hne : stage ≠ target) (record : AuxiliaryRecord) :
    overlaySeedMark P seedA stage record = overlaySeedMark P seedB stage record := by
  simp only [overlaySeedMark, (hseed.2 stage hne).2]

theorem overlaySeedCoins_eq_seed_off (P : Parameters) (target : P.sharedInstance.Stage)
    (seedA seedB : OverlaySeed P Seed) (hseed : OverlaySeedAgreeOff P target seedA seedB)
    (stage : P.sharedInstance.Stage) (hne : stage ≠ target) :
    overlaySeedCoins P seedA stage = overlaySeedCoins P seedB stage := by
  funext record
  simp only [overlaySeedCoins, (hseed.2 stage hne).2]

theorem overlaySeedGhost_eq_seed_off (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : OverlaySeed P Seed)
    (hseed : OverlaySeedAgreeOff P target seedA seedB) (cache : SimulatorCache P.sharedInstance) :
    overlaySeedGhost P source seedA cache = overlaySeedGhost P source seedB cache := by
  simp only [overlaySeedGhost, hseed.1]

theorem overlaySeedReplay_eq_seed_off (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : OverlaySeed P Seed)
    (hseed : OverlaySeedAgreeOff P target seedA seedB) (history : List (VisibleEvent P.sharedInstance))
    (hwrite : historyWritten history target = none)
    (hreport : historyReport history target = none) (hhalt : historyHalted history = false) :
    overlaySeedReplay P source seedA history = overlaySeedReplay P source seedB history := by
  apply overlayReplay_eq_before_target (overlaySeedDraw P source) (overlaySeedMark P)
    (overlaySeedGhost P source) seedA seedB target history
  · exact overlaySeedDraw_eq_seed_off P source target seedA seedB hseed
  · exact overlaySeedMark_eq_seed_off P target seedA seedB hseed
  · exact overlaySeedGhost_eq_seed_off P source target seedA seedB hseed
  · exact hwrite
  · exact hreport
  · exact hhalt

theorem overlayPostwriteAction_eq_seed_off (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : OverlaySeed P Seed)
    (hseed : OverlaySeedAgreeOff P target seedA seedB) (history : List (VisibleEvent P.sharedInstance))
    (cache : SimulatorCache P.sharedInstance) :
    overlayPostwriteAction P source seedA history cache = overlayPostwriteAction P source seedB history cache := by
  unfold overlayPostwriteAction
  rw [hseed.1, overlaySeedGhost_eq_seed_off P source target seedA seedB hseed cache]

theorem overlayCandidateAtCache_eq_seed_off (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : OverlaySeed P Seed) (hseed : OverlaySeedAgreeOff P target seedA seedB)
    (history : List (VisibleEvent P.sharedInstance)) (cache : SimulatorCache P.sharedInstance)
    (hcursor : historyCursor history < target.val) :
    overlayCandidateAtCache P fee hfee source seedA history cache =
      overlayCandidateAtCache P fee hfee source seedB history cache := by
  by_cases hh : historyHalted history = true
  · simp only [overlayCandidateAtCache, hh, ite_true]
  · have hhfalse : historyHalted history = false := Bool.eq_false_iff.mpr hh
    simp only [overlayCandidateAtCache, hhfalse, Bool.false_eq_true, ↓reduceIte]
    cases hs : simulatorStageAt history with
    | none => exact overlayPostwriteAction_eq_seed_off P source target seedA seedB hseed history cache
    | some stage =>
      have hv : stage.val = historyCursor history := by
        unfold simulatorStageAt at hs
        split at hs
        next hg => exact congrArg Fin.val (Option.some.inj hs).symm
        next hg => cases hs
      have hne : stage ≠ target := by intro he; have := congrArg Fin.val he; omega
      dsimp only
      by_cases hw : historyWritten history stage = none
      · simp only [hw, ite_true]
        rw [overlaySeedCoins_eq_seed_off P target seedA seedB hseed stage hne,
          overlaySeedDraw_eq_seed_off P source target seedA seedB hseed stage hne cache.shadow]
      · simpa only [hw, ite_false] using
          overlayPostwriteAction_eq_seed_off P source target seedA seedB hseed history cache

theorem overlayRule_eq_seed_off (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : OverlaySeed P Seed) (hseed : OverlaySeedAgreeOff P target seedA seedB)
    (history : List (VisibleEvent P.sharedInstance)) (hcursor : historyCursor history < target.val)
    (hwrite : historyWritten history target = none)
    (hreport : historyReport history target = none) (hhalt : historyHalted history = false) :
    overlayRule P fee hfee source seedA history = overlayRule P fee hfee source seedB history := by
  have hc := overlaySeedReplay_eq_seed_off P source target seedA seedB hseed history hwrite hreport hhalt
  have ha : overlayCandidate P fee hfee source seedA history = overlayCandidate P fee hfee source seedB history := by
    unfold overlayCandidate
    rw [hc]
    exact overlayCandidateAtCache_eq_seed_off P fee hfee source target seedA seedB hseed history _ hcursor
  simp only [overlayRule, ha]

/-- The actual prefix supplies the target-report absence; it is not an added
source-policy restriction or a simulator invariant hypothesis. -/
theorem overlayRule_eq_seed_off_prefix (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : OverlaySeed P Seed) (hseed : OverlaySeedAgreeOff P target seedA seedB)
    {PrefixSeed : Type*} (actualRule : PolicyRule P.sharedInstance PrefixSeed)
    (actualSeed : PrefixSeed) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting actualRule actualSeed truth tapes n s)
    (ha : s.halted = false) (hcursor : s.cursor < target.val) :
    overlayRule P fee hfee source seedA s.history = overlayRule P fee hfee source seedB s.history := by
  have hc := prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting actualRule actualSeed truth tapes hp
  have hw := (prefix_cursorInvariant (P.input fee hfee) C.val .uncapped accounting actualRule actualSeed truth tapes hp).future_written target hcursor
  have hi := prefix_invariant (P.input fee hfee) C.val .uncapped accounting actualRule actualSeed truth tapes hp
  have hr : s.ledger.reportTime target = none := by
    cases hh : s.ledger.reportTime target with
    | none => rfl
    | some time => exact (hi.report_written target time hh hw).elim
  have hreport : historyReport s.history target = none := by
    rw [prefix_historyReport_early (P.input fee hfee) C.val C.property.1.1 .uncapped accounting actualRule actualSeed truth tapes hp,
      hr]
    rfl
  have hwrite : historyWritten s.history target = none :=
    (prefix_historyWritten (P.input fee hfee) C.val .uncapped accounting actualRule actualSeed truth tapes hp target).trans hw
  have hhalt : historyHalted s.history = false :=
    (prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting actualRule actualSeed truth tapes hp).trans ha
  exact overlayRule_eq_seed_off P fee hfee source target seedA seedB hseed s.history
    (by simpa only [hc] using hcursor) hwrite hreport hhalt


end EntryPart2

section EntryPart3

theorem overlayRun_eq_before_target {Seed : Type*}
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : OverlaySeed P Seed)
    (hseed : OverlaySeedAgreeOff P target seedA seedB) (world : (P.input fee hfee).World) (n : ℕ)
    (hbefore : ∀ k < n, (run (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) (seedA, world) k).cursor < target.val) :
    run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seedA, world) n =
      run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seedB, world) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
    by_cases hh : (run (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) (seedA, world) n).halted = true
    · rw [run_succ_of_halted (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
        (seedA, world) n hh,
        run_succ_of_halted (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
          (seedB, world) n (heq ▸ hh), heq]
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) (overlayRule_legal P fee hfee C accounting source) (seedA, world) n
      have haction := overlayRule_eq_seed_off_prefix P fee hfee C accounting source target
        seedA seedB hseed (overlayRule P fee hfee source) seedA (P.input fee hfee |>.truthAt world)
        (worldTapes (P.input fee hfee) world) hp ha (hbefore n (Nat.lt_succ_self n))
      simp only [run, ← heq, haction]

theorem overlayFirstEntry_transport_seed_off {Seed : Type*}
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (target : P.sharedInstance.Stage) (seedA seedB : OverlaySeed P Seed)
    (hseed : OverlaySeedAgreeOff P target seedA seedB) (world : (P.input fee hfee).World) (n : ℕ)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) target.val n (seedA, world)) :
    FirstEntryAt (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) target.val n (seedB, world) ∧
      run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seedA, world) n =
        run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seedB, world) n := by
  have hbefore := firstEntryAt_strictly_before (P.input fee hfee) C.val .uncapped accounting
    (overlayRule P fee hfee source) (overlayRule_legal P fee hfee C accounting source) (seedA, world) target.val n hentry
  have heq := overlayRun_eq_before_target P fee hfee C accounting source target seedA seedB hseed world n hbefore
  refine ⟨⟨?_, ?_⟩, heq⟩
  · simpa only [← heq] using hentry.1
  · intro k hk
    have hkEq := overlayRun_eq_before_target P fee hfee C accounting source target seedA seedB hseed world k
      (fun j hj => hbefore j (lt_trans hj hk))
    simpa only [← hkEq] using hentry.2 k hk



open MeasureTheory
universe u
variable {Seed : Type u}

noncomputable def overlayVirtualEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) : EntryHistory P.sharedInstance :=
  (entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample).map
    (overlayShadow P source sample.1)

set_option maxHeartbeats 800000 in
theorem measurable_overlayVirtualEntry [MeasurableSpace Seed] (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayVirtualEntry P fee hfee C accounting source stage) := by
  let build := fun pair : OverlaySeed P Seed × EntryHistory P.sharedInstance =>
    pair.2.map (overlayShadow P source pair.1)
  have hb : Measurable build := by
    apply measurable_from_prod_countable_left
    intro entry
    cases entry with
    | none => exact measurable_const
    | some history =>
      change Measurable (fun seed : OverlaySeed P Seed => some (overlayShadow P source seed history))
      have hjoint := measurable_overlayShadow P source hm
      have he : Measurable (fun seed : OverlaySeed P Seed => (seed, history)) :=
        measurable_id.prodMk measurable_const
      have hs := hjoint.comp he
      change Measurable (fun seed : OverlaySeed P Seed => overlayShadow P source seed history) at hs
      exact (measurable_of_countable (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp hs
  change Measurable (fun sample : OverlaySeed P Seed × (P.input fee hfee).World =>
    build (sample.1, entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample))
  have he := measurable_entryHistory (P.input fee hfee) C.val .uncapped accounting
    (overlayRule P fee hfee source) (measurable_overlayRule P fee hfee source hm) stage
  have hp := measurable_fst.prodMk he
  exact hb.comp hp

theorem overlayVirtualEntry_eq_seed_off (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : OverlaySeed P Seed) (hseed : OverlaySeedAgreeOff P target seedA seedB)
    (world : (P.input fee hfee).World) :
    overlayVirtualEntry P fee hfee C accounting source target (seedA, world) =
      overlayVirtualEntry P fee hfee C accounting source target (seedB, world) := by
  let input := P.input fee hfee
  let rule := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  cases he : entryHistory input C.val .uncapped accounting rule target (seedA, world) with
  | none =>
    have he' : entryHistory input C.val .uncapped accounting rule target (seedB, world) = none := by
      cases hb : entryHistory input C.val .uncapped accounting rule target (seedB, world) with
      | none => rfl
      | some history =>
        obtain ⟨n, hn, hbefore, _⟩ := (entryHistory_some_iff input C.val .uncapped accounting rule target (seedB, world) history).mp hb
        have ha := (overlayFirstEntry_transport_seed_off P fee hfee C accounting source target seedB seedA hseed.symm world n ⟨hn, hbefore⟩).1
        exact False.elim ((entryHistory_none_iff input C.val .uncapped accounting rule target (seedA, world)).mp he ⟨n, ha.1⟩)
    change (entryHistory input C.val .uncapped accounting rule target (seedA, world)).map (overlayShadow P source seedA) =
      (entryHistory input C.val .uncapped accounting rule target (seedB, world)).map (overlayShadow P source seedB)
    rw [he, he']
    rfl
  | some history =>
    obtain ⟨n, hn, hbefore, hhistory⟩ := (entryHistory_some_iff input C.val .uncapped accounting rule target (seedA, world) history).mp he
    have hentry : FirstEntryAt input C.val .uncapped accounting rule target.val n (seedA, world) := ⟨hn, hbefore⟩
    obtain ⟨hentryB, hruns⟩ := overlayFirstEntry_transport_seed_off P fee hfee C accounting source target seedA seedB hseed world n hentry
    have he' : entryHistory input C.val .uncapped accounting rule target (seedB, world) = some history := by
      apply (entryHistory_some_iff input C.val .uncapped accounting rule target (seedB, world) history).mpr
      exact ⟨n, hentryB.1, hentryB.2, hruns.symm ▸ hhistory⟩
    obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting rule hl (seedA, world) target.val n hentry
    obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting rule hl (seedA, world) n
    have hw : historyWritten history target = none := by
      rw [← hhistory, prefix_historyWritten input C.val .uncapped accounting rule seedA _ _ hp target]
      exact (hunborn target le_rfl).1
    have hh : historyHalted history = false := by
      rw [← hhistory, prefix_historyHalted input C.val .uncapped accounting rule seedA _ _ hp]
      exact ha
    have hfuture := (hunborn target le_rfl).1
    have hi := prefix_invariant input C.val .uncapped accounting rule seedA _ _ hp
    have htime : (run input C.val .uncapped accounting rule (seedA, world) n).ledger.reportTime target = none := by
      cases ht : (run input C.val .uncapped accounting rule (seedA, world) n).ledger.reportTime target with
      | none => rfl
      | some time => exact (hi.report_written target time ht hfuture).elim
    have hr : historyReport history target = none := by
      rw [← hhistory, prefix_historyReport_early input C.val C.property.1.1 .uncapped accounting rule seedA _ _ hp, htime]
      rfl
    have hcache := overlaySeedReplay_eq_seed_off P source target seedA seedB hseed history hw hr hh
    have hshadow : overlayShadow P source seedA history = overlayShadow P source seedB history :=
      congrArg SimulatorCache.shadow hcache
    change (entryHistory input C.val .uncapped accounting rule target (seedA, world)).map (overlayShadow P source seedA) =
      (entryHistory input C.val .uncapped accounting rule target (seedB, world)).map (overlayShadow P source seedB)
    rw [he, he']
    exact congrArg some hshadow



end EntryPart3

section EntryPart4


universe u
variable {Seed : Type u}

/-- A measurable proof representative fills the entire current-stage noise,
including its auxiliary tape. It is never sampled by the actual controller. -/
def overlayCompleteFullOther (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins)
    (past : (Seed × OverlayFullOtherNoise P OverlayStageCoins stage) × SimulatorOtherWorld P stage) :
    OverlaySeed P Seed × (P.input fee hfee).World :=
  ((past.1.1, ((fun i => if hi : i = stage then simulatorDummyTape P else past.1.2.1 ⟨i, hi⟩),
    fun i => if hi : i = stage then row else past.1.2.2 ⟨i, hi⟩)),
    fun i => if hi : i = stage then (false, simulatorDummyTape P) else past.2 ⟨i, hi⟩)

theorem measurable_overlayCompleteFullOther [MeasurableSpace Seed] (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :
    Measurable (overlayCompleteFullOther (Seed := Seed) P fee hfee stage row) := by
  have ht : Measurable (fun past : (Seed × OverlayFullOtherNoise P OverlayStageCoins stage) × SimulatorOtherWorld P stage =>
      fun i => if hi : i = stage then simulatorDummyTape P else past.1.2.1 ⟨i, hi⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [dite_eq_left hi]; exact measurable_const
    · simp only [dite_eq_right hi]; fun_prop
  have hr : Measurable (fun past : (Seed × OverlayFullOtherNoise P OverlayStageCoins stage) × SimulatorOtherWorld P stage =>
      fun i => if hi : i = stage then row else past.1.2.2 ⟨i, hi⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [dite_eq_left hi]; exact measurable_const
    · simp only [dite_eq_right hi]; fun_prop
  have hw : Measurable (fun past : (Seed × OverlayFullOtherNoise P OverlayStageCoins stage) × SimulatorOtherWorld P stage =>
      fun i => if hi : i = stage then (false, simulatorDummyTape P) else past.2 ⟨i, hi⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [dite_eq_left hi]; exact measurable_const
    · simp only [dite_eq_right hi]; fun_prop
  exact ((measurable_fst.comp measurable_fst).prodMk (ht.prodMk hr)).prodMk hw

noncomputable def overlayVirtualEntryGate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) : Seed × EntryHistory P.sharedInstance :=
  (sample.1.1, overlayVirtualEntry P fee hfee C accounting source stage sample)

noncomputable def overlayVirtualEntryFactor (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :=
  overlayVirtualEntryGate P fee hfee C accounting source stage ∘ overlayCompleteFullOther P fee hfee stage row

/-- The actual generated entry excludes ALL current-stage noise. This is a
pointwise conclusion for the actual guarded Native controller, not an assumption. -/
theorem overlayVirtualEntryGate_factorization (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (row : OverlayStageCoins)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    overlayVirtualEntryGate P fee hfee C accounting source stage sample =
      overlayVirtualEntryFactor P fee hfee C accounting source stage row
        (overlayFullAllOther P fee hfee stage sample) := by
  let completed := overlayCompleteFullOther P fee hfee stage row (overlayFullAllOther P fee hfee stage sample)
  have hseed : OverlaySeedAgreeOff P stage sample.1 completed.1 := by
    constructor
    · rfl
    · intro i hi
      constructor <;> simp only [completed, overlayCompleteFullOther, overlayFullAllOther,
        overlayFullOtherNoise, dite_eq_right hi]
  have hpast : ∀ i : P.sharedInstance.Stage, i.val < stage.val → completed.2 i = sample.2 i := by
    intro i hi
    have hne : i ≠ stage := by intro h; subst i; omega
    simp only [completed, overlayCompleteFullOther, overlayFullAllOther, dite_eq_right hne]
  have he := entryHistory_eq_of_past (P.input fee hfee) C.val .uncapped accounting
    (overlayRule P fee hfee source) (overlayRule_legal P fee hfee C accounting source)
    sample.1 sample.2 completed.2 stage hpast
  have hworld : overlayVirtualEntry P fee hfee C accounting source stage (sample.1, completed.2) =
      overlayVirtualEntry P fee hfee C accounting source stage sample :=
    congrArg (fun entry : EntryHistory P.sharedInstance => entry.map (overlayShadow P source sample.1)) he
  have hnoise := overlayVirtualEntry_eq_seed_off P fee hfee C accounting source stage sample.1 completed.1 hseed completed.2
  exact Prod.ext rfl (hworld.symm.trans hnoise)

/-- Full old-seed × entire virtual-entry law against the current auxiliary
tape, complete record-indexed mark row, and real truth/tape is a product.
No entry law, no MAP-source restriction, and no finite-ET premise is supplied. -/
theorem overlayVirtualEntry_joint_freshStage [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (rowLaw : Measure OverlayStageCoins) [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (overlayVirtualEntryGate P fee hfee C accounting source stage sample,
        overlayFullCurrent P fee hfee stage sample)) =
      ((overlayFullAllOtherLaw P fee hfee ν rowLaw stage).map
        (overlayVirtualEntryFactor P fee hfee C accounting source stage row)).prod
        (((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) := by
  have hg : Measurable (overlayVirtualEntryFactor P fee hfee C accounting source stage row) :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_overlayVirtualEntry P fee hfee C accounting source hm stage)).comp
        (measurable_overlayCompleteFullOther P fee hfee stage row)
  have h := overlayFullWorldLaw_pastGate P fee hfee ν rowLaw stage
    (overlayVirtualEntryFactor P fee hfee C accounting source stage row) hg
  have heq : (fun sample : OverlaySeed P Seed × (P.input fee hfee).World =>
      (overlayVirtualEntryGate P fee hfee C accounting source stage sample, overlayFullCurrent P fee hfee stage sample)) =
      (fun sample => (overlayVirtualEntryFactor P fee hfee C accounting source stage row
        (overlayFullAllOther P fee hfee stage sample), overlayFullCurrent P fee hfee stage sample)) := by
    funext sample
    rw [overlayVirtualEntryGate_factorization P fee hfee C accounting source stage row]
  rw [← heq] at h
  exact h


end EntryPart4

section EntryPart5


universe u
variable {Seed : Type u}

theorem overlayFullAllOther_replace_current (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) (world : Bool × P.experiment.Tape)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    overlayFullAllOther P fee hfee stage (overlayFreshReplace P fee hfee stage row world sample) =
      overlayFullAllOther P fee hfee stage sample := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext i
        simp only [overlayFullAllOther, overlayFullOtherNoise, overlayFreshReplace,
          i.property, ite_false]
  · funext i
    change (if i.val = stage then world else sample.2 i.val) = sample.2 i.val
    exact ite_eq_right i.property

/-- Actual entry invariance under the replacement used by Fresh002. -/
theorem overlayVirtualEntryGate_replace_current (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (representative : OverlayStageCoins) (row : OverlayStageCoins) (world : Bool × P.experiment.Tape)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    overlayVirtualEntryGate P fee hfee C accounting source stage
      (overlayFreshReplace P fee hfee stage row world sample) =
      overlayVirtualEntryGate P fee hfee C accounting source stage sample := by
  rw [overlayVirtualEntryGate_factorization P fee hfee C accounting source stage representative,
    overlayVirtualEntryGate_factorization P fee hfee C accounting source stage representative,
    overlayFullAllOther_replace_current]

/-- Select the genuine prewrite source draw at the actual virtual entry.
Outer none retains the never-entered and nonreturn branches honestly. -/
noncomputable def overlayCurrentDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) : Option (SimulatorDraw P.sharedInstance) :=
  (overlayVirtualEntry P fee hfee C accounting source stage sample).bind
    (fun entry => overlaySeedDraw P source sample.1 stage entry)

theorem measurable_overlayCurrentDraw [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayCurrentDraw P fee hfee C accounting source stage) := by
  let build := fun pair : OverlaySeed P Seed × EntryHistory P.sharedInstance =>
    pair.2.bind (fun entry => overlaySeedDraw P source pair.1 stage entry)
  have hb : Measurable build := by
    apply measurable_from_prod_countable_left
    intro entry
    cases entry with
    | none => exact measurable_const
    | some history =>
      exact (measurable_overlaySeedDraw P source hm stage).comp (measurable_id.prodMk measurable_const)
  exact hb.comp (measurable_fst.prodMk (measurable_overlayVirtualEntry P fee hfee C accounting source hm stage))

theorem overlayCurrentDraw_replace_current (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (representative : OverlayStageCoins) (row : OverlayStageCoins) (world : Bool × P.experiment.Tape)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    overlayCurrentDraw P fee hfee C accounting source stage
      (overlayFreshReplace P fee hfee stage row world sample) =
      overlayCurrentDraw P fee hfee C accounting source stage sample := by
  have he := congrArg Prod.snd
    (overlayVirtualEntryGate_replace_current P fee hfee C accounting source stage representative row world sample)
  change overlayVirtualEntry P fee hfee C accounting source stage
    (overlayFreshReplace P fee hfee stage row world sample) =
      overlayVirtualEntry P fee hfee C accounting source stage sample at he
  unfold overlayCurrentDraw
  rw [he]
  rfl

noncomputable def overlayRecordGate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :=
  (overlayVirtualEntryGate P fee hfee C accounting source stage sample,
    overlayCurrentDraw P fee hfee C accounting source stage sample)

theorem measurable_overlayRecordGate [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayRecordGate P fee hfee C accounting source stage) :=
  ((measurable_fst.comp measurable_fst).prodMk
    (measurable_overlayVirtualEntry P fee hfee C accounting source hm stage)).prodMk
    (measurable_overlayCurrentDraw P fee hfee C accounting source hm stage)

theorem overlayRecordGate_replace_current (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (representative : OverlayStageCoins) (row : OverlayStageCoins) (world : Bool × P.experiment.Tape)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    overlayRecordGate P fee hfee C accounting source stage
      (overlayFreshReplace P fee hfee stage row world sample) =
      overlayRecordGate P fee hfee C accounting source stage sample := by
  apply Prod.ext
  · exact overlayVirtualEntryGate_replace_current P fee hfee C accounting source stage representative row world sample
  · exact overlayCurrentDraw_replace_current P fee hfee C accounting source stage representative row world sample

/-- Concrete original-seed/full-entry/full-record gate has fresh row and
fresh actual world. Current auxiliary tape remains inside the selected record.
All replacement invariance has been proved for the actual controller above. -/
theorem overlayRecordGate_joint_freshEndpoint [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (rowLaw : Measure OverlayStageCoins) [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (overlayRecordGate P fee hfee C accounting source stage sample, overlayFreshCurrent P fee hfee stage sample)) =
        ((overlayFreshAllOtherLaw P fee hfee ν rowLaw stage).map
          (overlayFreshGateFactor P fee hfee stage row (false, simulatorDummyTape P)
            (overlayRecordGate P fee hfee C accounting source stage))).prod
            (rowLaw.prod ((P.input fee hfee).stageLaw stage)) :=
  overlayFreshWorldLaw_invariantGate P fee hfee ν rowLaw stage row (false, simulatorDummyTape P)
    (overlayRecordGate P fee hfee C accounting source stage)
    (measurable_overlayRecordGate P fee hfee C accounting source hm stage)
    (fun sample newRow newWorld =>
      overlayRecordGate_replace_current P fee hfee C accounting source stage row newRow newWorld sample)


end EntryPart5

end PDROC
