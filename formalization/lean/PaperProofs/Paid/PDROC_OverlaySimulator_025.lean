module

public import PaperProofs.Paid.PDROC_OverlaySimulator_020
public import PaperProofs.Paid.PDROC_OverlaySimulator_024
public import PaperProofs.Paid.PDROC_SimulatorRecords_002
public import PaperProofs.Paid.PDROC_OverlayTermination_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem completed_overlay_written_port_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I))
    (hh : completedHistory input C mode accounting rule sample = some history)
    (start : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    overlayPortView (overlayReplay draw mark ghost seed history).shadow stage =
      overlayPortView (overlayReplay draw mark ghost seed (run input C mode accounting rule sample start).history).shadow stage := by
  obtain ⟨finish, hf, _, he⟩ := (completedHistory_some_iff input C mode accounting rule sample history).mp hh
  rw [← he]
  rcases le_total start finish with h | h
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    exact run_overlay_written_port_frame input C hearly mode accounting rule hl sample draw mark ghost seed start extra stage bit hw
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_after_halt input C mode accounting rule sample finish hf extra]

theorem overlayReplay_writeReport_port {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial : ℕ)
    (ho : historyObservations (overlayReplay draw mark ghost seed history).shadow stage = [])
    (decision : Bool)
    (hd : (simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)).decision = some decision) :
    overlayPortView (overlayReplay draw mark ghost seed
      (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow stage =
      ((simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)).observations.map Fin.val,
        some decision) := by
  rw [show history ++ [.wrote stage bit serial, .report stage truth serial] =
    (history ++ [.wrote stage bit serial]) ++ [.report stage truth serial] by simp]
  rw [overlayReplay_append_event, overlayReplay_append_event]
  simp only [overlayStep, simulatorStep, simulatorAppend]
  rw [hd]
  simp only [Option.getD_some]
  change List.filterMap (eventObservation stage) (overlayReplay draw mark ghost seed history).shadow = [] at ho
  simp [overlayPortView, historyObservations, historyWritten, historyWrite, simulatorReviewPacket,
    List.filterMap_append, List.filterMap_map, List.filterMap_cons, List.filterMap_nil, Function.comp_def, eventObservation, eventWrite, ho]
theorem overlayReplay_terminal_port {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage) (abandon : Bool)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage = none)
    (ho : historyObservations (overlayReplay draw mark ghost seed history).shadow stage = [])
    (hvw : historyWritten (overlayReplay draw mark ghost seed history).shadow stage = none) :
    overlayPortView (overlayReplay draw mark ghost seed
      (history ++ [if abandon then .abandoned else .stopped])).shadow stage =
      ((simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)).observations.map Fin.val, none) := by
  have hc' : historyCursor (overlayReplay draw mark ghost seed history).seen < I.stageCount := by
    rw [overlayReplay_seen, hc]
    exact stage.isLt
  have he : (⟨historyCursor (overlayReplay draw mark ghost seed history).seen, hc'⟩ : I.Stage) = stage := by
    apply Fin.ext
    simpa only [overlayReplay_seen] using hc
  have hw' : historyWritten (overlayReplay draw mark ghost seed history).seen
      ⟨historyCursor (overlayReplay draw mark ghost seed history).seen, hc'⟩ = none := by
    rw [he, overlayReplay_seen, hw]
  have hw'' : historyWritten (overlayReplay draw mark ghost seed history).seen stage = none := by
    simpa only [he] using hw'
  change List.filterMap (eventObservation stage) (overlayReplay draw mark ghost seed history).shadow = [] at ho
  change (List.filterMap (eventWrite stage) (overlayReplay draw mark ghost seed history).shadow).getLast?.map Prod.fst = none at hvw
  cases abandon <;>
    simp only [Bool.false_eq_true, ↓reduceIte, overlayReplay_append_event, overlayStep,
      hc', ↓reduceDIte, he, hw'', simulatorAppend] <;>
    simp [overlayPortView, historyObservations, historyWritten, historyWrite, simulatorReviewPacket,
      List.filterMap_append, overlayGhostEvents_no_observation, overlayGhostEvents_no_write, List.filterMap_map, Function.comp_def, eventObservation, eventWrite, ho] <;> simpa [eventWrite] using hvw


universe u
variable {Seed : Type u}

theorem overlay_entry_shadow_fresh (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample = some entry) :
    historyCursor (overlayShadow P source sample.1 entry) = stage.val ∧
      historyObservations (overlayShadow P source sample.1 entry) stage = [] ∧
      historyWrite (overlayShadow P source sample.1 entry) stage = none := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨start, hc, hbefore, hhistory⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start sample := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl sample stage.val start he'
  have hw := (hunborn stage le_rfl).1
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  have hf := prefix_overlay_unwritten_port_fresh input C.val .uncapped accounting actual sample.1 _ _ hp ha stage hw
    (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1
  have hcu := (overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
    sample.1 (run input C.val .uncapped accounting actual sample start).history).1.symm.trans
      ((prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc)
  rw [hhistory] at hf hcu
  exact ⟨hcu, hf.1, hf.2⟩

theorem overlayReviewStateFrom_shadow (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (stage : P.sharedInstance.Stage) (tape : ((P.input fee hfee).experiment stage).Tape) (s : State P.sharedInstance) (n : ℕ) :
    overlayShadow P source seed
      (simulatorReviewStateFrom (P.input fee hfee) accounting stage tape s n).history =
      overlayShadow P source seed s.history := by
  rw [simulatorReviewStateFrom_history (P.input fee hfee) accounting stage tape s n]
  have he : headReviewHistory (P.input fee hfee) stage tape n =
      (List.ofFn (fun k : Fin n => tape k)).map (fun symbol => .observation stage symbol.val) := by
    simp only [headReviewHistory, List.map_ofFn, Function.comp_def]
  rw [he]
  exact overlayShadow_append_observations P source seed s.history stage _

theorem overlay_writing_record_shadow_at_stop (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hvo : historyObservations (overlayShadow P source seed s.history) stage = [])
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    overlayPortView (overlayShadow P source seed
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
        (seed, world) (start + n + 1)).history) stage =
      (draw.record.observations.map Fin.val, some decision) := by
  let input := P.input fee hfee
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record) tape
  have hstate := overlayRun_write_at_mixture P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hshadow : overlayShadow P source seed before.history =
      overlayShadow P source seed s.history :=
    overlayReviewStateFrom_shadow P fee hfee accounting source seed stage tape s n
  have hbefore : historyObservations (overlayShadow P source seed before.history) stage = [] :=
    (congrArg (fun history => historyObservations history stage) hshadow).trans hvo
  have hrec : simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed before.history)) = draw.record := by
    rw [hshadow, hdraw]
    rfl
  change simulatorDrawRecord (overlaySeedDraw P source seed stage
    (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed before.history).shadow) = draw.record at hrec
  have hresult := overlayReplay_writeReport_port (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed before.history
    stage bit (before.ledger.truth stage) before.clock hbefore decision (by rw [hrec, hd])
  rw [hstate]
  simpa only [record, writeResponses, C.property.1.1, ↓reduceIte, writeLedger, List.singleton_append,
    overlayShadow, overlaySeedReplay, hrec] using hresult

theorem overlay_none_record_shadow_completed (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (history : List (VisibleEvent P.sharedInstance))
    (hh : completedHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) (seed, world) = some history)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hnone : (simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed s.history))).decision = none) :
    overlayPortView (overlayShadow P source seed history) stage =
      ((simulatorDrawRecord (overlaySeedDraw P source seed stage
        (overlayShadow P source seed s.history))).observations.map Fin.val, none) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) (seed, world) start
  have hprefix : Prefix input C.val .uncapped accounting actual seed (input.truthAt world) (worldTapes input world) k s := hs0 ▸ hp
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
  have hf := prefix_overlay_unwritten_port_fresh input C.val .uncapped accounting actual seed _ _ hprefix ha stage hw
    (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed
  have hvw : historyWritten (overlayShadow P source seed s.history) stage = none := by
    simp only [overlayShadow, overlaySeedReplay, historyWritten, hf.2, Option.map_none]
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
  have hhfinal := completedHistory_eq_history_of_halted input C.val .uncapped accounting actual
    (seed, world) history hh (start + 1) (by rw [hhalt]; rfl)
  rw [hhfinal, hhalt]
  exact overlayReplay_terminal_port (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed s.history stage abandon hhc hhw hf.1 hvw

theorem overlay_writing_record_shadow_completed (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (history : List (VisibleEvent P.sharedInstance))
    (hh : completedHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) (seed, world) = some history)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hvo : historyObservations (overlayShadow P source seed s.history) stage = [])
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    overlayPortView (overlayShadow P source seed history) stage =
      (draw.record.observations.map Fin.val, some decision) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record) tape
  have hstate := overlayRun_write_at_mixture P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hwritten : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.written stage = some bit := by
    rw [hstate]
    simp only [record, reportedWriteLedger, C.property.1.1, ↓reduceIte, writeLedger, Function.update_self]
    rfl
  have hframe := completed_overlay_written_port_frame input C.val C.property.1.1 .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) (seed, world) (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
    seed history hh (start + n + 1) stage bit hwritten
  exact hframe.trans (overlay_writing_record_shadow_at_stop P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hvo hdraw hd n hs)


section Alignment
variable [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
/-- The concrete source word and decision align with the entire final shadow,
including the immediate nonwriting termination branch. -/
theorem overlay_sourceRecordAlignment_pointwise (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed) (world : (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (coins : Bool × Bool), ∃ n : ℕ,
      (P.overlayRecordTest fee hfee record).rule.stop coins (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    ∀ history, completedHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) (seed, world) = some history →
      ∀ stage entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) stage (seed, world) = some entry →
        historyCursor ((overlayData P source).shadow seed entry) = stage.val ∧
        historyObservations ((overlayData P source).shadow seed entry) stage = [] ∧
        historyWrite ((overlayData P source).shadow seed entry) stage = none ∧
        ((overlayData P source).record seed stage entry).observations.map Fin.val =
          historyObservations ((overlayData P source).shadow seed history) stage ∧
        ((overlayData P source).record seed stage entry).decision =
          historyWritten ((overlayData P source).shadow seed history) stage := by
  intro history hh stage entry he
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  have hf := overlay_entry_shadow_fresh P fee hfee C accounting source (seed, world) stage entry he
  obtain ⟨start, hc, hbefore, hentry⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage (seed, world) entry).mp he
  let s := run input C.val .uncapped accounting actual (seed, world) start
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start (seed, world) := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl (seed, world) stage.val start he'
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) start
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual seed _ _ hp stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  have hvo : historyObservations (overlayShadow P source seed s.history) stage = [] := by
    change historyObservations (overlayShadow P source seed
      (run input C.val .uncapped accounting actual (seed, world) start).history) stage = []
    rw [hentry]
    exact hf.2.1
  let record := (overlayData P source).record seed stage entry
  have hrecord : record = simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed s.history)) := by
    change simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayShadow P source seed entry)) = _
    rw [hentry]
  have hview : overlayPortView (overlayShadow P source seed history) stage =
      (record.observations.map Fin.val, record.decision) := by
    cases hd : record.decision with
    | none =>
      have hn : (simulatorDrawRecord (overlaySeedDraw P source seed stage
          (overlayShadow P source seed s.history))).decision = none := hrecord ▸ hd
      have hv := overlay_none_record_shadow_completed P fee hfee C accounting source seed world history hh
        start s stage rfl ha hc hw hn
      rw [← hrecord] at hv
      simpa only [hd] using hv
    | some decision =>
      cases hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed s.history) with
      | none =>
        have hn : record.decision = none := by rw [hrecord, hdraw]; rfl
        rw [hn] at hd
        cases hd
      | some draw =>
        have hrec : record = draw.record := by rw [hrecord, hdraw]; rfl
        have hd' : draw.record.decision = some decision := hrec ▸ hd
        obtain ⟨n, hn⟩ := hfinite stage draw.record (overlaySeedCoins P seed stage draw.record)
        have hv := overlay_writing_record_shadow_completed P fee hfee C accounting source seed world history hh
          start s stage draw decision rfl ha hc hw hr ho hvo hdraw hd' n hn
        simpa only [hrec, hd'] using hv
  exact ⟨hf.1, hf.2.1, hf.2.2, (congrArg Prod.fst hview).symm, (congrArg Prod.snd hview).symm⟩

/-- The original D06 SourceRecordAlignment is closed for the actual simulator,
with no source-history-law or finite-source-charge premise. -/
theorem overlaySourceRecordAlignment (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure (OverlaySeed P Seed)) [IsProbabilityMeasure ν] :
    P.SourceRecordAlignment fee hfee C accounting ν (overlayRule P fee hfee source)
      (overlayData P source).toRecordSimulatorData := by
  filter_upwards [allOverlayTests_finite_seededWorld P fee hfee ν] with sample hs
  exact overlay_sourceRecordAlignment_pointwise P fee hfee C accounting source sample.1 sample.2 hs


end Alignment

end PDROC
