module

public import PaperProofs.Paid.PDROC_SimulatorLaw_005
public import PaperProofs.Paid.PDROC_DirectEntry_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- Full finite-draw identification, including the original action rather
than only its write bit. No actual or future truth is used in this sampler. -/
theorem simulatorDrawAt_some_history_spec (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (seed : Seed) (entry : List (VisibleEvent P.sharedInstance)) (tape : P.experiment.Tape)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage seed entry tape = some draw) :
    headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape =
        (draw.record.observations.length : ℕ∞) ∧
      simulatorReviewPacket stage draw.record =
        headReviewHistory (P.input fee hfee) stage tape draw.record.observations.length ∧
      draw.action = source seed (entry ++ simulatorReviewPacket stage draw.record) := by
  by_cases ht : headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape = ⊤
  · simp only [simulatorDrawAt, ht, ↓reduceIte, reduceCtorEq] at hd
  · simp only [simulatorDrawAt, ht, ↓reduceIte, Option.some.injEq] at hd
    let n := (headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape).toNat
    let action := source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n)
    let canonical : SimulatorDraw P.sharedInstance :=
      ⟨⟨List.ofFn (fun k : Fin n => tape k.val), optionWriteBit action⟩, action⟩
    have heq : canonical = draw := hd
    have hlength : draw.record.observations.length = n :=
      (congrArg (fun d : SimulatorDraw P.sharedInstance => d.record.observations.length) heq).symm.trans
        List.length_ofFn
    have hpacket : simulatorReviewPacket stage draw.record = headReviewHistory (P.input fee hfee) stage tape n := by
      rw [← heq]
      change (List.ofFn (fun k : Fin n => tape k.val)).map (fun symbol => VisibleEvent.observation stage symbol.val) = _
      exact List.map_ofFn
    have haction : draw.action = source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n) :=
      congrArg SimulatorDraw.action heq.symm
    refine ⟨?_, ?_, ?_⟩
    · exact (ENat.natCast_toNat_eq_self.mpr ht).symm.trans (congrArg (fun k : ℕ => (k : ℕ∞)) hlength.symm)
    · exact hpacket.trans (congrArg (headReviewHistory (P.input fee hfee) stage tape) hlength.symm)
    · exact haction.trans (congrArg (fun packet => source seed (entry ++ packet)) hpacket.symm)

theorem sourceDrawTerminalHistory_eq_stepHistory (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth : Bool) {s next : State I}
    (hbefore : s.history = entry ++ simulatorReviewPacket stage draw.record)
    (hserial : s.clock = (historyActions entry).length + draw.record.observations.length)
    (htruth : truth = s.ledger.truth stage)
    (hc : (∃ bit, draw.action = .write stage bit) ∨ draw.action = .stop ∨ draw.action = .abandon)
    (hs : Step input C mode accounting tapes s draw.action next) :
    sourceDrawTerminalHistory stage entry draw truth = next.history := by
  rcases hc with ⟨bit, hw⟩ | hstop | habandon
  · rw [hw] at hs
    cases hs
    simp only [sourceDrawTerminalHistory, hw]
    rw [← hbefore, ← hserial, htruth]
    simp only [record, writeResponses, hearly, ↓reduceIte, writeLedger, List.singleton_append]
  · rw [hstop] at hs
    cases hs
    simp only [sourceDrawTerminalHistory, hstop, stopState, Bool.false_eq_true, ↓reduceIte]
    rw [hbefore]
  · rw [habandon] at hs
    cases hs
    simp only [sourceDrawTerminalHistory, habandon, stopState, ↓reduceIte]
    rw [hbefore]

theorem postwriteStageTrace_of_halted {source : PolicyRule I Seed} (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) (hh : historyHalted history = true) (n : ℕ) :
    postwriteStageTrace source seed stage history n = history := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [postwriteStageTrace, ih, postwriteStageStep, hh, ↓reduceIte]

theorem sourceDrawStep_halted_or_written (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (stage : I.Stage) (draw : SimulatorDraw I) {s next : State I}
    (hcursor : s.cursor = stage.val)
    (hc : (∃ bit, draw.action = .write stage bit) ∨ draw.action = .stop ∨ draw.action = .abandon)
    (hs : Step input C mode accounting tapes s draw.action next) :
    next.halted = true ∨ (next.cursor = stage.val ∧ next.ledger.written stage ≠ none) := by
  rcases hc with ⟨bit, hw⟩ | hstop | habandon
  · rw [hw] at hs
    cases hs
    right
    refine ⟨hcursor, ?_⟩
    classical
    simp only [record, reportedWriteLedger]
    split_ifs <;> simp only [writeLedger, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
  · rw [hstop] at hs
    cases hs
    exact Or.inl rfl
  · rw [habandon] at hs
    cases hs
    exact Or.inl rfl

/-- At an original genuine first entry, the concrete finite simulator draw
reproduces the actual source write/early-report or source termination packet. -/
theorem firstEntry_sourceDrawTerminalHistory (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source stage.val start sample)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage sample.1
      (run (P.input fee hfee) C.val .uncapped accounting source sample start).history
        (worldTapes (P.input fee hfee) sample.2 stage) = some draw) :
    sourceDrawTerminalHistory stage (run (P.input fee hfee) C.val .uncapped accounting source sample start).history
      draw ((P.input fee hfee).truthAt sample.2 stage) =
      (run (P.input fee hfee) C.val .uncapped accounting source sample
        (start + draw.record.observations.length + 1)).history := by
  let input := P.input fee hfee
  let n := draw.record.observations.length
  obtain ⟨hstop, hpacket, hdrawAction⟩ := simulatorDrawAt_some_history_spec P fee hfee source stage sample.1
    (run input C.val .uncapped accounting source sample start).history (worldTapes input sample.2 stage) draw hd
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting source hl sample stage.val start he
  have hr := run_eq_entryReviewState_before_directExit P fee hfee C.val accounting source sample start stage
    ha he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 n (by rw [hstop])
  have hactive : (run input C.val .uncapped accounting source sample (start + n)).halted = false := by
    rw [hr]
    exact entryReviewState_active _ _ _ _ _ n ha
  have hbefore : (run input C.val .uncapped accounting source sample (start + n)).history =
      (run input C.val .uncapped accounting source sample start).history ++ simulatorReviewPacket stage draw.record := by
    rw [hr, entryReviewState_history, hpacket]
  have hserial : (run input C.val .uncapped accounting source sample (start + n)).clock =
      (historyActions (run input C.val .uncapped accounting source sample start).history).length + n := by
    rw [run_clock_eq_index_of_active input C.val .uncapped accounting source hl sample (start + n) hactive,
      prefix_historyActions_length input C.val .uncapped accounting source sample.1 _ _
        (run_prefix_of_active input C.val .uncapped accounting source hl sample start ha),
      run_clock_eq_index_of_active input C.val .uncapped accounting source hl sample start ha]
  have haction : source sample.1 (run input C.val .uncapped accounting source sample (start + n)).history = draw.action := by
    rw [hbefore]
    exact hdrawAction.symm
  have hs := run_actualStep_of_active input C.val .uncapped accounting source hl sample (start + n) hactive
  rw [haction] at hs
  have htruth : input.truthAt sample.2 stage =
      (run input C.val .uncapped accounting source sample (start + n)).ledger.truth stage :=
    (congrFun (prefix_truth input C.val .uncapped accounting source sample.1 _ _
      (run_prefix_of_active input C.val .uncapped accounting source hl sample (start + n) hactive)) stage).symm
  exact sourceDrawTerminalHistory_eq_stepHistory input C.val C.property.1.1 .uncapped accounting
    (worldTapes input sample.2) stage _ draw _ hbefore hserial htruth
      (firstEntry_simulatorDrawAt_action_cases P fee hfee C accounting source hl sample start stage he draw hd) hs

/-- The full finite source stage, including all its genuine correction and
exit actions, is exactly the concrete measurable stage transition used in
the coupling law. All source failures and both termination actions remain. -/
theorem firstEntry_sourceDrawStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source stage.val start sample)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage sample.1
      (run (P.input fee hfee) C.val .uncapped accounting source sample start).history
        (worldTapes (P.input fee hfee) sample.2 stage) = some draw) :
    ∃ exit : ℕ, exit ≤ 3 ∧
      ((run (P.input fee hfee) C.val .uncapped accounting source sample
          (start + draw.record.observations.length + 1 + exit)).halted = true ∨
        stage.val < (run (P.input fee hfee) C.val .uncapped accounting source sample
          (start + draw.record.observations.length + 1 + exit)).cursor) ∧
      sourceDrawStageExit source stage
          (((sample.1, (run (P.input fee hfee) C.val .uncapped accounting source sample start).history), draw),
            (P.input fee hfee).truthAt sample.2 stage) =
        (sample.1, (run (P.input fee hfee) C.val .uncapped accounting source sample
          (start + draw.record.observations.length + 1 + exit)).history) := by
  let input := P.input fee hfee
  let n := draw.record.observations.length
  obtain ⟨hstop, hpacket, hdrawAction⟩ := simulatorDrawAt_some_history_spec P fee hfee source stage sample.1
    (run input C.val .uncapped accounting source sample start).history (worldTapes input sample.2 stage) draw hd
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting source hl sample stage.val start he
  have hr := run_eq_entryReviewState_before_directExit P fee hfee C.val accounting source sample start stage
    ha he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 n (by rw [hstop])
  have hactive : (run input C.val .uncapped accounting source sample (start + n)).halted = false := by
    rw [hr]
    exact entryReviewState_active _ _ _ _ _ n ha
  have hcursor : (run input C.val .uncapped accounting source sample (start + n)).cursor = stage.val := by
    rw [hr, entryReviewState_cursor]
    exact he.1
  have hbefore : (run input C.val .uncapped accounting source sample (start + n)).history =
      (run input C.val .uncapped accounting source sample start).history ++ simulatorReviewPacket stage draw.record := by
    rw [hr, entryReviewState_history, hpacket]
  have haction : source sample.1 (run input C.val .uncapped accounting source sample (start + n)).history = draw.action := by
    rw [hbefore]
    exact hdrawAction.symm
  have hs := run_actualStep_of_active input C.val .uncapped accounting source hl sample (start + n) hactive
  rw [haction] at hs
  have hshape := sourceDrawStep_halted_or_written input C.val .uncapped accounting
    (worldTapes input sample.2) stage draw hcursor
      (firstEntry_simulatorDrawAt_action_cases P fee hfee C accounting source hl sample start stage he draw hd) hs
  have hterminal := firstEntry_sourceDrawTerminalHistory P fee hfee C accounting source hl sample start stage he draw hd
  rcases hshape with hh | ⟨hc, hw⟩
  · obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting source hl sample (start + n + 1)
    have hhistoryHalted : historyHalted (run input C.val .uncapped accounting source sample (start + n + 1)).history = true := by
      rw [prefix_historyHalted input C.val .uncapped accounting source sample.1 _ _ hp]
      exact hh
    refine ⟨0, by omega, Or.inl ?_, ?_⟩
    · simpa only [Nat.add_zero] using hh
    · change (sample.1, postwriteStageTrace source sample.1 stage _ 3) = _
      rw [hterminal, postwriteStageTrace_of_halted sample.1 stage _ hhistoryHalted]
  · obtain ⟨exit, hb, he, htrace⟩ := postwriteStageTrace_three_eq_actual_exit input C.val C.property .uncapped
      accounting source hl sample (start + n + 1) stage hc hw
    refine ⟨exit, hb, he, ?_⟩
    change (sample.1, postwriteStageTrace source sample.1 stage _ 3) = _
    rw [hterminal, htrace]

end PDROC
