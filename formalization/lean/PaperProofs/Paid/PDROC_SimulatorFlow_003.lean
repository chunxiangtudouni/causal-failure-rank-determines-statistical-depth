module

public import PaperProofs.Paid.PDROC_SimulatorFlow_002
public import PaperProofs.Paid.PDROC_SimulatorLaw_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

theorem sourceDrawStageExit_optionalHistory_some (source : PolicyRule I Seed) (stage : I.Stage)
    (seed : Seed) (prior entry : List (VisibleEvent I)) (draw : SimulatorDraw I) (truth : Bool) :
    sourceDrawStageExit (sourceForOptionalHistory source) stage ((((seed, some prior), entry), draw), truth) =
      ((seed, some prior), (sourceDrawStageExit source stage (((seed, entry), draw), truth)).2) := by
  change ((seed, some prior), postwriteStageTrace (sourceForOptionalHistory source) (seed, some prior) stage
    (sourceDrawTerminalHistory stage entry draw truth) 3) = _
  rw [postwriteStageTrace_congr_seed_rule (sourceForOptionalHistory source) source (seed, some prior) seed
    (fun _ => rfl) stage _ 3]
  rfl

/-- A finite direct draw at the genuine source entry determines the FIRST
full stage exit, including all source stop/abandon and postwrite branches. -/
theorem firstEntry_sourceDrawStageExit_minimal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source stage.val start sample)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage sample.1
      (run (P.input fee hfee) C.val .uncapped accounting source sample start).history
        (worldTapes (P.input fee hfee) sample.2 stage) = some draw) :
    ∃ offset : ℕ,
      (∀ k < offset, (run (P.input fee hfee) C.val .uncapped accounting source sample (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting source sample (start + k)).cursor = stage.val) ∧
      ((run (P.input fee hfee) C.val .uncapped accounting source sample (start + offset)).halted = true ∨
        (run (P.input fee hfee) C.val .uncapped accounting source sample (start + offset)).cursor = stage.val + 1) ∧
      (sample.1, (run (P.input fee hfee) C.val .uncapped accounting source sample (start + offset)).history) =
        sourceDrawStageExit source stage
          (((sample.1, (run (P.input fee hfee) C.val .uncapped accounting source sample start).history), draw),
            (P.input fee hfee).truthAt sample.2 stage) := by
  let input := P.input fee hfee
  let n := draw.record.observations.length
  obtain ⟨hstop, _, hdrawAction⟩ := simulatorDrawAt_some_history_spec P fee hfee source stage sample.1
    (run input C.val .uncapped accounting source sample start).history (worldTapes input sample.2 stage) draw hd
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting source hl sample stage.val start he
  have hpre (k : ℕ) (hk : k ≤ n) :
      (run input C.val .uncapped accounting source sample (start + k)).halted = false ∧
      (run input C.val .uncapped accounting source sample (start + k)).cursor = stage.val := by
    have hr := run_eq_entryReviewState_before_directExit P fee hfee C.val accounting source sample start stage
      ha he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 k (by rw [hstop]; exact_mod_cast hk)
    rw [hr]
    exact ⟨entryReviewState_active _ _ _ _ _ k ha, (entryReviewState_cursor _ _ _ _ _ k).trans he.1⟩
  have hbefore : (run input C.val .uncapped accounting source sample (start + n)).history =
      (run input C.val .uncapped accounting source sample start).history ++ simulatorReviewPacket stage draw.record := by
    rw [firstEntry_directReviewPrefix P fee hfee C.val accounting source hl sample start stage he n (by rw [hstop])]
    rw [(simulatorDrawAt_some_history_spec P fee hfee source stage sample.1
      (run input C.val .uncapped accounting source sample start).history (worldTapes input sample.2 stage) draw hd).2.1]
  have haction : source sample.1 (run input C.val .uncapped accounting source sample (start + n)).history = draw.action := by
    rw [hbefore]
    exact hdrawAction.symm
  have hs := run_actualStep_of_active input C.val .uncapped accounting source hl sample (start + n) (hpre n le_rfl).1
  rw [haction] at hs
  have hshape := sourceDrawStep_halted_or_written input C.val .uncapped accounting (worldTapes input sample.2) stage draw
    (hpre n le_rfl).2 (firstEntry_simulatorDrawAt_action_cases P fee hfee C accounting source hl sample start stage he draw hd) hs
  have hterminal := firstEntry_sourceDrawTerminalHistory P fee hfee C accounting source hl sample start stage he draw hd
  by_cases hh : (run input C.val .uncapped accounting source sample (start + n + 1)).halted = true
  · have hhh : historyHalted (run input C.val .uncapped accounting source sample (start + n + 1)).history = true := by
      obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting source hl sample (start + n + 1)
      exact (prefix_historyHalted input C.val .uncapped accounting source sample.1 _ _ hp).trans hh
    refine ⟨n + 1, ?_, ?_, ?_⟩
    · intro k hk
      exact hpre k (by omega)
    · exact Or.inl (by simpa only [Nat.add_assoc] using hh)
    · symm
      change (sample.1, postwriteStageTrace source sample.1 stage _ 3) = _
      rw [hterminal, postwriteStageTrace_of_halted sample.1 stage _ hhh]
      simp only [Nat.add_assoc]
      rfl
  · have haf : (run input C.val .uncapped accounting source sample (start + n + 1)).halted = false := Bool.eq_false_iff.mpr hh
    obtain ⟨hc, hw⟩ := hshape.resolve_left hh
    obtain ⟨exit, _, hexit, hpost, htrace⟩ := postwrite_first_exit input C.val C.property .uncapped accounting source hl
      sample (start + n + 1) stage haf hc hw
    refine ⟨n + 1 + exit, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hkn : k ≤ n
      · exact hpre k hkn
      · have hb := hpost (k - (n + 1)) (by omega)
        simpa only [show start + n + 1 + (k - (n + 1)) = start + k by omega] using hb
    · simpa only [Nat.add_assoc] using hexit
    · symm
      change (sample.1, postwriteStageTrace source sample.1 stage _ 3) = _
      rw [hterminal, htrace]
      simp only [Nat.add_assoc]
      rfl

/-- Source finite-draw flow into the exact measurable next-entry projection.
The retained optional seed is the original eventual entry, not a normalized gate. -/
theorem source_nextEntry_projection_of_finiteDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage next : P.sharedInstance.Stage)
    (hnext : next.val = stage.val + 1)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source stage.val start sample)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage sample.1
      (run (P.input fee hfee) C.val .uncapped accounting source sample start).history
        (worldTapes (P.input fee hfee) sample.2 stage) = some draw) :
    (sample.1, entryHistory (P.input fee hfee) C.val .uncapped accounting source next sample) =
      simulatorNextEntryProjection next
        (sourceDrawStageExit (sourceForOptionalHistory source) stage
          ((((sample.1, some (run (P.input fee hfee) C.val .uncapped accounting source sample start).history),
            (run (P.input fee hfee) C.val .uncapped accounting source sample start).history), draw),
              (P.input fee hfee).truthAt sample.2 stage)) := by
  obtain ⟨offset, hbefore, hexit, hhistory⟩ := firstEntry_sourceDrawStageExit_minimal P fee hfee C accounting source hl sample start stage he draw hd
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting source hl sample (start + offset)
  have h := entryHistory_map_projection_of_minimal_stage_exit (P.input fee hfee) C.val .uncapped accounting source hl
    sample start offset stage next hnext he.1 (fun k hk => (hbefore k hk).2) hexit id
    (prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting source sample.1 _ _ hp)
    (prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting source sample.1 _ _ hp)
    sample.1 (run (P.input fee hfee) C.val .uncapped accounting source sample start).history
  rw [Option.map_id] at h
  rw [sourceDrawStageExit_optionalHistory_some]
  rw [show (sourceDrawStageExit source stage
    (((sample.1, (run (P.input fee hfee) C.val .uncapped accounting source sample start).history), draw),
      (P.input fee hfee).truthAt sample.2 stage)).2 =
    (run (P.input fee hfee) C.val .uncapped accounting source sample (start + offset)).history from
      (congrArg Prod.snd hhistory).symm]
  exact h

end PDROC

