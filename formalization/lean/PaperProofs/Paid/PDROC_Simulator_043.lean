module

public import PaperProofs.Paid.PDROC_Simulator_042

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem minimal_run_stage_exit_cursor {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (start offset : ℕ) (stage : I.Stage)
    (_ha : (run input C mode accounting source sample start).halted = false)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hbefore : ∀ k < offset,
      (run input C mode accounting source sample (start + k)).halted = false ∧
      (run input C mode accounting source sample (start + k)).cursor = stage.val)
    (hexit : (run input C mode accounting source sample (start + offset)).halted = true ∨
      stage.val < (run input C mode accounting source sample (start + offset)).cursor) :
    (run input C mode accounting source sample (start + offset)).halted = true ∨
      (run input C mode accounting source sample (start + offset)).cursor = stage.val + 1 := by
  rcases hexit with hh | hgt
  · exact Or.inl hh
  · have hpos : 0 < offset := by
      by_contra hn
      have hz : offset = 0 := by omega
      rw [hz, Nat.add_zero, hc] at hgt
      omega
    have hp := (hbefore (offset - 1) (by omega)).2
    have hs := (run_cursor_step_bounds input C mode accounting source hl sample (start + (offset - 1))).2
    rw [hp, show start + (offset - 1) + 1 = start + offset by omega] at hs
    exact Or.inr (by omega)

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The pure-guard writing-stage realization exposes minimality across
both real endpoint reviews and every later physical correction step. -/
theorem simulator_writing_stageExit_minimal_of_guardGood (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (haction : draw.action = .write stage decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (hgood : sourcePostwriteGuardGood source seed.1 stage
      (sourceDrawTerminalHistory stage (simulatorShadow P fee hfee source seed s.history) draw
        (recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
          (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)))) :
    ∃ offset : ℕ,
      (∀ k < offset,
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + k)).cursor = stage.val) ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (start + offset)).halted = true ∨
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + offset)).cursor = stage.val + 1) ∧
      (seed.1, simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + offset)).history) =
        sourceDrawStageExit source stage
          (((seed.1, simulatorShadow P fee hfee source seed s.history), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
              (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let tape := worldTapes input world stage
  let bit := Bool.xor decision (Bool.xor draw.record.orientation
    ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))
  have hl := simulatorRule_legal P fee hfee C accounting source
  have hd : draw.record.decision = some decision := by
    have hd := (simulatorSeedDraw_some_spec P fee hfee source seed stage _ draw hdraw).1
    simpa only [haction, optionWriteBit] using hd
  have hstate := simulator_run_write_at_endpoint P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have haw : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.written stage = some bit := by
    rw [hstate]
    simp only [record, reportedWriteLedger, C.property.1.1, ↓reduceIte, writeLedger, Function.update_self]
    rfl
  have hac : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).cursor = stage.val := by
    rw [hstate]
    exact (simulatorReviewStateFrom_cursor input accounting stage tape s n).trans hc
  have hpacket := simulator_writing_record_shadow_packet P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw haction n hs
  have hgood' : sourcePostwriteGuardGood source seed.1 stage
      (simulatorShadow P fee hfee source seed
        (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).history) := by
    rw [hpacket]
    exact hgood
  obtain ⟨exit, _, hpostbefore, hexit, hfinal⟩ := simulator_postwrite_exit_of_guardGood P fee hfee C accounting source
    seed world (start + n + 1) stage bit hac haw hgood'
  have hbefore (k : ℕ) (hk : k < n + 1 + exit) :
      (run input C.val .uncapped accounting actual (seed, world) (start + k)).halted = false ∧
      (run input C.val .uncapped accounting actual (seed, world) (start + k)).cursor = stage.val := by
    by_cases hpre : k ≤ n
    · have hreview := simulator_run_eq_reviewStateFrom P fee hfee C accounting source seed world start stage draw decision
        (by simpa only [hs0] using ha) (by simpa only [hs0] using hc)
        (by simpa only [hs0] using hw) (by simpa only [hs0] using hr)
        (by simpa only [hs0] using ho) (by simpa only [hs0] using hdraw) hd k
        (by rw [hs]; exact_mod_cast hpre)
      have heq : run input C.val .uncapped accounting actual (seed, world) (start + k) =
          simulatorReviewStateFrom input accounting stage tape s k := by simpa only [hs0] using hreview
      exact ⟨(congrArg State.halted heq).trans (simulatorReviewStateFrom_active input accounting stage tape s k ha),
        (congrArg State.cursor heq).trans ((simulatorReviewStateFrom_cursor input accounting stage tape s k).trans hc)⟩
    · have hb := hpostbefore (k - (n + 1)) (by omega)
      have ht : start + n + 1 + (k - (n + 1)) = start + k := by omega
      simpa only [ht] using hb
  have hexit' : (run input C.val .uncapped accounting actual (seed, world) (start + (n + 1 + exit))).halted = true ∨
      stage.val < (run input C.val .uncapped accounting actual (seed, world) (start + (n + 1 + exit))).cursor := by
    simpa only [Nat.add_assoc] using hexit
  have hone := minimal_run_stage_exit_cursor input C.val .uncapped accounting actual hl (seed, world)
    start (n + 1 + exit) stage ((congrArg State.halted hs0).trans ha) ((congrArg State.cursor hs0).trans hc) hbefore hexit'
  refine ⟨n + 1 + exit, hbefore, hone, ?_⟩
  rw [hpacket] at hfinal
  simpa only [Nat.add_assoc, sourceDrawStageExit] using congrArg (Prod.mk seed.1) hfinal

end PDROC
