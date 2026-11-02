module

public import PaperProofs.Paid.PDROC_Simulator_037
public import PaperProofs.Paid.PDROC_SimulatorLaw_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Deterministic realization of the full stage kernel at genuine actual
and source first entries. The source continuation witness uses the selected
auxiliary tape and the truth reconstructed after the actual endpoint report. -/
theorem simulator_stageExit_of_source_firstEntry (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (seed : SimulatorSeed P Seed) (world vworld : (P.input fee hfee).World)
    (astart vstart : ℕ) (stage : P.sharedInstance.Stage)
    (haentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage.val astart (seed, world))
    (hventry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      source stage.val vstart (seed.1, vworld))
    (hentry : (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) vstart).history =
      simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) astart).history)
    (htape : worldTapes (P.input fee hfee) vworld stage = seed.2.1 stage)
    (draw : SimulatorDraw P.sharedInstance)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) astart).history) = some draw)
    (htruth : (P.input fee hfee).truthAt vworld stage =
      recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
        (seed.2.2 stage, worldTapes (P.input fee hfee) world stage))
    (hfinite : ∃ n : ℕ, (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    ∃ finish : ℕ, astart ≤ finish ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) finish).halted = true ∨
        stage.val < (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) finish).cursor) ∧
      (seed.1, simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) finish).history) =
        sourceDrawStageExit source stage
          (((seed.1, simulatorShadow P fee hfee source seed
            (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
              (seed, world) astart).history), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
              (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let s := run input C.val .uncapped accounting actual (seed, world) astart
  have hla := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hla
    (seed, world) stage.val astart haentry
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hla (seed, world) astart
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual seed _ _ ap stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  have hsourceDraw : simulatorDrawAt P fee hfee source stage seed.1
      (run input C.val .uncapped accounting source (seed.1, vworld) vstart).history
      (worldTapes input vworld stage) = some draw := by
    rw [hentry, htape]
    exact hdraw
  have hcases := firstEntry_simulatorDrawAt_action_cases P fee hfee C accounting source hl
    (seed.1, vworld) vstart stage hventry draw hsourceDraw
  rcases hcases with ⟨decision, hwrite⟩ | hstop | habandon
  · obtain ⟨n, hn⟩ := hfinite
    let vterminal := vstart + draw.record.observations.length + 1
    have hpacket := firstEntry_sourceDrawTerminalHistory P fee hfee C accounting source hl
      (seed.1, vworld) vstart stage hventry draw hsourceDraw
    rw [hentry, htruth] at hpacket
    obtain ⟨vn, _, vp⟩ := run_has_prefix input C.val .uncapped accounting source hl (seed.1, vworld) vterminal
    obtain ⟨en, _, ep⟩ := run_has_prefix input C.val .uncapped accounting source hl (seed.1, vworld) vstart
    have hcursorEntry : historyCursor (run input C.val .uncapped accounting source (seed.1, vworld) vstart).history = stage.val :=
      (prefix_historyCursor input C.val .uncapped accounting source seed.1 _ _ ep).trans hventry.1
    have hcursorShadow : historyCursor (simulatorShadow P fee hfee source seed s.history) = stage.val := by
      rw [← hentry]
      exact hcursorEntry
    have hvc : (run input C.val .uncapped accounting source (seed.1, vworld) vterminal).cursor = stage.val := by
      rw [← prefix_historyCursor input C.val .uncapped accounting source seed.1 _ _ vp, ← hpacket]
      rw [sourceDrawTerminalHistory_write stage _ draw _ decision hwrite, historyCursor_append, historyCursor_append]
      have hz : historyCursor (simulatorReviewPacket stage draw.record) = 0 := by
        simp [historyCursor, simulatorReviewPacket, List.filterMap_map, Function.comp_def, eventAdvance]
      rw [hz, show historyCursor ([VisibleEvent.wrote stage decision _, .report stage _ _] : List (VisibleEvent P.sharedInstance)) = 0 from rfl]
      simpa only [Nat.add_zero] using hcursorShadow
    have hvw : (run input C.val .uncapped accounting source (seed.1, vworld) vterminal).ledger.written stage = some decision := by
      rw [← prefix_historyWritten input C.val .uncapped accounting source seed.1 _ _ vp stage, ← hpacket]
      rw [sourceDrawTerminalHistory_write stage _ draw _ decision hwrite]
      simp [historyWritten, historyWrite, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, eventWrite, List.getLast?_append]
    exact simulator_writing_stageExit_of_source_terminal P fee hfee C accounting source hl seed world vworld
      astart s stage draw decision rfl ha haentry.1 hw hr ho hdraw hwrite n hn vterminal hpacket.symm hvc hvw
  · obtain ⟨finish, hle, hh, heq⟩ := simulator_terminal_stageExit P fee hfee C accounting source seed world
      astart s stage draw false _ rfl ha haentry.1 hw hdraw (by simpa only [Bool.false_eq_true, ↓reduceIte] using hstop)
    exact ⟨finish, hle, Or.inl hh, heq⟩
  · obtain ⟨finish, hle, hh, heq⟩ := simulator_terminal_stageExit P fee hfee C accounting source seed world
      astart s stage draw true _ rfl ha haentry.1 hw hdraw habandon
    exact ⟨finish, hle, Or.inl hh, heq⟩

end PDROC
