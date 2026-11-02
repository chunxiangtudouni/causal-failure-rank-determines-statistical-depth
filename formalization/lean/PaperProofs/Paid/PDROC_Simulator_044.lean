module

public import PaperProofs.Paid.PDROC_Simulator_043
public import PaperProofs.Paid.PDROC_SimulatorLaw_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The complete original actual stage is realized at its genuine FIRST
exit on the measurable source-draw guard event. Only the finite observable
source guard predicate is transported under a kernel law. -/
theorem simulator_stageExit_minimal_of_sourceDrawGuardGood (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage.val start (seed, world))
    (draw : SimulatorDraw P.sharedInstance)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).history) = some draw)
    (hfinite : ∃ n : ℕ, (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (hgood : sourceDrawGuardGood source stage
      (((seed.1, simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) start).history), draw),
        recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
          (seed.2.2 stage, worldTapes (P.input fee hfee) world stage))) :
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
          (((seed.1, simulatorShadow P fee hfee source seed
            (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
              (seed, world) start).history), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
              (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let s := run input C.val .uncapped accounting actual (seed, world) start
  have hl := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl
    (seed, world) stage.val start hentry
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) start
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual seed _ _ ap stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  rcases hgood with ⟨hshape, hpost⟩
  rcases hshape with ⟨decision, hwrite⟩ | hstop | habandon
  · obtain ⟨n, hn⟩ := hfinite
    exact simulator_writing_stageExit_minimal_of_guardGood P fee hfee C accounting source seed world
      start s stage draw decision rfl ha hentry.1 hw hr ho hdraw hwrite n hn hpost
  · have ht := simulator_terminal_record_shadow_packet P fee hfee C accounting source seed world start s stage draw false
      (recordVirtualTruth P draw.record (input.truthAt world stage) (seed.2.2 stage, worldTapes input world stage))
      rfl ha hentry.1 hw hdraw (by simpa only [Bool.false_eq_true, ↓reduceIte] using hstop)
    refine ⟨1, ?_, Or.inl ht.1, ?_⟩
    · intro k hk
      have hz : k = 0 := by omega
      subst k
      simpa only [Nat.add_zero] using And.intro ha hentry.1
    · rw [sourceDrawStageExit_terminal source seed.1 stage _ draw false _ (by simpa only [Bool.false_eq_true, ↓reduceIte] using hstop)]
      exact congrArg (Prod.mk seed.1) ht.2
  · have ht := simulator_terminal_record_shadow_packet P fee hfee C accounting source seed world start s stage draw true
      (recordVirtualTruth P draw.record (input.truthAt world stage) (seed.2.2 stage, worldTapes input world stage))
      rfl ha hentry.1 hw hdraw habandon
    refine ⟨1, ?_, Or.inl ht.1, ?_⟩
    · intro k hk
      have hz : k = 0 := by omega
      subst k
      simpa only [Nat.add_zero] using And.intro ha hentry.1
    · rw [sourceDrawStageExit_terminal source seed.1 stage _ draw true _ habandon]
      exact congrArg (Prod.mk seed.1) ht.2

end PDROC
