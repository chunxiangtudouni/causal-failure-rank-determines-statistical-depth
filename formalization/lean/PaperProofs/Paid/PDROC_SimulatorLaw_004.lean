module

public import PaperProofs.Paid.PDROC_SimulatorLaw_001
public import PaperProofs.Paid.PDROC_SimulatorLaw_002
public import PaperProofs.Common.HistorySuffixRun

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def simulatorVirtualEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) : EntryHistory P.sharedInstance :=
  (entryHistory (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) stage sample).map
    (simulatorShadow P fee hfee source sample.1)

set_option maxHeartbeats 800000 in
theorem measurable_simulatorVirtualEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorVirtualEntry P fee hfee C accounting source stage) := by
  let build := fun pair : SimulatorSeed P Seed × EntryHistory P.sharedInstance =>
    pair.2.map (simulatorShadow P fee hfee source pair.1)
  have hb : Measurable build := by
    apply measurable_from_prod_countable_left
    intro entry
    cases entry with
    | none => exact measurable_const
    | some history =>
      change Measurable (fun seed : SimulatorSeed P Seed => some (simulatorShadow P fee hfee source seed history))
      have hjoint := measurable_simulatorShadow P fee hfee source hm
      have he : Measurable (fun seed : SimulatorSeed P Seed => (seed, history)) :=
        measurable_id.prodMk measurable_const
      have hs := hjoint.comp he
      change Measurable (fun seed : SimulatorSeed P Seed => simulatorShadow P fee hfee source seed history) at hs
      exact (measurable_of_countable (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp hs
  change Measurable (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
    build (sample.1, entryHistory (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) stage sample))
  have he := measurable_entryHistory (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) (measurable_simulatorRule P fee hfee source hm) stage
  have hp := measurable_fst.prodMk he
  exact hb.comp hp

theorem simulatorVirtualEntry_eq_off_target (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (target : P.sharedInstance.Stage)
    (seedA seedB : SimulatorSeed P Seed) (hseed : SimulatorSeedAgreeOff P target seedA seedB)
    (world : (P.input fee hfee).World) :
    simulatorVirtualEntry P fee hfee C accounting source target (seedA, world) =
      simulatorVirtualEntry P fee hfee C accounting source target (seedB, world) := by
  let input := P.input fee hfee
  let rule := simulatorRule P fee hfee source
  have hl := simulatorRule_legal P fee hfee C accounting source
  cases he : entryHistory input C.val .uncapped accounting rule target (seedA, world) with
  | none =>
    have he' : entryHistory input C.val .uncapped accounting rule target (seedB, world) = none := by
      cases hb : entryHistory input C.val .uncapped accounting rule target (seedB, world) with
      | none => rfl
      | some history =>
        obtain ⟨n, hn, hbefore, _⟩ := (entryHistory_some_iff input C.val .uncapped accounting rule target (seedB, world) history).mp hb
        have ha := (simulatorFirstEntry_transport_off_target P fee hfee C accounting source target seedB seedA hseed.symm world n ⟨hn, hbefore⟩).1
        exact False.elim ((entryHistory_none_iff input C.val .uncapped accounting rule target (seedA, world)).mp he ⟨n, ha.1⟩)
    change (entryHistory input C.val .uncapped accounting rule target (seedA, world)).map (simulatorShadow P fee hfee source seedA) =
      (entryHistory input C.val .uncapped accounting rule target (seedB, world)).map (simulatorShadow P fee hfee source seedB)
    rw [he, he']
    rfl
  | some history =>
    obtain ⟨n, hn, hbefore, hhistory⟩ := (entryHistory_some_iff input C.val .uncapped accounting rule target (seedA, world) history).mp he
    have hentry : FirstEntryAt input C.val .uncapped accounting rule target.val n (seedA, world) := ⟨hn, hbefore⟩
    obtain ⟨hentryB, hruns⟩ := simulatorFirstEntry_transport_off_target P fee hfee C accounting source target seedA seedB hseed world n hentry
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
    have hcache := simulatorReplay_eq_off_target (simulatorSeedDraw P fee hfee source) seedA seedB target history
      (simulatorSeedDraw_eq_off_target P fee hfee source target seedA seedB hseed) hw hh
    have hshadow : simulatorShadow P fee hfee source seedA history = simulatorShadow P fee hfee source seedB history :=
      congrArg SimulatorCache.shadow hcache
    change (entryHistory input C.val .uncapped accounting rule target (seedA, world)).map (simulatorShadow P fee hfee source seedA) =
      (entryHistory input C.val .uncapped accounting rule target (seedB, world)).map (simulatorShadow P fee hfee source seedB)
    rw [he, he']
    exact congrArg some hshadow

def simulatorDummyTape (P : PaperProofs.Paid.Parameters) : P.experiment.Tape := fun _ => (0 : Fin 2)

/-- Analysis-only measurable completion inserts fixed dummy current data.
It is not a simulator seed sampler or an oracle for the controller. -/
def completeSimulatorAllOther (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage)
    (past : (Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage) :
    SimulatorSeed P Seed × (P.input fee hfee).World :=
  ((past.1.1, ((fun i => if hi : i = stage then simulatorDummyTape P else past.1.2.1 ⟨i, hi⟩),
    (fun i => if hi : i = stage then false else past.1.2.2 ⟨i, hi⟩))),
    fun i => if hi : i = stage then (false, simulatorDummyTape P) else past.2 ⟨i, hi⟩)

theorem measurable_completeSimulatorAllOther (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) : Measurable (completeSimulatorAllOther (Seed := Seed) P fee hfee stage) := by
  have ht : Measurable (fun past : (Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage =>
      fun i => if hi : i = stage then simulatorDummyTape P else past.1.2.1 ⟨i, hi⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [dite_eq_left hi]; exact measurable_const
    · simp only [dite_eq_right hi]; fun_prop
  have hb : Measurable (fun past : (Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage =>
      fun i => if hi : i = stage then false else past.1.2.2 ⟨i, hi⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [dite_eq_left hi]; exact measurable_const
    · simp only [dite_eq_right hi]; fun_prop
  have hw : Measurable (fun past : (Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage =>
      fun i => if hi : i = stage then (false, simulatorDummyTape P) else past.2 ⟨i, hi⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [dite_eq_left hi]; exact measurable_const
    · simp only [dite_eq_right hi]; fun_prop
  exact ((measurable_fst.comp measurable_fst).prodMk (ht.prodMk hb)).prodMk hw

noncomputable def simulatorVirtualEntryGate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) : Seed × EntryHistory P.sharedInstance :=
  (sample.1.1, simulatorVirtualEntry P fee hfee C accounting source stage sample)

noncomputable def simulatorVirtualEntryFactor (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) :=
  simulatorVirtualEntryGate P fee hfee C accounting source stage ∘ completeSimulatorAllOther P fee hfee stage

theorem simulatorVirtualEntryGate_factorization (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    simulatorVirtualEntryGate P fee hfee C accounting source stage sample =
      simulatorVirtualEntryFactor P fee hfee C accounting source stage (simulatorAllOther P fee hfee stage sample) := by
  let completed := completeSimulatorAllOther P fee hfee stage (simulatorAllOther P fee hfee stage sample)
  have hseed : SimulatorSeedAgreeOff P stage sample.1 completed.1 := by
    constructor
    · rfl
    · intro i hi
      constructor <;> simp only [completed, completeSimulatorAllOther, simulatorAllOther, simulatorOtherNoise, dite_eq_right hi]
  have hpast : ∀ i : P.sharedInstance.Stage, i.val < stage.val → completed.2 i = sample.2 i := by
    intro i hi
    have hne : i ≠ stage := by intro heq; subst i; omega
    simp only [completed, completeSimulatorAllOther, simulatorAllOther, dite_eq_right hne]
  have hentry := entryHistory_eq_of_past (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) (simulatorRule_legal P fee hfee C accounting source)
    sample.1 sample.2 completed.2 stage hpast
  have hworld : simulatorVirtualEntry P fee hfee C accounting source stage (sample.1, completed.2) =
      simulatorVirtualEntry P fee hfee C accounting source stage sample :=
    congrArg (fun entry : EntryHistory P.sharedInstance => entry.map (simulatorShadow P fee hfee source sample.1)) hentry
  have hnoise := simulatorVirtualEntry_eq_off_target P fee hfee C accounting source stage sample.1 completed.1 hseed completed.2
  exact Prod.ext rfl (hworld.symm.trans hnoise)

/-- Concrete generated virtual entry, together with the ORIGINAL old seed,
is independent of all current auxiliary/coin/actual-stage randomness. -/
theorem simulatorVirtualEntry_joint_freshStage (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (simulatorVirtualEntryGate P fee hfee C accounting source stage sample,
        simulatorFreshStage P fee hfee stage sample)) =
      ((simulatorAllOtherLaw P fee hfee ν stage).map
        (simulatorVirtualEntryFactor P fee hfee C accounting source stage)).prod
        (((auxiliaryTapeLaw P).prod PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw).prod
          ((P.input fee hfee).stageLaw stage)) := by
  have hg : Measurable (simulatorVirtualEntryFactor P fee hfee C accounting source stage) :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_simulatorVirtualEntry P fee hfee C accounting source hm stage)).comp
      (measurable_completeSimulatorAllOther P fee hfee stage)
  have h := simulatorWorldLaw_pastGate_freshStage P fee hfee ν stage
    (simulatorVirtualEntryFactor P fee hfee C accounting source stage) hg
  have heq : (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
      (simulatorVirtualEntryGate P fee hfee C accounting source stage sample, simulatorFreshStage P fee hfee stage sample)) =
      (fun sample => (simulatorVirtualEntryFactor P fee hfee C accounting source stage
        (simulatorAllOther P fee hfee stage sample), simulatorFreshStage P fee hfee stage sample)) := by
    funext sample
    rw [simulatorVirtualEntryGate_factorization]
  rw [← heq] at h
  exact h

end PDROC




