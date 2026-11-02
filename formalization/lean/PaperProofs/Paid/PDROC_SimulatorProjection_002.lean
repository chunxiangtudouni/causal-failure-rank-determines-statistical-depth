module

public import PaperProofs.Paid.PDROC_SimulatorProjection_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem reserial_pairLists_of_stageTool_projection
    (target : List (VisibleEvent I)) (actual virtual : List (MismatchHandle I × I.Tool))
    (hp : actual.map (fun pair => (pair.1.stage, pair.2)) =
      virtual.map (fun pair => (pair.1.stage, pair.2)))
    (hserial : ∀ pair ∈ actual, pair.1.writeSerial = historyWriteSerial target pair.1.stage) :
    actual = virtual.map (fun pair => (reserialHandle target pair.1, pair.2)) := by
  have hframe : actual.map (fun pair => (reserialHandle target pair.1, pair.2)) = actual := by
    calc
      _ = actual.map id := by
        apply List.map_congr_left
        intro pair hm
        have hh : reserialHandle target pair.1 = pair.1 := by
          cases hpair : pair.1 with
          | mk stage serial =>
            have hs := hserial pair hm
            rw [hpair] at hs
            simp only [reserialHandle]
            congr
            exact hs.symm
        exact congrArg (fun handle => (handle, pair.2)) hh
      _ = actual := List.map_id _
  have h := congrArg (List.map (fun pair : I.Stage × I.Tool =>
    ((⟨pair.1, historyWriteSerial target pair.1⟩ : MismatchHandle I), pair.2))) hp
  simp only [List.map_map, Function.comp_def] at h
  exact hframe.symm.trans h

theorem prefix_simulatorCommitments_reserial (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed SimSeed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (simseed : SimSeed) :
    historyCommitments s.history =
      (historyCommitments (simulatorReplay draw simseed s.history).shadow).map
        (fun pair => (reserialHandle s.history pair.1, pair.2)) := by
  apply reserial_pairLists_of_stageTool_projection s.history
  · exact (simulatorReplay_sameProjection draw simseed s.history).2.1
  · intro pair hpair
    rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hpair
    obtain ⟨commitment, hc, rfl⟩ := List.mem_map.mp hpair
    exact ((prefix_invariant input C mode accounting rule seed truth tapes hp).commitment_genuine commitment hc).2.trans
      (prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp commitment.handle.stage).symm

theorem prefix_simulatorExecutions_reserial (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed SimSeed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (simseed : SimSeed) :
    historyExecutions s.history =
      (historyExecutions (simulatorReplay draw simseed s.history).shadow).map
        (fun pair => (reserialHandle s.history pair.1, pair.2)) := by
  apply reserial_pairLists_of_stageTool_projection s.history
  · exact (simulatorReplay_sameProjection draw simseed s.history).2.2.1
  · intro pair hpair
    rw [prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at hpair
    obtain ⟨execution, he, rfl⟩ := List.mem_map.mp hpair
    exact ((prefix_invariant input C mode accounting rule seed truth tapes hp).wellFormed.genuine execution he).2.trans
      (prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp execution.handle.stage).symm

end PDROC
