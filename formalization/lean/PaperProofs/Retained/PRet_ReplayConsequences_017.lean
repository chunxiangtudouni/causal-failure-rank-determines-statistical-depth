module

public import PaperProofs.Retained.PRet_ReplayInvariant_016
public import PaperProofs.Common.NativeCostBound

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetReplayConsequences017

open Common Common.Native MeasureTheory
open PRetExactTerminal001 PRetInformationPackets006 PRetReplayInvariant016

variable {I : Instance}

def extractHistory (startup : Option (Startup I)) : List (VisibleEvent I) :=
  match startup with
  | none => []
  | some startup => startup.history

noncomputable def shadowHistory {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (history : List (VisibleEvent I)) : List (VisibleEvent I) :=
  extractHistory (shadow accounting source seed history)

theorem measurable_shadowHistory {Seed : Type*} [MeasurableSpace Seed]
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (hsource : MeasurableRule source) :
    Measurable (fun sample : Seed × List (VisibleEvent I) => shadowHistory accounting source sample.1 sample.2) :=
  (measurable_of_countable extractHistory).comp (measurable_shadow accounting source hsource)

theorem pair_charge_prefix (input : StatisticalInput I) (first later : List (I.Stage × I.Tool))
    (hp : first.IsPrefix later) :
    (first.map (pairCharge input)).sum ≤ (later.map (pairCharge input)).sum := by
  obtain ⟨suffix, rfl⟩ := hp
  rw [List.map_append, List.sum_append]
  exact le_self_add

theorem ledger_bill_le (input : StatisticalInput I) (target source : Ledger I)
    (hreviews : target.reviews = source.reviews)
    (hpairs : (target.executions.map executionPair).IsPrefix (source.executions.map executionPair)) :
    target.actualBill input.fees ≤ source.actualBill input.fees := by
  have hcorrect : target.correctionBill input.fees ≤ source.correctionBill input.fees := by
    simpa only [List.map_map, Function.comp_def, executionPair, pairCharge, Ledger.correctionBill] using
      pair_charge_prefix input _ _ hpairs
  have hobservation : target.observationBill input.fees = source.observationBill input.fees := by
    unfold Ledger.observationBill
    rw [hreviews]
  unfold Ledger.actualBill
  rw [hobservation]
  exact add_le_add le_rfl hcorrect

/-- Exact original R02 shadow-history conclusion, conditional only on the
actual induction fact. Proving that fact for every target run is separate;
this theorem is not reported as complete NativeRearrangement. -/
theorem shadow_of_replayInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (target : State I)
    (hinvariant : ReplayInvariant input C mode accounting source sample target) :
    ∃ oldClock,
      shadowHistory accounting source sample.1 target.history =
        (run input C mode accounting source sample oldClock).history ∧
      informationTrace (shadowHistory accounting source sample.1 target.history) = informationTrace target.history := by
  obtain ⟨packets, oldClock, hinfo, hreplay, _, _, _⟩ := hinvariant
  have hshadow : shadow accounting source sample.1 target.history =
      some (publicStartup (run input C mode accounting source sample oldClock)) := by
    unfold shadow
    rw [hinfo, parse_packets]
    exact hreplay
  have hhistory : shadowHistory accounting source sample.1 target.history =
      (run input C mode accounting source sample oldClock).history := by
    rw [shadowHistory, hshadow]
    rfl
  refine ⟨oldClock, hhistory, ?_⟩
  rw [hhistory]
  exact (replay_information accounting source sample.1 packets _ hreplay).trans hinfo.symm

/-- Every target prefix bill is dominated by a genuine source prefix bill;
failed, abandoned and nonreturning paths are not discarded or assigned zero. -/
theorem actualBill_le_of_replayInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (target : State I)
    (hinvariant : ReplayInvariant input C mode accounting source sample target) :
    target.ledger.actualBill input.fees ≤ runActualBill input C mode accounting source sample := by
  obtain ⟨_, oldClock, _, _, hreviews, _, hpairs⟩ := hinvariant
  exact (ledger_bill_le input _ _ hreviews hpairs).trans
    (prefixBill_le_runActualBill input C mode accounting source sample oldClock)

theorem observationBill_le_of_replayInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (target : State I)
    (hinvariant : ReplayInvariant input C mode accounting source sample target) :
    target.ledger.observationBill input.fees ≤ runObservationBill input C mode accounting source sample := by
  obtain ⟨_, oldClock, _, _, hreviews, _, _⟩ := hinvariant
  have hobs : target.ledger.observationBill input.fees =
      (run input C mode accounting source sample oldClock).ledger.observationBill input.fees := by
    unfold Ledger.observationBill
    rw [hreviews]
  rw [hobs]
  exact le_iSup (fun n => (run input C mode accounting source sample n).ledger.observationBill input.fees) oldClock

end PaperProofs.Retained.PRetReplayConsequences017
