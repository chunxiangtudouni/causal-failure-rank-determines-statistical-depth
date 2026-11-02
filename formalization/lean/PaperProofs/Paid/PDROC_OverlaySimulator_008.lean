module

public import PaperProofs.Paid.PDROC_OverlaySimulator_007
public import PaperProofs.Paid.PDROC_OverlayCoins_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- Private state contains the old private seed, auxiliary tapes and
independent record-indexed coin tables, with no latent truth coordinate. -/
abbrev OverlaySeed (P : Parameters) (Seed : Type u) :=
  Seed × ((P.sharedInstance.Stage → P.experiment.Tape) × OverlayCoinTables P)

variable {Seed : Type u} [MeasurableSpace Seed]

def overlaySeedCoins (P : Parameters) (seed : OverlaySeed P Seed)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) : Bool × Bool :=
  (seed.2.2 stage).1 record

def overlaySeedMark (P : Parameters) (seed : OverlaySeed P Seed)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) : Bool :=
  (seed.2.2 stage).2 record

theorem measurable_overlaySeedCoins (P : Parameters) (stage : P.sharedInstance.Stage) :
    Measurable (fun pair : OverlaySeed P Seed × AuxiliaryRecord => overlaySeedCoins P pair.1 stage pair.2) := by
  apply measurable_from_prod_countable_left
  intro record
  exact (measurable_pi_apply record).comp (measurable_fst.comp
    ((measurable_pi_apply stage).comp (measurable_snd.comp measurable_snd)))

theorem measurable_overlaySeedMark (P : Parameters) (stage : P.sharedInstance.Stage) :
    Measurable (fun pair : OverlaySeed P Seed × AuxiliaryRecord => overlaySeedMark P pair.1 stage pair.2) := by
  apply measurable_from_prod_countable_left
  intro record
  exact (measurable_pi_apply record).comp (measurable_snd.comp
    ((measurable_pi_apply stage).comp (measurable_snd.comp measurable_snd)))

noncomputable def overlaySeedDraw (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance)) :
    Option (SimulatorDraw P.sharedInstance) :=
  simulatorDrawAt P 0 (by norm_num) source stage seed.1 entry (seed.2.1 stage)

theorem measurable_overlaySeedDraw (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (fun pair : OverlaySeed P Seed × List (VisibleEvent P.sharedInstance) =>
      overlaySeedDraw P source pair.1 stage pair.2) := by
  have ht : Measurable (fun pair : OverlaySeed P Seed × List (VisibleEvent P.sharedInstance) =>
      pair.1.2.1 stage) :=
    (measurable_pi_apply stage).comp ((measurable_fst.comp measurable_snd).comp measurable_fst)
  exact (measurable_simulatorDrawAt P 0 (by norm_num) source hm stage).comp
    (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk ht)

def overlaySeedGhost (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (cache : SimulatorCache P.sharedInstance) :
    List (OverlayGhostCall P.sharedInstance) :=
  overlayGhostAtCache source seed.1 cache

noncomputable def overlaySeedReplay (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (history : List (VisibleEvent P.sharedInstance)) : SimulatorCache P.sharedInstance :=
  overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed history

theorem measurable_overlaySeedReplay (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) :
    Measurable (fun pair : OverlaySeed P Seed × List (VisibleEvent P.sharedInstance) =>
      overlaySeedReplay P source pair.1 pair.2) := by
  exact measurable_overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
    (measurable_overlaySeedDraw P source hm)
    (fun stage record => (measurable_overlaySeedMark P stage).comp (measurable_id.prodMk measurable_const))
    (fun cache => (measurable_overlayGhostAtCache_fixed source hm cache).comp measurable_fst)

noncomputable def overlayShadow (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (history : List (VisibleEvent P.sharedInstance)) : List (VisibleEvent P.sharedInstance) :=
  (overlaySeedReplay P source seed history).shadow

theorem measurable_overlayShadow (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) :
    Measurable (fun pair : OverlaySeed P Seed × List (VisibleEvent P.sharedInstance) =>
      overlayShadow P source pair.1 pair.2) :=
  (measurable_of_countable (SimulatorCache.shadow (I := P.sharedInstance))).comp
    (measurable_overlaySeedReplay P source hm)

end PDROC
