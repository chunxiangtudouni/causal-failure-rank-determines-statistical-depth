module

public import PaperProofs.Paid.PDROC_LocalRecord_001
public import PaperProofs.Common.ReferenceController

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- The simulator seed contains only the old seed, auxiliary tapes, and
independent endpoint tie coins. There is no truth coordinate. -/
abbrev SimulatorSeed (P : PaperProofs.Paid.Parameters) (Seed : Type u) :=
  Seed × ((P.sharedInstance.Stage → P.experiment.Tape) × (P.sharedInstance.Stage → Bool))

structure SimulatorDraw (I : Instance) where
  record : AuxiliaryRecord
  action : Action I
  deriving Countable

instance simulatorDrawMeasurable (I : Instance) : MeasurableSpace (SimulatorDraw I) := ⊤
instance simulatorDrawSingleton (I : Instance) : MeasurableSingletonClass (SimulatorDraw I) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance simulatorOptionDrawMeasurable (I : Instance) : MeasurableSpace (Option (SimulatorDraw I)) := ⊤
instance simulatorOptionDrawSingleton (I : Instance) : MeasurableSingletonClass (Option (SimulatorDraw I)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

variable {Seed : Type u} [MeasurableSpace Seed]

local instance : MeasurableSpace (List (Fin 2)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 2)) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def simulatorPrewriteRule (P : PaperProofs.Paid.Parameters) (source : PolicyRule P.sharedInstance Seed) :
    PolicyRule P.sharedInstance (Seed × List (VisibleEvent P.sharedInstance)) :=
  fun seed localHistory => source seed.1 (seed.2 ++ localHistory)

theorem measurable_simulatorPrewriteRule (P : PaperProofs.Paid.Parameters)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    MeasurableRule (simulatorPrewriteRule P source) := by
  have hh : Measurable (fun pair : (Seed × List (VisibleEvent P.sharedInstance)) ×
      List (VisibleEvent P.sharedInstance) => pair.1.2 ++ pair.2) :=
    (measurable_of_countable (fun pair : List (VisibleEvent P.sharedInstance) ×
      List (VisibleEvent P.sharedInstance) => pair.1 ++ pair.2)).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact hm.comp ((measurable_fst.comp measurable_fst).prodMk hh)

/-- Actual prewrite sampling from an auxiliary tape. The first non-review
action is retained, so stop and abandonment remain distinct. Outer none
denotes genuine nonreturn; no performance conclusion is assumed. -/
noncomputable def simulatorDrawAt (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (seed : Seed) (entry : List (VisibleEvent P.sharedInstance)) (tape : P.experiment.Tape) :
    Option (SimulatorDraw P.sharedInstance) :=
  let stop := headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape
  if stop = ⊤ then none else
    let n := stop.toNat
    let action := source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n)
    some ⟨⟨List.ofFn (fun k : Fin n => tape k.val), optionWriteBit action⟩, action⟩

theorem measurable_simulatorDrawAt (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (fun pair : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
      simulatorDrawAt P fee hfee source stage pair.1.1 pair.1.2 pair.2) := by
  let stop := fun pair : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
    headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) pair.1 pair.2
  have hs : Measurable stop := measurable_headExitStop (P.input fee hfee) stage
    (simulatorPrewriteRule P source) (measurable_simulatorPrewriteRule P source hm)
  have hn : Measurable (fun pair => (stop pair).toNat) := (measurable_of_countable ENat.toNat).comp hs
  have hfinite : ∀ n : ℕ, Measurable (fun pair : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
      (some {
        record := ⟨List.ofFn (fun k : Fin n => pair.2 k.val),
          optionWriteBit (source pair.1.1 (pair.1.2 ++ headReviewHistory (P.input fee hfee) stage pair.2 n))⟩
        action := source pair.1.1 (pair.1.2 ++ headReviewHistory (P.input fee hfee) stage pair.2 n)
      } : Option (SimulatorDraw P.sharedInstance))) := by
    intro n
    have hw : Measurable (fun tape : P.experiment.Tape => (List.ofFn (fun k : Fin n => tape k.val) : List (Fin 2))) := by
      exact (measurable_of_countable (fun word : Fin n → Fin 2 => List.ofFn word)).comp
        (measurable_pi_iff.mpr fun k => measurable_pi_apply k.val)
    have ha : Measurable (fun pair : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
        source pair.1.1 (pair.1.2 ++ headReviewHistory (P.input fee hfee) stage pair.2 n)) :=
      (measurable_simulatorPrewriteRule P source hm).comp
        (measurable_fst.prodMk ((measurable_headReviewHistory (P.input fee hfee) stage n).comp measurable_snd))
    exact (measurable_of_countable (fun pair : List (Fin 2) × Action P.sharedInstance =>
      (some (⟨⟨pair.1, optionWriteBit pair.2⟩, pair.2⟩ : SimulatorDraw P.sharedInstance)))).comp
        ((hw.comp measurable_snd).prodMk ha)
  have hbuild : Measurable (fun pair : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) × ℕ =>
      (some {
        record := ⟨List.ofFn (fun k : Fin pair.2 => pair.1.2 k.val),
          optionWriteBit (source pair.1.1.1 (pair.1.1.2 ++ headReviewHistory (P.input fee hfee) stage pair.1.2 pair.2))⟩
        action := source pair.1.1.1 (pair.1.1.2 ++ headReviewHistory (P.input fee hfee) stage pair.1.2 pair.2)
      } : Option (SimulatorDraw P.sharedInstance))) :=
    measurable_from_prod_countable_left hfinite
  have hall := hbuild.comp (measurable_id.prodMk hn)
  exact measurable_const.ite (hs (measurableSet_singleton (⊤ : ℕ∞))) hall

end PDROC
