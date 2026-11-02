module

public import PaperProofs.Paid.PDROC_OverlaySimulator_004
public import PaperProofs.Paid.PDROC_Simulator_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

instance overlayGhostChoiceMeasurable (I : Instance) : MeasurableSpace (Option (OverlayGhostCall I)) := ⊤

instance overlayGhostChoiceSingleton (I : Instance) : MeasurableSingletonClass (Option (OverlayGhostCall I)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

universe u
variable {I : Instance} {Seed : Type u}

def overlayGhostAction (call : OverlayGhostCall I) : Action I :=
  if call.1 then .allocate call.2.1 call.2.2 else .execute call.2.1 call.2.2

/-- Ghost calls are selected solely from a permission-checked SOURCE action.
They are never supplied to the physical Native execution. -/
def overlayGhostCallOfAction (virtual : List (VisibleEvent I)) (action : Action I) : Option (OverlayGhostCall I) :=
  if historyAllowsAction virtual action then
    match action with
    | .allocate handle tool => some (true, handle, tool)
    | .execute handle tool => some (false, handle, tool)
    | _ => none
  else none

theorem overlayGhostCallOfAction_some (virtual : List (VisibleEvent I)) (action : Action I)
    (call : OverlayGhostCall I) (h : overlayGhostCallOfAction virtual action = some call) :
    action = overlayGhostAction call ∧ historyAllowsAction virtual action := by
  unfold overlayGhostCallOfAction at h
  split at h
  next hallow =>
    cases action <;> simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst call; exact ⟨rfl, hallow⟩
  next hnot => simp at h

def overlayGhostCalls (fuel : ℕ) (source : PolicyRule I Seed) (seed : Seed)
    (virtual : List (VisibleEvent I)) : List (OverlayGhostCall I) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match overlayGhostCallOfAction virtual (source seed virtual) with
    | none => []
    | some call => call :: overlayGhostCalls fuel source seed (virtual ++ overlayGhostEvents [call])

theorem overlayGhostCalls_length_le (fuel : ℕ) (source : PolicyRule I Seed) (seed : Seed)
    (virtual : List (VisibleEvent I)) :
    (overlayGhostCalls fuel source seed virtual).length ≤ fuel := by
  induction fuel generalizing virtual with
  | zero => simp [overlayGhostCalls]
  | succ fuel ih =>
    simp only [overlayGhostCalls]
    cases h : overlayGhostCallOfAction virtual (source seed virtual) with
    | none => simp
    | some call => exact Nat.succ_le_succ (ih _)

def OverlayGhostTrace (source : PolicyRule I Seed) (seed : Seed)
    (virtual : List (VisibleEvent I)) : List (OverlayGhostCall I) → Prop
  | [] => True
  | call :: rest =>
    source seed virtual = overlayGhostAction call ∧
      historyAllowsAction virtual (source seed virtual) ∧
      OverlayGhostTrace source seed (virtual ++ overlayGhostEvents [call]) rest

/-- Every virtual-only call is an actual next source action with the original
visible permission. No success, free handle, or unpaid physical call is
assumed by this trace. -/
theorem overlayGhostCalls_trace (fuel : ℕ) (source : PolicyRule I Seed) (seed : Seed)
    (virtual : List (VisibleEvent I)) :
    OverlayGhostTrace source seed virtual (overlayGhostCalls fuel source seed virtual) := by
  induction fuel generalizing virtual with
  | zero => trivial
  | succ fuel ih =>
    simp only [overlayGhostCalls]
    cases h : overlayGhostCallOfAction virtual (source seed virtual) with
    | none => trivial
    | some call =>
      have hc := overlayGhostCallOfAction_some virtual (source seed virtual) call h
      exact ⟨hc.1, hc.2, ih _⟩

def overlayHasActualMismatch (actual : List (VisibleEvent I)) : Bool :=
  match simulatorStageAt actual with
  | none => false
  | some stage => decide (historyValidHandle actual ⟨stage, historyWriteSerial actual stage⟩)

def overlayGhostAtCache (source : PolicyRule I Seed) (seed : Seed) (cache : SimulatorCache I) :
    List (OverlayGhostCall I) :=
  if overlayHasActualMismatch cache.seen then [] else overlayGhostCalls 2 source seed cache.shadow

theorem overlayGhostAtCache_length (source : PolicyRule I Seed) (seed : Seed) (cache : SimulatorCache I) :
    (overlayGhostAtCache source seed cache).length ≤ 2 := by
  unfold overlayGhostAtCache
  split
  · exact Nat.zero_le 2
  · exact overlayGhostCalls_length_le 2 source seed cache.shadow

theorem overlayGhostAtCache_actualMismatch (source : PolicyRule I Seed) (seed : Seed) (cache : SimulatorCache I)
    (h : overlayHasActualMismatch cache.seen = true) : overlayGhostAtCache source seed cache = [] := by
  simp only [overlayGhostAtCache, h, ite_true]

section Measurable

variable [MeasurableSpace Seed]

theorem measurable_overlayGhostCalls (fuel : ℕ) (source : PolicyRule I Seed) (hm : MeasurableRule source) :
    Measurable (fun pair : Seed × List (VisibleEvent I) => overlayGhostCalls fuel source pair.1 pair.2) := by
  induction fuel with
  | zero => exact measurable_const
  | succ fuel ih =>
    let next : Seed × List (VisibleEvent I) → Option (OverlayGhostCall I) :=
      fun pair => overlayGhostCallOfAction pair.2 (source pair.1 pair.2)
    have hn : Measurable next :=
      (measurable_of_countable (fun data : List (VisibleEvent I) × Action I =>
        overlayGhostCallOfAction data.1 data.2)).comp (measurable_snd.prodMk hm)
    have hfixed (call : Option (OverlayGhostCall I)) :
        Measurable (fun pair : Seed × List (VisibleEvent I) =>
          match call with
          | none => ([] : List (OverlayGhostCall I))
          | some call => call :: overlayGhostCalls fuel source pair.1 (pair.2 ++ overlayGhostEvents [call])) := by
      cases call with
      | none => exact measurable_const
      | some call =>
        exact (measurable_of_countable (List.cons call)).comp (ih.comp
          (measurable_fst.prodMk ((measurable_of_countable
            (fun virtual : List (VisibleEvent I) => virtual ++ overlayGhostEvents [call])).comp measurable_snd)))
    have hprod : Measurable (fun pair : (Seed × List (VisibleEvent I)) × Option (OverlayGhostCall I) =>
        match pair.2 with
        | none => ([] : List (OverlayGhostCall I))
        | some call => call :: overlayGhostCalls fuel source pair.1.1 (pair.1.2 ++ overlayGhostEvents [call])) :=
      measurable_from_prod_countable_left hfixed
    exact hprod.comp (measurable_id.prodMk hn)

theorem measurable_overlayGhostAtCache_fixed (source : PolicyRule I Seed) (hm : MeasurableRule source)
    (cache : SimulatorCache I) : Measurable (fun seed => overlayGhostAtCache source seed cache) := by
  unfold overlayGhostAtCache
  split
  · exact measurable_const
  · exact (measurable_overlayGhostCalls 2 source hm).comp (measurable_id.prodMk measurable_const)

end Measurable

end PDROC
