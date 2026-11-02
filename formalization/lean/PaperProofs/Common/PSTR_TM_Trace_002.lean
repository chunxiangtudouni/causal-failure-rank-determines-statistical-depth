module
public import PaperProofs.Common.RationalControllerComputation
public import Mathlib.Data.List.Chain

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrace002
open PaperProofs.Common.Native.RationalControllerComputation

theorem displacement_bounds {states : Nat} (machine : Machine states) (state : MachineState states) :
    -1 ≤ displacement machine state ∧ displacement machine state ≤ 1 := by
  unfold displacement
  split <;> norm_num

theorem scanl_bounds (ds : List Int) (hb : ∀ d ∈ ds, -1 ≤ d ∧ d ≤ 1)
    (z p : Int) (hp : p ∈ ds.scanl (· + ·) z) :
    z - ds.length ≤ p ∧ p ≤ z + ds.length := by
  induction ds generalizing z with
  | nil => simp_all
  | cons d ds ih =>
    simp only [List.scanl_cons, List.mem_cons] at hp
    have hd := hb d (by simp)
    rcases hp with rfl | hp
    · simp only [List.length_cons]; omega
    · have hs := ih (fun x hx => hb x (by simp [hx])) (z + d) hp
      simp only [List.length_cons]; push_cast; omega

theorem foldl_max_le (ps : List Int) (z bound : Int) (hz : z ≤ bound)
    (hp : ∀ p ∈ ps, p ≤ bound) : ps.foldl max z ≤ bound := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    apply ih (max z p) (max_le hz (hp p (by simp)))
    intro x hx
    exact hp x (by simp [hx])

theorem le_foldl_min (ps : List Int) (z bound : Int) (hz : bound ≤ z)
    (hp : ∀ p ∈ ps, bound ≤ p) : bound ≤ ps.foldl min z := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    apply ih (min z p) (le_min hz (hp p (by simp)))
    intro x hx
    exact hp x (by simp [hx])

/-- Peak visited tape cells follow from the actual TM's unit head movements.
This theorem does not assume validity or a supplied cost certificate. -/
theorem visitedSpace_le {states : Nat} (machine : Machine states) (inputLength : Nat)
    (trace : List (MachineState states)) :
    visitedSpace machine inputLength trace ≤ inputLength + 2 * trace.length + 1 := by
  let ds := trace.map (displacement machine)
  let ps := ds.scanl (· + ·) 0
  have hb : ∀ d ∈ ds, -1 ≤ d ∧ d ≤ 1 := by
    intro d hd
    obtain ⟨state, _, rfl⟩ := List.mem_map.mp hd
    exact displacement_bounds machine state
  have hp (p : Int) (h : p ∈ ps) : -(trace.length : Int) ≤ p ∧ p ≤ trace.length := by
    simpa [ds] using scanl_bounds ds hb 0 p h
  have hh : ps.foldl max (inputLength : Int) ≤ (inputLength : Int) + trace.length := by
    apply foldl_max_le
    · omega
    · intro p h
      have := (hp p h).2
      omega
  have hl : -(trace.length : Int) ≤ ps.foldl min 0 := by
    apply le_foldl_min
    · omega
    · intro p h
      exact (hp p h).1
  change (ps.foldl max (inputLength : Int) - ps.foldl min 0).toNat + 1 ≤ _
  omega

/-- Every real chain with the stated endpoints reaches its final state. -/
theorem chain_reaches {α : Type*} (step : α → Option α) (trace : List α) (initial final : α)
    (hh : trace.head? = some initial)
    (hc : trace.IsChain (fun a b => step a = some b))
    (hl : trace.getLast? = some final) : StateTransition.Reaches step initial final := by
  induction trace generalizing initial with
  | nil => simp at hh
  | cons a trace ih =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst a
    cases trace with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst final
      exact .refl
    | cons b bs =>
      have hstep : step initial = some b := (List.isChain_cons_cons.mp hc).1
      have htail := (List.isChain_cons_cons.mp hc).2
      exact Relation.ReflTransGen.head hstep (ih b (by rfl) htail (by simpa using hl))

/-- The eval clause of the original B23/D27 run format is derived from
actual transitions and HALT; no semantic oracle is required. -/
theorem runs_of_chain {states : Nat} (machine : Machine states) (input : List Bool)
    (trace : List (MachineState states)) (final : MachineState states)
    (hh : trace.head? = some (Turing.TM0.init input))
    (hc : trace.IsChain (fun a b => Turing.TM0.step machine a = some b))
    (hl : trace.getLast? = some final) (halt : Turing.TM0.step machine final = none) :
    Runs machine input trace final :=
  ⟨hh, hc, hl, halt, StateTransition.mem_eval.mpr ⟨chain_reaches _ _ _ _ hh hc hl, halt⟩⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrace002
