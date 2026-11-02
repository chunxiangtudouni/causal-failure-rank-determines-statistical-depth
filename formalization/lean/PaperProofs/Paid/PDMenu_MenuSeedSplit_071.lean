module

public import PaperProofs.Paid.MenuCompiler
public import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory

namespace PDMenu

open PaperProofs.Paid

def menuStageAt (n K : ℕ) (i : Fin n) : (freshInstance n K).Stage :=
  ⟨i.val, by simp [freshInstance]⟩

def menuSeedFinEquiv (n K : ℕ) : MenuSeed n K ≃ᵐ (Fin n → Bool) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => Bool)
    (finCongr (by simp [freshInstance]))

theorem menuSeedFinEquiv_measurePreserving (n K : ℕ) :
    MeasurePreserving (menuSeedFinEquiv n K) (menuSeedLaw n K)
      (Measure.pi (fun _ : Fin n => PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw)) :=
  measurePreserving_piCongrLeft (fun _ : Fin n =>
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw)
      (finCongr (by simp [freshInstance]))

/-- Split the original per-physical-stage private seed, rather than
replacing it by unrelated seed laws in the compiler analysis. -/
def menuSeedSplit (n K : ℕ) : MenuSeed (n + 1) K ≃ᵐ Bool × MenuSeed n K :=
  ((menuSeedFinEquiv (n + 1) K).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Bool) 0)).trans
      ((MeasurableEquiv.refl Bool).prodCongr (menuSeedFinEquiv n K).symm)

theorem menuSeedSplit_fst (n K : ℕ) (seed : MenuSeed (n + 1) K) :
    (menuSeedSplit n K seed).1 = seed (menuStageAt (n + 1) K 0) := rfl

theorem menuSeedSplit_snd (n K : ℕ) (seed : MenuSeed (n + 1) K) (i : Fin n) :
    (menuSeedSplit n K seed).2 (menuStageAt n K i) = seed (menuStageAt (n + 1) K i.succ) := rfl

theorem menuSeedSplit_measurePreserving (n K : ℕ) :
    MeasurePreserving (menuSeedSplit n K) (menuSeedLaw (n + 1) K)
      (PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw.prod (menuSeedLaw n K)) := by
  have hfirst := menuSeedFinEquiv_measurePreserving (n + 1) K
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) =>
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw) 0
  have htail := (MeasurePreserving.id PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw).prod
    ((menuSeedFinEquiv_measurePreserving n K).symm (menuSeedFinEquiv n K))
  exact htail.comp (hsplit.comp hfirst)

theorem menuSeedSplit_law (n K : ℕ) :
    (menuSeedLaw (n + 1) K).map (menuSeedSplit n K) =
      PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw.prod (menuSeedLaw n K) :=
  (menuSeedSplit_measurePreserving n K).map_eq

theorem menuSeedUnsplit_law (n K : ℕ) :
    (PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw.prod (menuSeedLaw n K)).map
      (menuSeedSplit n K).symm = menuSeedLaw (n + 1) K :=
  ((menuSeedSplit_measurePreserving n K).symm (menuSeedSplit n K)).map_eq

end PDMenu
