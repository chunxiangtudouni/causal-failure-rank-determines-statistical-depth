module

public import PaperProofs.Star.Claims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters
open scoped ENNReal

theorem testingAction_quota_coupling (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) :
    P.testingActionReal order kind r (some quota) history stage =
      P.testingActionReal order kind r none history stage ∨
      P.testingActionReal order kind r (some quota) history stage = .abandon := by
  classical
  cases ht : P.chosenTargetReal order kind r history stage with
  | none => exact Or.inl (by simp only [testingActionReal, ht])
  | some target =>
    by_cases hv : ∀ symbol ∈ historyObservations history stage,
        symbol < P.channel.experiment.alphabetSize
    · simp only [testingActionReal, ht, dite_eq_left hv]
      split
      · exact Or.inl rfl
      · by_cases hq : (historyObservations history stage).length < quota
        · exact Or.inl (by simp only [ite_eq_left hq])
        · exact Or.inr (by simp only [ite_eq_right hq])
    · exact Or.inl (by simp only [testingActionReal, ht, dite_eq_right hv])

theorem candidateWithTesting_coupling (P : Parameters) (order : Order) (kind : PortKind)
    (left right : List (VisibleEvent (starInstance P.tools order)) →
      (starInstance P.tools order).Stage → Action (starInstance P.tools order))
    (h : ∀ history stage, left history stage = right history stage ∨ left history stage = .abandon)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    P.candidateWithTesting order kind left history = P.candidateWithTesting order kind right history ∨
      P.candidateWithTesting order kind left history = .abandon := by
  by_cases hh : historyHalted history = true
  · exact Or.inl (by simp only [candidateWithTesting, hh, ↓reduceIte])
  · by_cases hs : historyCursor history < (starInstance P.tools order).stageCount
    · cases hw : historyWritten history ⟨historyCursor history, hs⟩ with
      | none =>
        rcases h history ⟨historyCursor history, hs⟩ with heq | ha
        · exact Or.inl (by simpa only [candidateWithTesting, ite_eq_right hh, dite_eq_left hs, hw] using heq)
        · exact Or.inr (by simpa only [candidateWithTesting, ite_eq_right hh, dite_eq_left hs, hw] using ha)
      | some bit => exact Or.inl (by simp only [candidateWithTesting, ite_eq_right hh, dite_eq_left hs, hw])
    · exact Or.inl (by simp only [candidateWithTesting, ite_eq_right hh, dite_eq_right hs])

theorem starRule_quota_coupling {Seed : Type*} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (seed : Seed) (history : List (VisibleEvent (starInstance P.tools order))) :
    P.starReferenceRule order kind r (some quota) seed history =
      P.starReferenceRule order kind r none seed history ∨
      P.starReferenceRule order kind r (some quota) seed history = .abandon :=
  candidateWithTesting_coupling P order kind _ _ (testingAction_quota_coupling P order kind r quota) history

theorem run_same_or_first_abandon {I : Instance} {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (bounded ideal : PolicyRule I Seed)
    (hcoupled : ∀ seed history, bounded seed history = ideal seed history ∨ bounded seed history = .abandon)
    (sample : Seed × input.World) :
    (∀ n, run input C mode accounting bounded sample n = run input C mode accounting ideal sample n) ∨
      ∃ cut, (∀ n, n ≤ cut → run input C mode accounting bounded sample n = run input C mode accounting ideal sample n) ∧
        (run input C mode accounting ideal sample cut).halted = false ∧
        run input C mode accounting bounded sample (cut + 1) = stopState (run input C mode accounting ideal sample cut) true ∧
        ∀ n, run input C mode accounting bounded sample (cut + 1 + n) =
          stopState (run input C mode accounting ideal sample cut) true := by
  classical
  by_cases hex : ∃ n, run input C mode accounting bounded sample n ≠ run input C mode accounting ideal sample n
  · let first := Nat.find hex
    have hdiff : run input C mode accounting bounded sample first ≠ run input C mode accounting ideal sample first := Nat.find_spec hex
    have hfirst : 0 < first := by
      by_contra hz
      have heq : first = 0 := by omega
      exact hdiff (by rw [heq]; rfl)
    let cut := first - 1
    have hsucc : first = cut + 1 := by omega
    have hprefix : ∀ n, n ≤ cut → run input C mode accounting bounded sample n = run input C mode accounting ideal sample n := by
      intro n hn
      exact not_ne_iff.mp (Nat.find_min hex (by omega : n < first))
    have heq := hprefix cut le_rfl
    have hactive : (run input C mode accounting ideal sample cut).halted = false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      have hhb : (run input C mode accounting bounded sample cut).halted = true := by rw [heq]; exact hh
      apply hdiff
      rw [hsucc, run_succ_of_halted input C mode accounting bounded sample cut hhb,
        run_succ_of_halted input C mode accounting ideal sample cut hh, heq]
    have habandon : bounded sample.1 (run input C mode accounting ideal sample cut).history = .abandon := by
      rcases hcoupled sample.1 (run input C mode accounting ideal sample cut).history with hs | ha
      · exfalso
        apply hdiff
        rw [hsucc]
        simp only [run]
        rw [heq, hs]
      · exact ha
    have hbactive : (run input C mode accounting bounded sample cut).halted = false := by rw [heq]; exact hactive
    have hstopped : run input C mode accounting bounded sample (cut + 1) =
        stopState (run input C mode accounting ideal sample cut) true := by
      apply run_succ_of_step input C mode accounting bounded sample cut _ hbactive
      rw [heq, habandon]
      exact Step.abandon (run input C mode accounting ideal sample cut) hactive
    refine Or.inr ⟨cut, hprefix, hactive, hstopped, ?_⟩
    intro n
    rw [run_after_halt input C mode accounting bounded sample (cut + 1) (by rw [hstopped]; rfl) n, hstopped]
  · exact Or.inl (fun n => not_ne_iff.mp (not_exists.mp hex n))

theorem sameTapeStarTruncation (P : Parameters) : P.SameTapeStarTruncation := by
  intro order kind C _hC accounting r quota _hr _hq sample
  have h := run_same_or_first_abandon (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r (some quota)) (P.starReferenceRule order kind r none)
    (starRule_quota_coupling P order kind r quota) sample
  refine ⟨h, ?_⟩
  apply iSup_le
  intro n
  rcases h with hall | ⟨cut, hprefix, _, _, hafter⟩
  · rw [hall n]
    exact prefixBill_le_runActualBill (P.input order) C .uncapped accounting _ sample n
  · by_cases hn : n ≤ cut
    · rw [hprefix n hn]
      exact prefixBill_le_runActualBill (P.input order) C .uncapped accounting _ sample n
    · have heq : n = cut + 1 + (n - (cut + 1)) := by omega
      rw [heq, hafter, stop_actualBill]
      exact prefixBill_le_runActualBill (P.input order) C .uncapped accounting _ sample cut

end RootStarOverflow
