module

public import PaperProofs.Paid.PDROC_MenuExpected_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.MenuExpected

theorem badRecord_computed_means (P : Parameters) (fee penalty : ℚ) (table : MenuTable)
    (previous : MenuRow) (n k : ℕ)
    (hprevious : ∀ j, j ≤ k → RecordMeans P n
      (fun sample => PDMenu.menuPathSummary P table n j sample.1 sample.2) (previous.getD j abandonEntry))
    (hstats : ∀ j, PDMenu.MenuStatsBound (previous.getD j abandonEntry) n j) :
    RecordMeans P n (badRecord P table n k (P.menuBadBranch fee penalty previous k).1)
      (P.menuBadBranch fee penalty previous k).2 := by
  cases k with
  | zero => exact recordMeans_abandon P n
  | succ k =>
      dsimp only [Parameters.menuBadBranch]
      split_ifs
      · have heq : badRecord P table n (k+1) .repair =
          fun sample : Tail P n =>
            let child := PDMenu.menuPathSummary P table n k sample.1 sample.2
            {child with physicalRepairs := child.physicalRepairs+1} := by
          funext sample
          simp only [badRecord, ite_eq_right (by omega : k+1 ≠ 0), show k+1-1=k by omega]
        rw [heq]
        exact recordMeans_increment P n _ (previous.getD k abandonEntry)
          (PDMenu.measurable_menuPathSummary P table n k)
          (hprevious k (by omega)) (hstats k).2.1
      · exact recordMeans_abandon P n

theorem summary_testing_means (P : Parameters) (fee penalty : ℚ) (table : MenuTable)
    (previous : MenuRow) (n k level : ℕ)
    (hcell : menuEntryAt table (n+1) k = P.menuTestingEntry fee penalty previous k level)
    (hgood : RecordMeans P n (fun sample => PDMenu.menuPathSummary P table n k sample.1 sample.2)
      (previous.getD k abandonEntry))
    (hbad : RecordMeans P n (badRecord P table n k (P.menuBadBranch fee penalty previous k).1)
      (P.menuBadBranch fee penalty previous k).2)
    (hgstats : PDMenu.MenuStatsBound (previous.getD k abandonEntry) n k)
    (hbstats : PDMenu.MenuStatsBound (P.menuBadBranch fee penalty previous k).2 (n+1) k) :
    RecordMeans P (n+1) (fun sample => PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2)
      (menuEntryAt table (n+1) k) := by
  let good := previous.getD k abandonEntry
  let bad := (P.menuBadBranch fee penalty previous k).2
  let p := P.binarySymmetric.endpointError level
  have hp : 0 ≤ p := (P.binarySymmetric.endpointError_pos level).le
  have hp1 : p ≤ 1 := (P.binarySymmetric.endpointError_le_half level).trans (by norm_num)
  have ha : (menuEntryAt table (n+1) k).action = .test level (P.menuBadBranch fee penalty previous k).1 :=
    congrArg MenuEntry.action hcell
  have ho := summary_test_observation_integral P table n k level _ ha
  have hr := summary_test_repairs_integral P table n k level _ ha
  have hf := summary_test_failure_integral P table n k level _ ha
  rw [hgood.1,hbad.1] at ho
  rw [hgood.2.1,hbad.2.1] at hr
  rw [hgood.2.2,hbad.2.2] at hf
  refine ⟨?_,?_,?_⟩
  · rw [hcell]
    change _ = ENNReal.ofReal ((P.binarySymmetric.endpointCharge level+(1-p)*good.observation+p*bad.observation:ℚ):ℝ)
    exact ho.trans (ofReal_charge_weighted_sum _ p good.observation bad.observation
      (P.binarySymmetric.endpointCharge_nonneg level) hp hp1 hgstats.1 hbstats.1).symm
  · rw [hcell]
    change _ = ENNReal.ofReal (((1-p)*good.repairs+p*bad.repairs:ℚ):ℝ)
    exact hr.trans (ofReal_weighted_sum p good.repairs bad.repairs hp hp1 hgstats.2.1 hbstats.2.1).symm
  · rw [hcell]
    change _ = ENNReal.ofReal (((1-p)*good.failure+p*bad.failure:ℚ):ℝ)
    exact hf.trans (ofReal_weighted_sum p good.failure bad.failure hp hp1 hgstats.2.2.2.1 hbstats.2.2.2.1).symm

theorem summary_abandon_means (P : Parameters) (table : MenuTable) (n k : ℕ)
    (hcell : menuEntryAt table (n+1) k = abandonEntry) :
    RecordMeans P (n+1) (fun sample => PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2)
      (menuEntryAt table (n+1) k) := by
  have heq : (fun sample : Tail P (n+1) => PDMenu.menuPathSummary P table (n+1) k sample.1 sample.2) =
      fun _ => PDMenu.menuPathAbandon := by
    funext sample
    exact PDMenu.menuPathSummary_abandon P table n k sample.1 sample.2 (congrArg MenuEntry.action hcell)
  rw [heq,hcell]
  exact recordMeans_abandon P (n+1)

/-- A finite-product induction for the literal computed table. Child means
are induction conclusions, never assumptions of the final theorem. -/
theorem computed_record_means (P : Parameters) (fee penalty : ℚ) (N K : ℕ) :
    ∀ n, n ≤ N → ∀ k, k ≤ K →
      RecordMeans P n
        (fun sample => PDMenu.menuPathSummary P (P.solveMenuTable fee penalty K N) n k sample.1 sample.2)
        (menuEntryAt (P.solveMenuTable fee penalty K N) n k) := by
  let table := P.solveMenuTable fee penalty K N
  intro n
  induction n with
  | zero =>
      intro _hn k hk
      rw [computed_cell_zero P fee penalty N K k hk]
      exact recordMeans_finish P 0
  | succ n ih =>
      intro hn k hk
      let previous := table.getD n #[]
      have hcell : menuEntryAt table (n+1) k = P.nextMenuEntry fee penalty previous k :=
        computed_cell_succ P fee penalty N K n k hn hk
      have hprevious : ∀ j, j ≤ k → RecordMeans P n
          (fun sample => PDMenu.menuPathSummary P table n j sample.1 sample.2) (previous.getD j abandonEntry) := by
        intro j hj
        exact ih (by omega) j (hj.trans hk)
      have hstats : ∀ j, PDMenu.MenuStatsBound (previous.getD j abandonEntry) n j := by
        intro j
        exact PDMenu.solveMenuTable_stats P fee penalty N K n (by omega) j
      have hbad := badRecord_computed_means P fee penalty table previous n k hprevious hstats
      have hbstats := PDMenu.menuBadBranch_stats P fee penalty previous n k hstats
      unfold Parameters.nextMenuEntry at hcell
      dsimp only at hcell
      split_ifs at hcell
      · exact summary_abandon_means P table n k hcell
      · exact summary_abandon_means P table n k hcell
      · exact summary_testing_means P fee penalty table previous n k _ hcell
          (hprevious k le_rfl) hbad (hstats k) hbstats

end PDROC.MenuExpected

namespace PDROC

theorem expectedMenuPathRecords (P : Parameters) : PDMenu.ExpectedMenuPathRecords P := by
  intro fee penalty N K n k hn hk
  exact (MenuExpected.recordMeans_summary_iff P (P.solveMenuTable fee penalty K N) n k).mp
    (MenuExpected.computed_record_means P fee penalty N K n hn k hk)

end PDROC
