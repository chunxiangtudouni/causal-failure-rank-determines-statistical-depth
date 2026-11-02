module

public import PaperProofs.Paid.RepresentationClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def markedCorrectionPairs (marks : List (HistoryMark I)) : List (I.Stage × I.Tool) :=
  marks.filterMap fun mark => match mark with
    | .correction stage tool => some (stage, tool)
    | _ => none

theorem markedCorrectionPairs_markedHistory (history : List (VisibleEvent I)) :
    markedCorrectionPairs (markedHistory history) = executedPairs history := by
  unfold markedCorrectionPairs markedHistory executedPairs historyExecutions
  rw [List.filterMap_filterMap, List.map_filterMap]
  congr 1
  funext event
  cases event with
  | report stage truth serial =>
    simp only
    cases hw : historyWrite history stage with
    | none => rfl
    | some pair => simp only; split_ifs <;> rfl
  | observation | wrote | committed | executed | advanced | stopped | abandoned => rfl

theorem paid_correctionBill_eq_count (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (L : Ledger P.sharedInstance) :
    L.correctionBill (P.input fee hfee).fees =
      (L.executions.length : ℝ≥0∞) * ENNReal.ofReal (fee : ℝ) := by
  unfold Ledger.correctionBill
  change (L.executions.map (fun _ => ENNReal.ofReal (fee : ℝ))).sum = _
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul]

theorem step_executionCount_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next) :
    s.ledger.executions.length ≤ next.ledger.executions.length := by
  cases hs with
  | write => simp only [record, reportedWriteLedger]; split_ifs <;> exact le_rfl
  | execute => simp only [record, executeLedger, List.length_append, List.length_singleton]; omega
  | review | allocate | advance | stop | abandon => exact le_rfl

theorem nextFromFrontier_executionCount_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (frontier : Frontier input) :
    s.ledger.executions.length ≤ (nextFromFrontier input C mode accounting s action frontier).ledger.executions.length := by
  classical
  unfold nextFromFrontier
  split_ifs with hh hstep
  · exact le_rfl
  · exact step_executionCount_mono input C mode accounting (frozenTapes input frontier) (Classical.choose_spec hstep)
  · exact le_rfl

theorem run_executionCount_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (sample : Seed × input.World) :
    Monotone (fun n => (run input C mode accounting rule sample n).ledger.executions.length) := by
  apply monotone_nat_of_le_succ
  intro n
  exact nextFromFrontier_executionCount_mono input C mode accounting _ _ _

theorem paid_runCorrectionBill_of_halted (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World) (n : ℕ)
    (hh : (run (P.input fee hfee) C.val mode accounting rule sample n).halted = true) :
    P.runActualCorrectionBill fee hfee C mode accounting rule sample =
      (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.correctionBill (P.input fee hfee).fees := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hkn : k ≤ n
    · rw [paid_correctionBill_eq_count, paid_correctionBill_eq_count]
      apply mul_le_mul' _ le_rfl
      exact_mod_cast run_executionCount_mono (P.input fee hfee) C.val mode accounting rule sample hkn
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hkn)
      rw [run_after_halt (P.input fee hfee) C.val mode accounting rule sample n hh extra]
  · exact le_iSup (fun k => (run (P.input fee hfee) C.val mode accounting rule sample k).ledger.correctionBill
      (P.input fee hfee).fees) n

/-- The marker decoder has no finite fee value on nonreturn; equality with
the actual bill below is proved only at a genuine completed history. -/
noncomputable def markedCompletedCorrectionBill (fee : ℚ)
    (history : Option (List (HistoryMark I))) : ℝ≥0∞ :=
  match history with
  | none => ⊤
  | some marks => (markedCorrectionPairs marks).length * ENNReal.ofReal (fee : ℝ)

theorem paid_runCorrectionBill_of_completedHistory (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (history : List (VisibleEvent P.sharedInstance))
    (hh : completedHistory (P.input fee hfee) C.val mode accounting rule sample = some history) :
    P.runActualCorrectionBill fee hfee C mode accounting rule sample =
      markedCompletedCorrectionBill fee (some (markedHistory history)) := by
  obtain ⟨n, hhalt, _hbefore, hhistory⟩ :=
    (completedHistory_some_iff (P.input fee hfee) C.val mode accounting rule sample history).mp hh
  rw [paid_runCorrectionBill_of_halted P fee hfee C mode accounting rule sample n hhalt,
    paid_correctionBill_eq_count]
  obtain ⟨k, _hkn, hp⟩ := run_has_prefix (P.input fee hfee) C.val mode accounting rule hl sample n
  have he := prefix_historyExecutions (P.input fee hfee) C.val mode accounting rule sample.1 _ _ hp
  simp only [markedCompletedCorrectionBill]
  rw [markedCorrectionPairs_markedHistory, executedPairs, ← hhistory, he]
  simp only [List.length_map]

end PDROC
