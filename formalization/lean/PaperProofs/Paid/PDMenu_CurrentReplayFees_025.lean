module

public import PaperProofs.Paid.PDMenu_CurrentReplayRun_023
public import PaperProofs.Common.NativeCostBound
public import PaperProofs.Common.FreshSuffixComposition
public import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

theorem correctionBill_constant (fees : Fees I) (fee : ℚ)
    (hfee : ∀ stage tool, fees.correction stage tool = fee) (ledger : Ledger I) :
    ledger.correctionBill fees = (ledger.executions.length : ℝ≥0∞) * ENNReal.ofReal (fee : ℝ) := by
  simp only [Ledger.correctionBill, hfee, List.map_const', List.sum_replicate, nsmul_eq_mul]

/-- Each real child execution has a distinct source execution stage. An old
executed head is outside this image and contributes one additional payment. -/
theorem historySuffix_execution_count_le (input : StatisticalInput I) (first : ℕ)
    {source : State I} {target : State (I.freshSuffix first)}
    (view : HistorySuffixStateView input first source target)
    (hsource : LedgerWellFormed source.ledger) (htarget : LedgerWellFormed target.ledger) :
    target.ledger.executions.length ≤ source.ledger.executions.length ∧
    (∀ e ∈ source.ledger.executions, e.handle.stage.val < first →
      target.ledger.executions.length + 1 ≤ source.ledger.executions.length) := by
  classical
  let sourceStages := (source.ledger.executions.map (fun e => e.handle.stage)).toFinset
  let targetStages := (target.ledger.executions.map (fun e => I.freshStageLift first e.handle.stage)).toFinset
  have hnodup : (target.ledger.executions.map (fun e => I.freshStageLift first e.handle.stage)).Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      htarget.execution_stages.map (freshStageLift_injective I first)
  have hsCard : sourceStages.card = source.ledger.executions.length := by
    dsimp only [sourceStages]
    rw [List.toFinset_card_of_nodup hsource.execution_stages, List.length_map]
  have htCard : targetStages.card = target.ledger.executions.length := by
    dsimp only [targetStages]
    rw [List.toFinset_card_of_nodup hnodup, List.length_map]
  have hsub : targetStages ⊆ sourceStages := by
    intro stage hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    obtain ⟨a, ha, hstage, _htool⟩ := view.executions_reverse e he
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, hstage⟩)
  constructor
  · simpa only [hsCard, htCard] using Finset.card_le_card hsub
  · intro e he hold
    have hnot : e.handle.stage ∉ targetStages := by
      intro hm
      obtain ⟨a, _ha, hstage⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      have hh := congrArg Fin.val hstage
      change first + a.handle.stage.val = e.handle.stage.val at hh
      omega
    have hmem : e.handle.stage ∈ sourceStages := List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
    have hc := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hmem, hsub⟩)
    rwa [Finset.card_insert_of_notMem hnot, htCard, hsCard] at hc

theorem correctionBill_le_of_historySuffix (input : StatisticalInput I) (first : ℕ)
    {source : State I} {target : State (I.freshSuffix first)}
    (view : HistorySuffixStateView input first source target)
    (hsource : LedgerWellFormed source.ledger) (htarget : LedgerWellFormed target.ledger)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee) :
    target.ledger.correctionBill (input.freshSuffix first).fees ≤ source.ledger.correctionBill input.fees := by
  have hchild : ∀ stage tool, (input.freshSuffix first).fees.correction stage tool = fee := by
    intro stage tool
    exact (input.freshSuffix_correctionFee first stage tool).trans (hfee _ _)
  rw [correctionBill_constant _ fee hfee, correctionBill_constant _ fee hchild]
  exact mul_le_mul_left (by exact_mod_cast (historySuffix_execution_count_le input first view hsource htarget).1)
    (ENNReal.ofReal (fee : ℝ))

theorem paidHead_add_childCorrectionBill_le (input : StatisticalInput I) (first : ℕ)
    {source : State I} {target : State (I.freshSuffix first)}
    (view : HistorySuffixStateView input first source target)
    (hsource : LedgerWellFormed source.ledger) (htarget : LedgerWellFormed target.ledger)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee)
    (e : Execution I) (he : e ∈ source.ledger.executions) (hold : e.handle.stage.val < first) :
    ENNReal.ofReal (fee : ℝ) + target.ledger.correctionBill (input.freshSuffix first).fees ≤
      source.ledger.correctionBill input.fees := by
  have hchild : ∀ stage tool, (input.freshSuffix first).fees.correction stage tool = fee := by
    intro stage tool
    exact (input.freshSuffix_correctionFee first stage tool).trans (hfee _ _)
  rw [correctionBill_constant _ fee hfee, correctionBill_constant _ fee hchild]
  calc
    _ = ((target.ledger.executions.length + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (fee : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
    _ ≤ _ := mul_le_mul_left (by exact_mod_cast
      (historySuffix_execution_count_le input first view hsource htarget).2 e he hold) _

end PDMenu
