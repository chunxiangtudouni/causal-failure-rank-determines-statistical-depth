module

public import PaperProofs.Paid.PDMenu_PaidErasedSuffixLower_046
public import PaperProofs.Paid.PDMenu_CurrentReplayPaidCharge_026
public import PaperProofs.Paid.PDMenu_CurrentReplayDirac_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

/-- An actual execution is backed by a real commitment, so its tool is
absent from the genuine startup's remaining pool, including failed paths. -/
theorem executedTool_not_available (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World) (clock : ℕ)
    (e : Execution I) (he : e ∈ (run input C mode accounting rule sample clock).ledger.executions) :
    e.tool ∉ (publicStartup (run input C mode accounting rule sample clock)).availableTools := by
  intro havailable
  obtain ⟨a, ha, _hhandle, htool, _htime⟩ :=
    (run_ledgerWellFormed input C mode accounting rule hlegal sample clock).backed e he
  have hused : e.tool ∈ committedTools (run input C mode accounting rule sample clock) :=
    (mem_committedTools _ _).mpr ⟨a, ha, htool⟩
  exact (Finset.mem_sdiff.mp havailable).2 hused

variable [MeasurableSpace Seed]

/-- Sharp k-tool infimum comparison for the actual replay after a used head
tool. Only public startup data enter the target rule; the seed is arbitrary. -/
theorem freshPaidPenalty_le_paidReplay_erased_dirac (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (accounting : NormalAccounting (freshInstance (n + 1) (k + 1)))
    (rule : PolicyRule (freshInstance (n + 1) (k + 1)) Seed) (hm : MeasurableRule rule)
    (startup : Startup (freshInstance (n + 1) (k + 1))) (tool : Fin (k + 1))
    (hunavailable : tool ∉ startup.availableTools) (seed : Seed) (penalty : ℝ≥0∞) :
    let input := P.freshInput (n + 1) (k + 1) fee hfee
    let targetRule := paidGuardedRule (I := (freshInstance (n + 1) (k + 1)).freshSuffix 1)
      startup.availableTools (replayedSuffixCandidate 1 accounting rule startup)
    P.freshPaidPenalty fee hfee n k penalty ≤
      ∫⁻ fresh, runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract _)
        (zeroNormalAccounting _) targetRule penalty (seed, fresh) ∂(input.freshSuffix 1).worldLaw := by
  intro input targetRule
  let replay := paidReplayedSuffixAvailablePolicy input 1 accounting rule hm startup
  have havailable : startup.availableTools ⊆ Finset.univ.erase tool := by
    intro chosen hchosen
    exact Finset.mem_erase.mpr ⟨fun he => hunavailable (he ▸ hchosen), Finset.mem_univ _⟩
  let erased : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract _) (zeroNormalAccounting _)
      (Finset.univ.erase tool) Seed :=
    ⟨replay.val, UsesOnly.mono _ _ _ _ replay.property havailable⟩
  have hbound := freshPaidPenalty_le_erased_suffix_policy P fee hfee n k tool erased (Measure.dirac seed) penalty
  rw [paidPenaltyObjective_eq_lintegral _ _ _ _ erased.val.measurable_rule] at hbound
  rw [StatisticalInput.seededWorldLaw, Measure.dirac_prod,
    lintegral_map (measurable_runPaidPenaltyCharge _ _ _ _ erased.val.measurable_rule penalty)
      measurable_prodMk_left] at hbound
  exact hbound

end PDMenu


