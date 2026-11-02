module

public import PaperProofs.Retained.PRet_FiniteSourceHalt_025
public import PaperProofs.Retained.PRet_EventualPairs_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetHaltedPairs036

open Common Common.Native PRetExactTerminal001 PRetFiniteSourceHalt025 PRetEventualPairs004

variable {I : Instance}

theorem run_pairs_prefix_add {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (n extra : ℕ) :
    ((run input C mode accounting source sample n).ledger.executions.map executionPair).IsPrefix
      ((run input C mode accounting source sample (n + extra)).ledger.executions.map executionPair) := by
  have hh := run_history_prefix_add input C mode accounting source hlegal sample n extra
  have hp := List.IsPrefix.filterMap eventExecution hh
  change (historyExecutions (run input C mode accounting source sample n).history).IsPrefix
    (historyExecutions (run input C mode accounting source sample (n + extra)).history) at hp
  obtain ⟨_, _, hfirst⟩ := run_has_prefix input C mode accounting source hlegal sample n
  obtain ⟨_, _, hlater⟩ := run_has_prefix input C mode accounting source hlegal sample (n + extra)
  rw [prefix_historyExecutions input C mode accounting source sample.1 _ _ hfirst,
    prefix_historyExecutions input C mode accounting source sample.1 _ _ hlater] at hp
  have hp' := List.IsPrefix.map (fun pair : MismatchHandle I × I.Tool => (pair.1.stage, pair.2)) hp
  change (List.map (fun e : Execution I => (e.handle.stage, e.tool))
    (run input C mode accounting source sample n).ledger.executions).IsPrefix
      (List.map (fun e : Execution I => (e.handle.stage, e.tool))
        (run input C mode accounting source sample (n + extra)).ledger.executions)
  simpa only [List.map_map, Function.comp_def] using hp'

theorem run_pairs_prefix_of_halted {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (last n : ℕ)
    (hhalt : (run input C mode accounting source sample last).halted = true) :
    ((run input C mode accounting source sample n).ledger.executions.map executionPair).IsPrefix
      ((run input C mode accounting source sample last).ledger.executions.map executionPair) := by
  by_cases hn : n ≤ last
  · have hp := run_pairs_prefix_add input C mode accounting source hlegal sample n (last - n)
    rw [Nat.add_sub_of_le hn] at hp
    exact hp
  · have hlast : last ≤ n := by omega
    have heq := run_after_halt input C mode accounting source sample last hhalt (n - last)
    rw [Nat.add_sub_of_le hlast] at heq
    rw [heq]

theorem eventualPairs_of_halted {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (last : ℕ)
    (hhalt : (run input C mode accounting source sample last).halted = true) :
    eventualPairs input C mode accounting source sample =
      ((run input C mode accounting source sample last).ledger.executions.map executionPair).toFinset := by
  classical
  ext pair
  rw [mem_eventualPairs, List.mem_toFinset]
  constructor
  · rintro ⟨n, e, he, hs, ht⟩
    have hm : pair ∈ (run input C mode accounting source sample n).ledger.executions.map executionPair :=
      List.mem_map.mpr ⟨e, he, Prod.ext hs ht⟩
    exact (run_pairs_prefix_of_halted input C mode accounting source hlegal sample last n hhalt).subset hm
  · intro hm
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
    exact ⟨last, e, he, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end PaperProofs.Retained.PRetHaltedPairs036
