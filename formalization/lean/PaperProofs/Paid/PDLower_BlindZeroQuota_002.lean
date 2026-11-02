module

public import PaperProofs.Paid.PDLower_BlindZeroQuota_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

variable {I : Instance} {Seed : Type*}

theorem zero_quota_run_truth_congr (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (hquota : ∀ stage, C.reviewQuota stage = 0)
    (rule : PolicyRule I Seed) (legal : LegalRule input C .native accounting rule)
    (seed : Seed) (world world' : input.World)
    (htruth : input.truthAt world = input.truthAt world') (n : ℕ) :
    run input C .native accounting rule (seed, world) n =
      run input C .native accounting rule (seed, world') n := by
  induction n with
  | zero => change initial (input.truthAt world) = initial (input.truthAt world'); rw [htruth]
  | succ n ih =>
    by_cases hhalt : (run input C .native accounting rule (seed, world) n).halted = true
    · have hhalt' : (run input C .native accounting rule (seed, world') n).halted = true := by
        rw [← ih]
        exact hhalt
      rw [run_succ_of_halted input C .native accounting rule (seed, world) n hhalt,
        run_succ_of_halted input C .native accounting rule (seed, world') n hhalt']
      exact ih
    · have hactive : (run input C .native accounting rule (seed, world) n).halted = false :=
        Bool.eq_false_iff.mpr hhalt
      obtain ⟨clock, _hclock, path⟩ :=
        run_has_prefix input C .native accounting rule legal (seed, world) n
      obtain ⟨next, step⟩ := legal seed (input.truthAt world) (worldTapes input world)
        clock _ path hactive
      have hactive' : (run input C .native accounting rule (seed, world') n).halted = false := by
        rw [← ih]
        exact hactive
      have step' : Step input C .native accounting (worldTapes input world')
          (run input C .native accounting rule (seed, world') n)
          (rule seed (run input C .native accounting rule (seed, world') n).history) next := by
        rw [← ih]
        exact step_tapes_irrelevant_of_zero_quota input C accounting hquota
          (worldTapes input world) (worldTapes input world') step
      rw [run_succ_of_step input C .native accounting rule (seed, world) n next hactive step,
        run_succ_of_step input C .native accounting rule (seed, world') n next hactive' step']

theorem zero_quota_success_truth_congr (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (hquota : ∀ stage, C.reviewQuota stage = 0)
    (rule : PolicyRule I Seed) (legal : LegalRule input C .native accounting rule)
    (seed : Seed) (world world' : input.World)
    (htruth : input.truthAt world = input.truthAt world') :
    runSuccess input C .native accounting rule (seed, world) ↔
      runSuccess input C .native accounting rule (seed, world') := by
  unfold runSuccess
  simp_rw [zero_quota_run_truth_congr input C accounting hquota rule legal seed world world' htruth]

end PDLower
