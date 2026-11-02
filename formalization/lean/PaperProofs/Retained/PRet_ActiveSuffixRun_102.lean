module

public import PaperProofs.Common.NativeSuffixRunLift

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetActiveSuffixRun102

open Common Common.Native

variable {I : Instance}

/-- The existing genuine Step transport only needs action equality while
its real child is active. A halted child is already paired with a halted
parent and neither interpreter consults its raw rule again. -/
theorem suffixRun_view_of_active_rule_lift {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first)) (hchildEarly : childC.reporting = .early)
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (hstart : ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample start)
      (initial ((input.freshSuffix first).truthAt (referenceSuffixWorld input first sample.2))))
    (hlift : ∀ k : ℕ,
      ReferenceSuffixView I first before
        (run input C .uncapped accounting rule sample (start + k))
        (run (input.freshSuffix first) childC .uncapped childAccounting childRule
          (sample.1, referenceSuffixWorld input first sample.2) k) →
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k).halted = false →
      rule sample.1 (run input C .uncapped accounting rule sample (start + k)).history =
        referenceSuffixActionLift I first (historyActions before).length
          (childRule sample.1 (run (input.freshSuffix first) childC .uncapped childAccounting
            childRule (sample.1, referenceSuffixWorld input first sample.2) k).history)) :
    ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k) := by
  let childSample : Seed × (input.freshSuffix first).World :=
    (sample.1, referenceSuffixWorld input first sample.2)
  intro k
  induction k with
  | zero => simpa only [Nat.add_zero, run] using hstart
  | succ k ih =>
    change ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + (k + 1)))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample (k + 1))
    by_cases hh : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = true
    · have hparentHalt : (run input C .uncapped accounting rule sample (start + k)).halted = true := ih.halted.trans hh
      rw [Nat.add_succ, run_succ_of_halted input C .uncapped accounting rule sample (start + k) hparentHalt,
        run_succ_of_halted (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k hh]
      exact ih
    · have hchildActive : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = false :=
        Bool.eq_false_iff.mpr hh
      have hparentActive : (run input C .uncapped accounting rule sample (start + k)).halted = false := ih.halted.trans hchildActive
      obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
      obtain ⟨l, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal childSample k
      have ha := hlift k ih hchildActive
      obtain ⟨nextParent, hps⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) m _ hp hparentActive
      obtain ⟨nextChild, hcs⟩ := hchildLegal sample.1 ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) l _ hc hchildActive
      have hpsLift := hps
      rw [ha] at hpsLift
      have hcounts := referenceSuffix_reviews_of_prefixes input first C accounting rule childC childAccounting childRule sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) hp hc before ih hbefore
      have htruths : ∀ stage, (run input C .uncapped accounting rule sample (start + k)).ledger.truth (I.freshStageLift first stage) =
          (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).ledger.truth stage := by
        intro stage
        calc
          _ = input.truthAt sample.2 (I.freshStageLift first stage) := congrFun (prefix_truth input C .uncapped accounting rule sample.1 _ _ hp) _
          _ = (input.freshSuffix first).truthAt childSample.2 stage := rfl
          _ = _ := (congrFun (prefix_truth (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1 _ _ hc) stage).symm
      have hnext := referenceSuffix_step_view input first C childC hearly hchildEarly accounting childAccounting
        (worldTapes input sample.2) (worldTapes (input.freshSuffix first) childSample.2) before ih hcounts htruths
        (fun stage index => (referenceSuffixWorld_letter input first sample.2 stage index).symm) hpsLift hcs
      rw [Nat.add_succ, run_succ_of_step input C .uncapped accounting rule sample (start + k) nextParent hparentActive hps,
        run_succ_of_step (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k nextChild hchildActive hcs]
      exact hnext


end PaperProofs.Retained.PRetActiveSuffixRun102
