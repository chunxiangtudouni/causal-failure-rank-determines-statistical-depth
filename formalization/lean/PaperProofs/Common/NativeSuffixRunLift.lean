module

public import PaperProofs.Common.ReferenceSuffixRun

/-!
Arbitrary legal continuations obey the same already-proved native step
transport as the reference. The only local interface below is equality of
the two actual actions at a paired public view. No value, risk, finite-cost,
termination, or optimal-continuation assumption is supplied.
-/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance}

/-- An actual active prefix at the continuation cursor supplies its own
public initial view. The returned-action clock is recovered from the real
history; it is not supplied as an alignment assumption. -/
theorem suffixInitialView_of_prefix {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {parent : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n parent)
    (hcursor : parent.cursor = first) (hactive : parent.halted = false)
    (childTruth : (I.freshSuffix first).Stage → Bool) :
    ReferenceSuffixView I first parent.history parent (initial childTruth) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [referenceSuffixHistoryJoin, initial, referenceSuffixHistoryLift, List.map_nil, List.append_nil]
  · simpa only [initial, Nat.add_zero] using hcursor
  · simpa only [initial, Nat.add_zero] using
      (prefix_historyActions_length input C .uncapped accounting rule seed truth tapes hp).symm
  · exact hactive

theorem suffixRun_view_of_rule_lift {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
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
      have ha := hlift k ih
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

end PaperProofs.Common.Native
