module

public import PaperProofs.Common.NativeHorizon
public import PaperProofs.Common.ReferenceCertification

/-!
Finite returned-action termination of the actual uncapped quota-bounded
controller is independent of normal-call accounting and success. The source's
H0 bound on a complete execution can therefore be transported to every
prefix of THIS controller, including abandoned/failed executions.
This does not manufacture an H0 bound for an arbitrary normal-I/O function,
impose H0 on comparison policies, or assert a wall-clock/nonreturn bound.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

def quotaActionBound (I : Instance) (quota : I.Stage → ℕ) : ℕ :=
  (∑ stage, quota stage) + I.toolCount + I.toolCount + I.stageCount + I.stageCount + 1

private theorem natCast_sum_enat {α : Type*} (items : Finset α) (f : α → ℕ) :
    ((∑ item ∈ items, f item : ℕ) : ℕ∞) = ∑ item ∈ items, (f item : ℕ∞) := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items hnot ih =>
    simp only [Finset.sum_insert hnot, ENat.natCast_add, ih]

theorem prefix_length_le_of_review_bounds {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (quota : I.Stage → ℕ) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (hq : ∀ stage, s.ledger.reviews stage ≤ (quota stage : ℕ∞)) :
    n ≤ quotaActionBound I quota := by
  have hwf := prefix_ledgerWellFormed input C mode accounting policy seed truth tapes hp
  have hcursor := (prefix_cursorInvariant input C mode accounting policy seed truth tapes hp).bound
  have hreviews : (∑ stage, s.ledger.reviews stage) ≤ ((∑ stage, quota stage : ℕ) : ℕ∞) := by
    rw [natCast_sum_enat]
    exact Finset.sum_le_sum (fun stage _ => hq stage)
  have hcommitments : s.ledger.commitments.length ≤ I.toolCount := by
    have hh := hwf.commitment_tools.length_le_card
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hh
  have hexecutions : s.ledger.executions.length ≤ I.toolCount :=
    (Ledger.execution_count_le hwf).trans (min_le_right _ _)
  have hwritten : (writtenPorts s.ledger).card ≤ I.stageCount := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun stage : I.Stage => s.ledger.written stage ≠ none) Finset.univ)
    simpa only [writtenPorts, Finset.card_univ, Instance.Stage, Instance.stageCount, Fintype.card_fin] using hh
  have hhalted : (if s.halted then (1 : ℕ∞) else 0) ≤ 1 := by cases s.halted <;> simp
  have ht := add_le_add
    (add_le_add
      (add_le_add
        (add_le_add (add_le_add hreviews (ENat.natCast_le_natCast.mpr hcommitments))
          (ENat.natCast_le_natCast.mpr hexecutions))
        (ENat.natCast_le_natCast.mpr hcursor))
      (ENat.natCast_le_natCast.mpr hwritten)) hhalted
  have hprogress : actionProgress s ≤ (quotaActionBound I quota : ℕ∞) := by
    simpa only [actionProgress, quotaActionBound, ENat.natCast_add, ENat.natCast_one] using ht
  rw [prefix_actionProgress input C mode accounting policy seed truth tapes hp] at hprogress
  exact ENat.natCast_le_natCast.mp hprogress

theorem run_halted_of_reviewQuotaCertificate {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (policy : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting policy)
    (quota : I.Stage → ℕ) (hq : ReviewQuotaCertificate input C accounting policy quota)
    (sample : Seed × input.World) :
    (run input C .uncapped accounting policy sample (quotaActionBound I quota + 1)).halted = true := by
  by_contra hh
  have ha := Bool.eq_false_iff.mpr hh
  have hp := run_prefix_of_active input C .uncapped accounting policy hlegal sample
    (quotaActionBound I quota + 1) ha
  have hn := prefix_length_le_of_review_bounds input C .uncapped accounting policy sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) quota hp
    (hq sample (quotaActionBound I quota + 1))
  omega

theorem step_normalCalls_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes s action next) :
    s.ledger.normalCalls ≤ next.ledger.normalCalls := by
  cases hs with
  | review => exact le_self_add
  | write stage bit =>
    have hf : (reportedWriteLedger C s stage bit).normalCalls = s.ledger.normalCalls := by
      simp only [reportedWriteLedger]
      split_ifs <;> rfl
    change s.ledger.normalCalls ≤ (reportedWriteLedger C s stage bit).normalCalls + _
    rw [hf]
    exact le_self_add
  | allocate => exact le_self_add
  | execute => exact le_self_add
  | advance => exact le_self_add
  | stop | abandon => exact le_rfl

theorem nextFromFrontier_normalCalls_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (frontier : Frontier input) :
    s.ledger.normalCalls ≤
      (nextFromFrontier input C mode accounting s action frontier).ledger.normalCalls := by
  classical
  unfold nextFromFrontier
  split_ifs with hhalt hex
  · exact le_rfl
  · exact step_normalCalls_mono input C mode accounting _ (Classical.choose_spec hex)
  · exact le_rfl

theorem run_normalCalls_mono {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) :
    Monotone (fun n => (run input C mode accounting policy sample n).ledger.normalCalls) := by
  apply monotone_nat_of_le_succ
  intro n
  exact nextFromFrontier_normalCalls_mono input C mode accounting _ _ _

/-- Original complete-execution normal-I/O assumption for a selected
controller. Every halt is included, not only successful final outputs. -/
def CompletedNormalCallBound {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (H0 : ℕ) : Prop :=
  ∀ sample n, (run input C mode accounting policy sample n).halted = true →
    (run input C mode accounting policy sample n).ledger.normalCalls ≤ (H0 : ℕ∞)

theorem normalCallCertificate_iff_completed_of_halts {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (H0 : ℕ)
    (hhalts : ∀ sample : Seed × input.World, ∃ n, (run input C mode accounting policy.rule sample n).halted = true) :
    NormalCallCertificate input C mode accounting policy H0 ↔
      CompletedNormalCallBound input C mode accounting policy.rule H0 := by
  constructor
  · intro hp sample n _hh
    exact hp sample n
  · intro hc sample n
    obtain ⟨finish, hh⟩ := hhalts sample
    have hm := run_normalCalls_mono input C mode accounting policy.rule sample
      (show n ≤ finish + n from Nat.le_add_left _ _)
    dsimp only at hm
    rw [run_after_halt input C mode accounting policy.rule sample finish hh n] at hm
    exact hm.trans (hc sample finish hh)

theorem referenceBounded_halted {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (exponent : ℕ) (sample : Seed × input.World) :
    (run input C .uncapped accounting (referenceRule input available budget (some (referenceQuota input exponent)))
      sample (quotaActionBound I (referenceQuota input exponent) + 1)).halted = true :=
  run_halted_of_reviewQuotaCertificate input C accounting _
    (referenceRule_uncapped_legal input C hearly accounting available budget (some (referenceQuota input exponent)))
    (referenceQuota input exponent)
    (referenceRule_reviewQuotaCertificate input C hearly accounting available budget (referenceQuota input exponent)) sample

/-- The actual fixed bounded reference needs only the source's normal-I/O
bound on complete executions to certify all prefixes under the SAME H0. -/
theorem referenceBounded_normalCalls_iff_completed
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (exponent H0 : ℕ) :
    NormalCallCertificate input C .uncapped accounting
      (referenceBoundedPolicy input C hearly accounting available budget exponent) H0 ↔
    CompletedNormalCallBound input C .uncapped accounting
      (referenceBoundedPolicy input C hearly accounting available budget exponent).rule H0 := by
  apply normalCallCertificate_iff_completed_of_halts
  intro sample
  exact ⟨_, referenceBounded_halted input C hearly accounting available budget exponent sample⟩

end PaperProofs.Common.Native
