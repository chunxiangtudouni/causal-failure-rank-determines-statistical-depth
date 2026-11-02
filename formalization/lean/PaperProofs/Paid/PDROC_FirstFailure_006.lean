module

public import PaperProofs.Paid.PDROC_FirstFailure_004
public import PaperProofs.Paid.PDROC_FailureCharacterization_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Exact shared-pool feasibility: outside past missed repairs and exhausted
unallocated current errors, an active real prefix has a successful legal suffix. -/
theorem prefix_not_permanentlyFailed_of_noPast_noExhausted
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (world : input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed (input.truthAt world) (worldTapes input world) n s)
    (ha : s.halted = false) (hpast : ∀ stage, ¬ PastUnrepairedError s stage)
    (hexhausted : ∀ stage, ¬ ExhaustedUnrepairedError s stage)
    (hpool : ∀ stage : I.Stage, ∀ tool : I.Tool, tool ∈ I.eligible stage) :
    ¬ PermanentlyFailed input C accounting world s := by
  classical
  intro hfailed
  have hcurrent : ∀ stage : I.Stage, stage.val = s.cursor → s.ledger.written stage ≠ none →
      s.ledger.written stage = some (s.ledger.truth stage) ∨
        ∃ execution ∈ s.ledger.executions, execution.handle.stage = stage := by
    intro stage hstage hw
    by_cases hcorrect : s.ledger.written stage = some (s.ledger.truth stage)
    · exact Or.inl hcorrect
    by_cases hcorrected : ∃ execution ∈ s.ledger.executions, execution.handle.stage = stage
    · exact Or.inr hcorrected
    have hwrong : s.ledger.written stage = some (!s.ledger.truth stage) := by
      cases hb : s.ledger.written stage with
      | none => exact (hw hb).elim
      | some bit =>
        cases bit <;> cases hx : s.ledger.truth stage <;> simp_all
    have hnone : ∀ execution ∈ s.ledger.executions, execution.handle.stage ≠ stage := by
      intro execution he hstage
      exact hcorrected ⟨execution, he, hstage⟩
    obtain ⟨time, ht⟩ := prefix_early_written_reported input C hearly mode accounting source seed
      (input.truthAt world) (worldTapes input world) hp stage hw
    obtain ⟨next, hpath, hext⟩ := currentRepair_exists input C accounting (worldTapes input world) s
      (prefix_invariant input C mode accounting source seed _ _ hp) ha stage hstage.symm
      hwrong ⟨time, ht⟩ hnone (hexhausted stage) (hpool stage)
    exact False.elim (prefix_not_permanentlyFailed_of_currentRepair input C mode accounting source seed world stage
      hp hstage hpast hpath hext hfailed)
  exact prefix_not_permanentlyFailed_of_noPast_current input C mode accounting source seed world hp ha hpast hcurrent hfailed

theorem missedOrExhaustedDetector_active_prefix_iff
    (input : StatisticalInput I) (C : Contract I) (hpay : C.IsCurrentPayment)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (world : input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed (input.truthAt world) (worldTapes input world) n s)
    (ha : s.halted = false)
    (hpool : ∀ stage : I.Stage, ∀ tool : I.Tool, tool ∈ I.eligible stage) :
    missedOrExhaustedDetector s.history = true ↔ PermanentlyFailed input C accounting world s := by
  refine ⟨missedOrExhaustedDetector_sound input C hpay mode accounting source seed _ _ hp world, ?_⟩
  intro hfailed
  by_contra hnot
  have hd : missedOrExhaustedDetector s.history = false := Bool.eq_false_iff.mpr hnot
  have hparts : pastUnrepairedDetector s.history = false ∧ exhaustedUnrepairedDetector s.history = false := by
    simpa only [missedOrExhaustedDetector, Bool.or_eq_false_eq_eq_false_and_eq_false] using hd
  have hpast : ∀ stage, ¬ PastUnrepairedError s stage := by
    intro stage hstage
    have hhit := (pastUnrepairedDetector_prefix_iff input C hpay.1.1 mode accounting source seed _ _ hp).mpr ⟨stage, hstage⟩
    rw [hparts.1] at hhit
    contradiction
  have hexhausted : ∀ stage, ¬ ExhaustedUnrepairedError s stage := by
    intro stage hstage
    have hhit := (exhaustedUnrepairedDetector_prefix_iff input C hpay.1.1 mode accounting source seed _ _ hp).mpr ⟨stage, hstage⟩
    rw [hparts.2] at hhit
    contradiction
  exact prefix_not_permanentlyFailed_of_noPast_noExhausted input C hpay.1.1 mode accounting source seed world hp ha hpast hexhausted hpool hfailed

/-- A concrete visible first-permanent-failure policy for the ORIGINAL
current-payment shared pool. It retains the source seed and does not sample
any future truth; all fees are charged by the original real Native run. -/
def firstFailurePolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (source : Policy (P.input fee hfee) C.val mode accounting Seed) :
    Policy (P.input fee hfee) C.val .uncapped accounting Seed :=
  detectedStopPolicy (P.input fee hfee) C.val .uncapped accounting (activeDetector missedOrExhaustedDetector)
    (uncappedSourcePolicy (P.input fee hfee) C.val mode accounting source)

theorem firstFailurePolicy_domination (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (source : Policy (P.input fee hfee) C.val mode accounting Seed) :
    FirstFailureDomination (P.input fee hfee) C.val mode accounting source
      (firstFailurePolicy P fee hfee C mode accounting source) := by
  apply firstFailureDomination_of_active_detector_any_mode
  intro sample n ha
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val mode accounting source.rule source.legal sample n
  apply missedOrExhaustedDetector_active_prefix_iff (P.input fee hfee) C.val C.property mode accounting source.rule sample.1 sample.2 hp ha
  intro stage tool
  rw [P.eligible_eq_univ stage]
  exact Finset.mem_univ tool



/-- Original first-failure existence, for either original mode, every seed
universe and every legal full-history policy; no finite-fee or MAP input. -/
theorem firstFailureDomination_exists (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (source : Policy (P.input fee hfee) C.val mode accounting Seed) :
    ∃ stopped : Policy (P.input fee hfee) C.val .uncapped accounting Seed,
      FirstFailureDomination (P.input fee hfee) C.val mode accounting source stopped :=
  ⟨firstFailurePolicy P fee hfee C mode accounting source,
    firstFailurePolicy_domination P fee hfee C mode accounting source⟩

end PDROC
