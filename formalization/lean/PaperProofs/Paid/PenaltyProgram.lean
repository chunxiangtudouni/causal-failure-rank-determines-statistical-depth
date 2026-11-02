module

public import PaperProofs.Paid.Claims
public import PaperProofs.Common.NativePenalty
public import PaperProofs.Common.NativeEmpty
public import PaperProofs.Common.NativeAccountingIrrelevance
public import PaperProofs.Common.NativeContractMetadata

/-!
The independent Appendix-D penalty value of paid-proofs.tex:413--474.
It is an infimum over the existing full visible-history I_pay policy class.
Unlike the main-chain observation-only relaxation, it pays every actual
correction, including corrections on failed and abandoned paths. Definitions
of successors and endpoint objectives come only AFTER that policy infimum.

Fresh shared-pool subproblems allow n=0 and k>=n. No MAP, finite-ET, H0 or
Markov assumption is inserted into a policy or comparison class. The
Bellman and finite-menu identities below remain explicit unproved Props.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace PaperProofs.Paid

open Common

variable {I : Instance}

/-- Actual observation AND actual correction bills, with one task-failure
penalty. No charge is removed on an eventual-failure or nonreturn path. -/
noncomputable def paidPenaltyObjective {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : Native.NormalAccounting I)
    (rule : PolicyRule I Seed) (ν : Measure Seed) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  Native.expectedBill input C .uncapped accounting rule ν +
    penalty * Native.risk input C .uncapped accounting rule ν

/-- Genuine cap-relaxed full-policy infimum. Type-0 seed encoding below
proves that the displayed universe does not restrict private randomness. -/
noncomputable def paidPenaltyValue (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Seed : Type), ⨅ (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ⨅ (ν : Measure Seed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : Native.Policy input C .uncapped accounting Seed,
        paidPenaltyObjective input C accounting policy.rule ν penalty

theorem paidPenaltyValue_le_policy (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (penalty : ℝ≥0∞) {Seed : Type}
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Native.Policy input C .uncapped accounting Seed) :
    paidPenaltyValue input C accounting penalty ≤ paidPenaltyObjective input C accounting policy.rule ν penalty :=
  iInf_le_of_le Seed (iInf_le_of_le ‹MeasurableSpace Seed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν› (iInf_le_of_le policy le_rfl))))

theorem paidPenaltyValue_le_policy_any_seed {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : Native.NormalAccounting I)
    (penalty : ℝ≥0∞) (policy : Native.Policy input C .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    paidPenaltyValue input C accounting penalty ≤ paidPenaltyObjective input C accounting policy.rule ν penalty := by
  have h := paidPenaltyValue_le_policy input C accounting penalty
    (Native.encodedSeedLaw input C .uncapped accounting policy ν)
    (Native.strategyPolicy input C .uncapped accounting)
  simpa only [paidPenaltyObjective, Native.expectedBill_encoded_eq, Native.risk_encoded_eq] using h

theorem paidPenaltyValue_le_penalty (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (penalty : ℝ≥0∞) :
    paidPenaltyValue input C accounting penalty ≤ penalty := by
  let ν : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have h := paidPenaltyValue_le_policy input C accounting penalty ν
    (Native.abandonPolicy input C .uncapped accounting Unit)
  have hb : Native.expectedBill input C .uncapped accounting
      (Native.abandonPolicy input C .uncapped accounting Unit).rule ν = 0 := by
    simp only [Native.expectedBill, Native.abandon_runActualBill, lintegral_zero]
  rw [paidPenaltyObjective, hb, zero_add] at h
  exact h.trans (by simpa only [mul_one] using (mul_le_mul_right
    (show Native.risk input C .uncapped accounting
      (Native.abandonPolicy input C .uncapped accounting Unit).rule ν ≤ 1 from prob_le_one) penalty))

theorem paidPenaltyObjective_reaccount_eq {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : Native.NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : Native.LegalRule input C .uncapped accounting rule)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    paidPenaltyObjective input C accounting' rule ν penalty =
      paidPenaltyObjective input C accounting rule ν penalty := by
  unfold paidPenaltyObjective
  rw [Native.risk_reaccount_eq input C accounting accounting' rule hlegal]
  congr 1
  exact lintegral_congr (Native.runActualBill_reaccount_eq input C accounting accounting' rule hlegal)

theorem paidPenaltyValue_reaccount_le (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : Native.NormalAccounting I) (penalty : ℝ≥0∞) :
    paidPenaltyValue input C accounting' penalty ≤ paidPenaltyValue input C accounting penalty := by
  conv_rhs => unfold paidPenaltyValue
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  have h := paidPenaltyValue_le_policy input C accounting' penalty ν
    (policy.reaccount input C accounting accounting')
  change paidPenaltyValue input C accounting' penalty ≤ paidPenaltyObjective input C accounting' policy.rule ν penalty at h
  rwa [paidPenaltyObjective_reaccount_eq input C accounting accounting' policy.rule policy.legal] at h

theorem paidPenaltyValue_reaccount_eq (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : Native.NormalAccounting I) (penalty : ℝ≥0∞) :
    paidPenaltyValue input C accounting' penalty = paidPenaltyValue input C accounting penalty :=
  le_antisymm (paidPenaltyValue_reaccount_le input C accounting accounting' penalty)
    (paidPenaltyValue_reaccount_le input C accounting' accounting penalty)

theorem paidPenaltyObjective_recap_eq {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (quota : I.Stage → ℕ) (H H0 : ℕ)
    (accounting : Native.NormalAccounting I) (rule : PolicyRule I Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    paidPenaltyObjective input (C.withCaps quota H H0) accounting rule ν penalty =
      paidPenaltyObjective input C accounting rule ν penalty := by
  unfold paidPenaltyObjective Native.expectedBill Native.runActualBill Native.risk
  simp_rw [Native.run_recap_eq, Native.runSuccess_recap_iff]

theorem paidPenaltyValue_recap_eq (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : Native.NormalAccounting I) (penalty : ℝ≥0∞) :
    paidPenaltyValue input (C.withCaps quota H H0) accounting penalty = paidPenaltyValue input C accounting penalty := by
  apply le_antisymm
  · conv_rhs => unfold paidPenaltyValue
    refine le_iInf fun Seed => le_iInf fun m => ?_
    let : MeasurableSpace Seed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun policy => ?_
    have h := paidPenaltyValue_le_policy input (C.withCaps quota H H0) accounting penalty ν
      (policy.recap input C quota H H0 accounting)
    change paidPenaltyValue input (C.withCaps quota H H0) accounting penalty ≤
      paidPenaltyObjective input (C.withCaps quota H H0) accounting policy.rule ν penalty at h
    rwa [paidPenaltyObjective_recap_eq] at h
  · conv_rhs => unfold paidPenaltyValue
    refine le_iInf fun Seed => le_iInf fun m => ?_
    let : MeasurableSpace Seed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun policy => ?_
    have h := paidPenaltyValue_le_policy input C accounting penalty ν
      (policy.uncapMetadata input C quota H H0 accounting)
    change paidPenaltyValue input C accounting penalty ≤ paidPenaltyObjective input C accounting policy.rule ν penalty at h
    rwa [← paidPenaltyObjective_recap_eq input C quota H H0 accounting policy.rule ν penalty] at h

/-- Zero resource metadata represents the uncapped current-PAYMENT contract;
allocation and physical execution both remain current-window requirements. -/
def paidRelaxedContract (I : Instance) : Contract I :=
  ⟨.early, .currentWindow, .currentWindow, fun _ => 0, 0, 0⟩

theorem paidRelaxedContract_rights (I : Instance) : (paidRelaxedContract I).IsCurrentPayment :=
  ⟨⟨rfl, rfl⟩, rfl⟩

theorem currentPayment_zeroCaps (C : Contract I) (hC : C.IsCurrentPayment) :
    C.withCaps (fun _ => 0) 0 0 = paidRelaxedContract I := by
  rcases C with ⟨reporting, allocation, execution, quota, H, H0⟩
  rcases hC with ⟨⟨hr, ha⟩, he⟩
  change reporting = .early at hr
  change allocation = .currentWindow at ha
  change execution = .currentWindow at he
  subst reporting
  subst allocation
  subst execution
  rfl

def zeroAccounting (I : Instance) : Native.NormalAccounting I := fun _ _ _ => 0

/-- Shared-pool states are closed under both successors, including empty
tasks and states with more available tools than remaining facts. -/
def freshInstance (n k : ℕ) : Instance where
  toolCount := k
  compatibility := List.replicate n Finset.univ

namespace Parameters

def freshInput (P : PaperProofs.Paid.Parameters) (n k : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    StatisticalInput (freshInstance n k) where
  experiment := fun _ => P.experiment
  correctionFee := fun _ _ => fee
  correctionFee_nonneg := fun _ _ => hfee

theorem freshInstance_original (P : PaperProofs.Paid.Parameters) :
    freshInstance P.certificate.stages P.tools = P.sharedInstance := rfl

theorem freshInput_original (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    P.freshInput P.certificate.stages P.tools fee hfee = P.input fee hfee := rfl

/-- F is independently defined by the real policy infimum; no recurrence
or asserted controller performance occurs in this definition. -/
noncomputable def freshPaidPenalty (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  paidPenaltyValue (P.freshInput n k fee hfee) (paidRelaxedContract (freshInstance n k))
    (zeroAccounting (freshInstance n k)) penalty

theorem freshPaidPenalty_le_penalty (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) :
    P.freshPaidPenalty fee hfee n k penalty ≤ penalty :=
  paidPenaltyValue_le_penalty _ _ _ _

theorem freshPaidPenalty_empty (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (k : ℕ) (penalty : ℝ≥0∞) :
    P.freshPaidPenalty fee hfee 0 k penalty = 0 := by
  have : IsEmpty (freshInstance 0 k).Stage := by
    change IsEmpty (Fin (List.replicate 0 (Finset.univ : Finset (Fin k))).length)
    simp only [List.length_replicate]
    infer_instance
  let input := P.freshInput 0 k fee hfee
  let C := paidRelaxedContract (freshInstance 0 k)
  let accounting := zeroAccounting (freshInstance 0 k)
  let ν : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have h := paidPenaltyValue_le_policy input C accounting penalty ν
    (Native.stopPolicy input C .uncapped accounting Unit)
  have hb : Native.expectedBill input C .uncapped accounting
      (Native.stopPolicy input C .uncapped accounting Unit).rule ν = 0 := by
    simp only [Native.expectedBill, Native.stop_runActualBill, lintegral_zero]
  rw [paidPenaltyObjective, hb, Native.stop_risk_empty, mul_zero, add_zero] at h
  exact le_antisymm h zero_le

/-- A_(n,k), defined at a nonterminal n by the genuine fresh successor F. -/
noncomputable def paidGoodSuccessor (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  P.freshPaidPenalty fee hfee (n - 1) k penalty

/-- B_(n,k): a real correction is paid immediately, or the task abandons.
No allocation-only or delayed-payment alternative is introduced. -/
noncomputable def paidBadSuccessor (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  match k with
  | 0 => penalty
  | next + 1 => min penalty (ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee (n - 1) next penalty)

noncomputable def paidEndpointObjective (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) +
    ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ)) * P.paidGoodSuccessor fee hfee n k penalty +
    ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) * P.paidBadSuccessor fee hfee n k penalty

def IsPaidEndpointMinimizer (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ) : Prop :=
  ∀ index : ℕ, P.paidEndpointObjective fee hfee n k penalty m ≤
    P.paidEndpointObjective fee hfee n k penalty index

def IsLeastPaidEndpointMinimizer (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ) : Prop :=
  P.IsPaidEndpointMinimizer fee hfee n k penalty m ∧
    ∀ other : ℕ, P.IsPaidEndpointMinimizer fee hfee n k penalty other → m ≤ other

/-- D16 source penalties are finite nonnegative real numbers. ENNReal is
used for all policy costs; only this multiplier is required to be finite. -/
def PaidSuccessorOrder (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞),
    0 < n → penalty ≠ ⊤ →
      0 ≤ P.paidGoodSuccessor fee hfee n k penalty ∧
      P.paidGoodSuccessor fee hfee n k penalty ≤ P.paidBadSuccessor fee hfee n k penalty ∧
      P.paidBadSuccessor fee hfee n k penalty ≤ penalty

/-- The exact Bellman target compares the independently defined full-history
F with endpoints. It is not a definition of F and not a Policy hypothesis. -/
def ExactPaidPenaltyBellman (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞),
    0 < n → penalty ≠ ⊤ →
      P.freshPaidPenalty fee hfee n k penalty =
        min penalty (⨅ m : ℕ, P.paidEndpointObjective fee hfee n k penalty m)

/-- Source's least minimizing TESTING index, independently of whether the
outer abandonment action wins. The endpoint infimum must be attained. -/
def PaidEndpointMinimumExists (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞),
    0 < n → penalty ≠ ⊤ → ∃ m : ℕ,
      P.IsLeastPaidEndpointMinimizer fee hfee n k penalty m ∧
      (⨅ index : ℕ, P.paidEndpointObjective fee hfee n k penalty index) =
        P.paidEndpointObjective fee hfee n k penalty m

/-- Resource metadata and normal-call counters are immaterial only in the
cap-relaxed I_pay problem. The original-instance bridge is proved below. -/
def FreshPaidPenaltyOriginalIdentification (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (penalty : ℝ≥0∞),
    P.freshPaidPenalty fee hfee P.certificate.stages P.tools penalty =
      paidPenaltyValue (P.input fee hfee) C.val accounting penalty

/-- This is actual all-policy equivalence of the original paid input, not
an equality between current allocation and the stricter payment contract. -/
theorem freshPaidPenaltyOriginalIdentification (P : PaperProofs.Paid.Parameters) :
    P.FreshPaidPenaltyOriginalIdentification := by
  intro fee hfee C accounting penalty
  change paidPenaltyValue (P.input fee hfee) (paidRelaxedContract P.sharedInstance)
    (zeroAccounting P.sharedInstance) penalty = _
  rw [← currentPayment_zeroCaps C.val C.property, paidPenaltyValue_recap_eq]
  exact paidPenaltyValue_reaccount_eq _ C.val accounting (zeroAccounting P.sharedInstance) penalty

/-- D16's full first-round interface. Empty-task, F<=lambda and original-input
identification are proved above. Successor ordering, Bellman equality and
endpoint attainment remain unproved rather than being built into F. -/
def PaidPenaltyProgramClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.FreshPaidPenaltyOriginalIdentification ∧ P.PaidSuccessorOrder ∧ P.ExactPaidPenaltyBellman ∧
    P.PaidEndpointMinimumExists

noncomputable def paidSuccessorGap (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  P.paidBadSuccessor fee hfee n k penalty - P.paidGoodSuccessor fee hfee n k penalty

noncomputable def paidReducedEndpointObjective (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) +
    ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) * P.paidSuccessorGap fee hfee n k penalty

/-- D17: the original real endpoint charges diverge, and one extra integer
boundary level costs at least one actual review. This is not an assumed menu. -/
def PaidEndpointGrowth (P : PaperProofs.Paid.Parameters) : Prop :=
  Tendsto (fun m : ℕ => (P.binarySymmetric.endpointCharge m : ℝ)) atTop atTop ∧
    ∀ m : ℕ, 1 ≤ m → P.reviewFee ≤
      P.binarySymmetric.endpointCharge m - P.binarySymmetric.endpointCharge (m - 1)

/-- D17's strict adjacent improvement for the SMALLEST testing minimizer,
and the necessary inequality D p_(m-1)>c. All quantities remain ENNReal. -/
def PaidMenuNecessary (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ),
    0 < n → penalty ≠ ⊤ → 1 ≤ m →
    P.IsLeastPaidEndpointMinimizer fee hfee n k penalty m →
      P.paidReducedEndpointObjective fee hfee n k penalty m <
        P.paidReducedEndpointObjective fee hfee n k penalty (m - 1) ∧
      ENNReal.ofReal (P.reviewFee : ℝ) <
        P.paidSuccessorGap fee hfee n k penalty *
          ENNReal.ofReal (P.binarySymmetric.endpointError (m - 1) : ℝ)

/-- The DERIVED menu uses exactly the original Lambda, M and epsilon.
The fee f is unrestricted and does not enter those certificate numbers. -/
def PaidFiniteMenu (P : PaperProofs.Paid.Parameters) : Prop :=
  (∀ (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ),
    0 < n → penalty ≤ ENNReal.ofReal (P.Lambda : ℝ) →
    P.IsLeastPaidEndpointMinimizer fee hfee n k penalty m → m ≤ P.certificate.M) ∧
  (2 * P.reviewFee < P.Lambda) ∧ 1 ≤ P.certificate.M ∧
    P.certificate.epsilon <
      P.binarySymmetric.endpointError (P.certificate.M - 1) / P.binarySymmetric.odds ∧
    P.binarySymmetric.endpointError (P.certificate.M - 1) / P.binarySymmetric.odds ≤
      P.binarySymmetric.endpointError P.certificate.M

/-- Complete D17 first-round targets. None is used as an assumption in F,
its comparison class, a native policy, or the original integer searches. -/
def PaidPenaltyMenuClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.PaidEndpointGrowth ∧ P.PaidEndpointMinimumExists ∧ P.PaidMenuNecessary ∧ P.PaidFiniteMenu

end Parameters
end PaperProofs.Paid
