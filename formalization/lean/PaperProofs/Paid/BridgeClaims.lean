module

public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Paid.Survival
public import PaperProofs.Common.ReferenceCertification
public import PaperProofs.Statistics.Coefficient

/-!
First-round claims for paid-proofs.tex:720--741 and bridge.tex:18--71.
D31 retains real native delayed-payment policies and actual payments.
D33 uses the independent game rank and original ordered coefficient.
D34 is a fixed-pool same-native FREE I_pay value squeeze, with the actual
free reference controller's original H0 qualification, never equality of
finite-risk I and I_pay optimized values.

The pool N,K,c,gamma is fixed before epsilon and the real cutoff. Risk
targets remain the original rational inputs. No smaller rational risk is
substituted, and no Q or H is enlarged. D32 and the full qualified-caps D36
are NOT claimed here: the original paid algorithm still needs a concrete
rule to which its all-path normal-call certificate can be attached.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace PaperProofs.Paid

open Common Common.Native PaperProofs.Statistics PaperProofs.Structure

universe u

/-- Ordinary write/advance/allocation calls count once, while a physical
execution has its separate native execution count. This fixes one original
interface for the D31 counterexample; it does not bound all comparators. -/
def blindCallAccounting (I : Instance) : NormalAccounting I := fun _ action _ =>
  match action with
  | .review _ | .execute _ _ => 0
  | _ => 1

namespace Parameters

/-- A concrete original zero-review contract. Either allocation deadline
is allowed, but physical execution/payment may be retained to the barrier.
The finite H is fixed before constructing the witness, not enlarged later. -/
def retainedPaymentExampleContract (P : PaperProofs.Paid.Parameters) (allocation : Deadline) :
    Contract P.sharedInstance :=
  ⟨.early, allocation, .terminalBarrier, fun _ => 0,
    4 * P.certificate.stages + 1, 3 * P.certificate.stages + 1⟩

noncomputable def blindErrorCount (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : Unit × (P.input fee hfee).World) : ℕ :=
  (Finset.univ.filter (fun stage : P.sharedInstance.Stage => (sample.2 stage).1 = true)).card

/-- The minimum blind risk refers to EVERY legal randomized visible-history
native policy under the same original zero-review contract. -/
def BlindRiskMinimal (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (accounting : NormalAccounting P.sharedInstance) : Prop :=
  ∀ (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ policy : Policy (P.input fee hfee) C .native accounting Seed,
        ENNReal.ofReal ((1 / 2 : ℚ) ^ P.certificate.stages : ℝ) ≤
          risk (P.input fee hfee) C .native accounting policy.rule ν

/-- D31: a genuine blind native policy corrects exactly its errors unless
ALL facts are erroneous. On that failing event it makes no actual payment.
The numerical violation concerns only transferring the usage inequality;
it is not a claim that every delayed-payment price law is impossible. -/
def RetainedPaymentUsageCounterexample (P : PaperProofs.Paid.Parameters) : Prop :=
  6 ≤ P.certificate.stages → P.tools = P.certificate.stages - 1 →
    P.certificate.risk = (1 / 2 : ℚ) ^ P.certificate.stages →
    ∀ (fee : ℚ) (hfee : 0 ≤ fee) (allocation : Deadline),
      let C := P.retainedPaymentExampleContract allocation
      let accounting := blindCallAccounting P.sharedInstance
      P.BlindRiskMinimal.{u} fee hfee C accounting ∧
      ∃ policy : Policy (P.input fee hfee) C .native accounting Unit,
        (∀ (sample : Unit × (P.input fee hfee).World) (n : ℕ) (stage : P.sharedInstance.Stage),
          (run (P.input fee hfee) C .native accounting policy.rule sample n).ledger.reviews stage = 0) ∧
        (∀ (sample : Unit × (P.input fee hfee).World), ∃ n : ℕ,
          allWritten (run (P.input fee hfee) C .native accounting policy.rule sample n).ledger) ∧
        (∀ (sample : Unit × (P.input fee hfee).World) (n : ℕ) (stage : P.sharedInstance.Stage) (bit : Bool),
          (run (P.input fee hfee) C .native accounting policy.rule sample n).ledger.written stage = some bit →
            bit = false) ∧
        (∀ sample : Unit × (P.input fee hfee).World,
          runRepairCount (P.input fee hfee) C .native accounting policy.rule sample =
            if P.blindErrorCount fee hfee sample = P.certificate.stages then 0
            else (P.blindErrorCount fee hfee sample : ℝ≥0∞)) ∧
        risk (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) = P.targetRisk ∧
        expectedObservationBill (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
        expectedRepairCount (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) =
          ENNReal.ofReal ((P.certificate.stages : ℝ) / 2 -
            P.certificate.stages * (P.certificate.risk : ℝ)) ∧
        expectedBill (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) =
          ENNReal.ofReal (fee : ℝ) *
            expectedRepairCount (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) ∧
        let repairs := meanRepairCount (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ())
        repairs + (P.certificate.risk : ℝ) <
          P.certificate.stages * (1 - (P.certificate.risk : ℝ)) / 2 ∧
        0 < ENNReal.ofReal (P.a * P.certificate.stages * (1 - (P.certificate.risk : ℝ))) *
          BinarySymmetric.phi (min (1 / 2)
            ((repairs + (P.certificate.risk : ℝ)) /
              ((P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ)))))

/-- D33's shared subproblem rank includes n=0 and k>=n, and has no hidden
positive-tool assumption. The rank is the existing independent game value. -/
def SharedPoolSubproblemRank : Prop :=
  ∀ n k : ℕ,
    errorRank (freshInstance n k).compatibility (freshInstance n k).tools =
      if n ≤ k then ⊤ else ((k + 1 : ℕ) : ℕ∞)

/-- A shared-pool rank calculation over the already independent game
semantics. The available set may be empty or a proper subset of all tools. -/
theorem sharedPool_rank_replicate {Tool : Type*} [Fintype Tool] [DecidableEq Tool]
    (n : ℕ) (remaining : Finset Tool) :
    errorRank (List.replicate n (Finset.univ : Finset Tool)) remaining =
      if n ≤ remaining.card then ⊤ else ((remaining.card + 1 : ℕ) : ℕ∞) := by
  induction n generalizing remaining with
  | zero => simp only [List.replicate_zero, errorRank_terminal, Nat.zero_le, ite_true]
  | succ n ih =>
    by_cases hempty : remaining = ∅
    · subst remaining
      rw [List.replicate_succ, errorRank_no_tools]
      simp
    · have hne : remaining.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      have hcard : 0 < remaining.card := Finset.card_pos.mpr hne
      have hcardone : remaining.card - 1 + 1 = remaining.card := by omega
      have hchild (tool : Tool) (htool : tool ∈ remaining) :
          errorRank (List.replicate n (Finset.univ : Finset Tool)) (remaining.erase tool) =
            if n ≤ remaining.card - 1 then ⊤ else (remaining.card : ℕ∞) := by
        rw [ih, Finset.card_erase_of_mem htool, hcardone]
      have hbad : badChildRank (Finset.univ : Finset Tool)
          (List.replicate n Finset.univ) remaining =
          if n ≤ remaining.card - 1 then ⊤ else (remaining.card : ℕ∞) := by
        apply le_antisymm
        · apply Finset.sup_le
          intro tool htool
          exact (hchild tool (Finset.mem_inter.mp htool).2).le
        · obtain ⟨tool, htool⟩ := hne
          have hh := childRank_le_badChildRank (Finset.univ : Finset Tool)
            (List.replicate n Finset.univ) remaining (Finset.mem_inter.mpr ⟨Finset.mem_univ tool, htool⟩)
          rwa [hchild tool htool] at hh
      rw [List.replicate_succ, errorRank_cons, ih, hbad]
      by_cases hn : n < remaining.card
      · have hsucc : n + 1 ≤ remaining.card := by omega
        have hprev : n ≤ remaining.card - 1 := by omega
        simp [hsucc, hn.le, hprev]
      · have hsucc : ¬ n + 1 ≤ remaining.card := by omega
        have hprev : ¬ n ≤ remaining.card - 1 := by omega
        by_cases hgood : n ≤ remaining.card
        · simp [hsucc, hprev, hgood, add_comm]
        · simp [hsucc, hprev, hgood, Nat.cast_add, Nat.cast_one, add_comm]

theorem sharedPoolSubproblemRank : SharedPoolSubproblemRank := by
  intro n k
  dsimp (config := { instances := true }) only [freshInstance, Instance.tools, Instance.Tool]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    sharedPool_rank_replicate n (Finset.univ : Finset (Fin k))

def SharedPoolRankCoefficient (P : PaperProofs.Paid.Parameters) : Prop :=
  SharedPoolSubproblemRank ∧
    errorRank P.sharedInstance.compatibility P.sharedInstance.tools = ((P.tools + 1 : ℕ) : ℕ∞) ∧
    (∀ stage : P.sharedInstance.Stage,
      badChildRank (P.sharedInstance.eligible stage)
        (P.sharedInstance.compatibility.drop (stage.val + 1)) P.sharedInstance.tools =
        if P.tools = 0 then 0
        else if stage.val < P.certificate.stages - P.tools then (P.tools : ℕ∞) else ⊤) ∧
    ∀ (fee : ℚ) (hfee : 0 ≤ fee),
      (P.input fee hfee).orderedCoefficient P.sharedInstance.tools =
        P.a * (P.certificate.stages - P.tools : ℕ)

end Parameters

/-- Only fixed pool/channel data, with K=0 included. Delta and the growing
correction price are absent, so the small-risk cutoff cannot vary with them. -/
structure FixedSharedPool where
  stages : ℕ
  stages_pos : 0 < stages
  tools : ℕ
  tools_lt_stages : tools < stages
  channel : BinarySymmetric.Parameters

namespace FixedSharedPool

def sharedInstance (pool : FixedSharedPool) : Instance := freshInstance pool.stages pool.tools

def input (pool : FixedSharedPool) (fee : ℚ) (hfee : 0 ≤ fee) : StatisticalInput pool.sharedInstance where
  experiment := fun _ => pool.channel.experiment
  correctionFee := fun _ _ => fee
  correctionFee_nonneg := fun _ _ => hfee

/-- Reuse the original paid certificate/parameter object at EXACTLY delta.
No conservative substitute is used to change its Q, Lambda, M or epsilon. -/
def atRisk (pool : FixedSharedPool) (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64) :
    PaperProofs.Paid.Parameters where
  certificate := {
    stages := pool.stages
    stages_pos := pool.stages_pos
    gamma := pool.channel.gamma
    gamma_pos := pool.channel.gamma_pos
    gamma_le_quarter := pool.channel.gamma_le_quarter
    risk := delta
    risk_pos := hd
    risk_le := hs
  }
  tools := pool.tools
  tools_lt_stages := pool.tools_lt_stages
  reviewFee := pool.channel.reviewFee
  reviewFee_pos := pool.channel.reviewFee_pos

theorem atRisk_input (pool : FixedSharedPool) (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64)
    (fee : ℚ) (hfee : 0 ≤ fee) :
    (pool.atRisk delta hd hs).input fee hfee = pool.input fee hfee := rfl

theorem atRisk_a (pool : FixedSharedPool) (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64) :
    (pool.atRisk delta hd hs).a = pool.channel.a := rfl

noncomputable def structuralScaleReal (pool : FixedSharedPool) (delta : ℚ) : ℝ :=
  pool.channel.a * (pool.stages - pool.tools : ℕ) *
    iteratedLog (pool.tools + 1) ((delta : ℝ)⁻¹)

noncomputable def structuralScale (pool : FixedSharedPool) (delta : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (pool.structuralScaleReal delta)

noncomputable def feeScale (pool : FixedSharedPool) (fee : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (pool.channel.a * pool.stages * Real.log (1 + (fee : ℝ) / pool.channel.a))

noncomputable def saturationScale (pool : FixedSharedPool) (delta : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (pool.channel.a * pool.stages * Real.log (1 + (pool.stages : ℝ) / (delta : ℝ)))

noncomputable def priceScale (pool : FixedSharedPool) (delta fee : ℚ) : ℝ≥0∞ :=
  min (pool.structuralScale delta + pool.feeScale fee) (pool.saturationScale delta)

noncomputable def nativeValue (pool : FixedSharedPool) (delta : ℚ) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract pool.sharedInstance) (accounting : NormalAccounting pool.sharedInstance) : ℝ≥0∞ :=
  Native.value (pool.input fee hfee) C .native accounting (ENNReal.ofReal (delta : ℝ))

/-- The BSC specialization of the ORIGINAL main-theorem quota. -/
def freeQuota (pool : FixedSharedPool) (delta : ℚ) : ℕ :=
  pool.channel.experiment.rationalQuota (BinaryExperiment.quotaExponent delta pool.stages)

/-- The actual free reference controller and its original H0 certificate.
The comparator remains the full native class; no comparator receives H0.
This is stronger in scope than assuming the still-unproved joint certificate. -/
def FreeControllerQualification (pool : FixedSharedPool) (delta : ℚ)
    (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting pool.sharedInstance) : Prop :=
  ReferenceOriginalQualification (pool.input 0 (by norm_num)) C hC.1.1 accounting
    pool.sharedInstance.tools delta (BinaryExperiment.quotaExponent delta pool.stages)

/-- The larger current-allocation class supplies ONLY a lower comparison.
Its native quotas/H/accounting and target delta remain identical. -/
theorem deferredFreeValue_le_currentPayment (pool : FixedSharedPool) (delta : ℚ)
    (C : Contract pool.sharedInstance) (accounting : NormalAccounting pool.sharedInstance) :
    pool.nativeValue delta 0 (by norm_num) C.deferExecution accounting ≤
      pool.nativeValue delta 0 (by norm_num) C accounting :=
  Native.value_deferred_le_original (pool.input 0 (by norm_num)) C .native accounting _

/-- D34, expressed as a uniform multiplicative squeeze instead of dividing
an infinite unknown value. The fixed pool precedes epsilon/cutoff; delta is
the exact original rational risk, and qualified caps/accounting may vary.
Only f=0 appears. There is no I=I_pay optimized-value premise. -/
def FreeNativeSqueeze (pool : FixedSharedPool) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∃ cutoff : ℝ, 0 < cutoff ∧
    ∀ (delta : ℚ), 0 < delta → delta ≤ 1 / 64 → (delta : ℝ) < cutoff →
      ∀ (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment)
        (accounting : NormalAccounting pool.sharedInstance),
        pool.FreeControllerQualification delta C hC accounting →
          ENNReal.ofReal ((1 - epsilon) * pool.structuralScaleReal delta) ≤
              pool.nativeValue delta 0 (by norm_num) C accounting ∧
          pool.nativeValue delta 0 (by norm_num) C accounting ≤
            ENNReal.ofReal ((1 + epsilon) * pool.structuralScaleReal delta)

/-- D36's pointwise NUMERICAL CONCLUSION only. This is deliberately NOT a
full theorem claim over qualified caps: that quantification still needs the
original concrete paid algorithm's H0 interface, in addition to Q_joint.
The scale includes K=0 and allows any nonnegative rational fee. -/
def FixedPoolPriceNumericalConclusion (pool : FixedSharedPool) (delta fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract pool.sharedInstance) (accounting : NormalAccounting pool.sharedInstance) (epsilon : ℝ) : Prop :=
  ENNReal.ofReal (1 - epsilon) * pool.priceScale delta fee / 129 ≤
      pool.nativeValue delta fee hfee C accounting ∧
    pool.nativeValue delta fee hfee C accounting ≤
      72 * ENNReal.ofReal (1 + epsilon) * pool.priceScale delta fee

/-- The K=0 boundary from bridge:69--71 uses the SAME original native
contract at all fees. It is an independent target, not a paid-cap surrogate. -/
def ZeroToolsFeeIndependence (pool : FixedSharedPool) : Prop :=
  pool.tools = 0 → ∀ (delta fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract pool.sharedInstance) (accounting : NormalAccounting pool.sharedInstance),
      pool.nativeValue delta fee hfee C accounting = pool.nativeValue delta 0 (by norm_num) C accounting

theorem input_eq_zero_of_no_tools (pool : FixedSharedPool) (htools : pool.tools = 0)
    (fee : ℚ) (hfee : 0 ≤ fee) : pool.input fee hfee = pool.input 0 (by norm_num) := by
  have hfees : (fun (_stage : pool.sharedInstance.Stage) (_tool : pool.sharedInstance.Tool) => fee) =
      (fun (_stage : pool.sharedInstance.Stage) (_tool : pool.sharedInstance.Tool) => (0 : ℚ)) := by
    funext stage tool
    have ht : tool.val < pool.tools := tool.isLt
    rw [htools] at ht
    omega
  unfold input
  congr 1

/-- No physical correction call exists when K=0. The actual full native
input, and hence its complete policy/value comparator, is fee independent. -/
theorem zeroToolsFeeIndependence (pool : FixedSharedPool) : pool.ZeroToolsFeeIndependence := by
  intro htools delta fee hfee C accounting
  unfold nativeValue
  rw [pool.input_eq_zero_of_no_tools htools fee hfee]

end FixedSharedPool
end PaperProofs.Paid

