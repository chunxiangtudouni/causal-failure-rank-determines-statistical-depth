module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Common.NativeHorizon

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Seed : Type*}

theorem prefix_progress_le_of_review_sum (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (Q : ℕ) (hq : (∑ i, s.ledger.reviews i) ≤ (Q : ℕ∞)) :
    actionProgress s ≤ ((Q + I.toolCount + I.toolCount + I.stageCount + I.stageCount + 1 : ℕ) : ℕ∞) := by
  have hwf := prefix_ledgerWellFormed input C mode accounting rule seed truth tapes hp
  have hcursor := (prefix_cursorInvariant input C mode accounting rule seed truth tapes hp).bound
  have hcommitments : s.ledger.commitments.length ≤ I.toolCount := by
    have hh := hwf.commitment_tools.length_le_card
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hh
  have hexecutions : s.ledger.executions.length ≤ I.toolCount :=
    (Ledger.execution_count_le hwf).trans (min_le_right _ _)
  have hwritten : (writtenPorts s.ledger).card ≤ I.stageCount := by
    have hh := Finset.card_le_card (Finset.filter_subset
      (fun stage : I.Stage => s.ledger.written stage ≠ none) Finset.univ)
    simpa only [writtenPorts, Finset.card_univ, Instance.Stage, Instance.stageCount, Fintype.card_fin] using hh
  have hhalted : (if s.halted then (1 : ℕ∞) else 0) ≤ 1 := by cases s.halted <;> simp
  have ht := add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add hq
      (ENat.natCast_le_natCast.mpr hcommitments)) (ENat.natCast_le_natCast.mpr hexecutions))
      (ENat.natCast_le_natCast.mpr hcursor)) (ENat.natCast_le_natCast.mpr hwritten)) hhalted
  simpa only [actionProgress, ENat.natCast_add, ENat.natCast_one] using ht

theorem paid_observationBill_eq_review_sum (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (L : Ledger P.sharedInstance) :
    L.observationBill (P.input fee hfee).fees =
      ENNReal.ofReal (P.reviewFee : ℝ) * ((∑ i, L.reviews i : ℕ∞) : ℝ≥0∞) := by
  have hcast : ((∑ i, L.reviews i : ℕ∞) : ℝ≥0∞) = ∑ i, (L.reviews i : ℝ≥0∞) :=
    map_sum ENat.toENNRealRingHom _ _
  change (∑ i, ENNReal.ofReal (P.reviewFee : ℝ) * (L.reviews i : ℝ≥0∞)) = _
  rw [hcast, Finset.mul_sum]

/-- A finite actual full bill forces the original returned-action Policy
interpreter to terminate, with no extra cap or success assumption. -/
theorem paid_finiteBill_exists_halt (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C mode accounting rule)
    (sample : Seed × (P.input fee hfee).World)
    (hb : runActualBill (P.input fee hfee) C mode accounting rule sample ≠ ⊤) :
    ∃ n, (run (P.input fee hfee) C mode accounting rule sample n).halted = true := by
  let q := runActualBill (P.input fee hfee) C mode accounting rule sample
  let c := ENNReal.ofReal (P.reviewFee : ℝ)
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by exact_mod_cast P.reviewFee_pos))
  obtain ⟨Q, hQ⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hb hc)
  have hsum (n : ℕ) : (∑ i, (run (P.input fee hfee) C mode accounting rule sample n).ledger.reviews i) ≤
      (Q : ℕ∞) := by
    have ho := ((run (P.input fee hfee) C mode accounting rule sample n).ledger.observationBill_le_actualBill
      (P.input fee hfee).fees).trans (prefixBill_le_runActualBill (P.input fee hfee) C mode accounting rule sample n)
    rw [paid_observationBill_eq_review_sum] at ho
    have hdiv : ((∑ i, (run (P.input fee hfee) C mode accounting rule sample n).ledger.reviews i : ℕ∞) : ℝ≥0∞) ≤ q / c :=
      (ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inl ENNReal.ofReal_ne_top)).mpr (by simpa only [mul_comm] using ho)
    exact ENat.toENNReal_le_natCast.mp (hdiv.trans hQ.le)
  by_contra hn
  let n := Q + P.sharedInstance.toolCount + P.sharedInstance.toolCount +
    P.sharedInstance.stageCount + P.sharedInstance.stageCount + 1 + 1
  have ha : (run (P.input fee hfee) C mode accounting rule sample n).halted = false :=
    Bool.eq_false_iff.mpr (fun h => hn ⟨n, h⟩)
  have hp := run_prefix_of_active (P.input fee hfee) C mode accounting rule hl sample n ha
  have hle := prefix_progress_le_of_review_sum (P.input fee hfee) C mode accounting rule sample.1
    ((P.input fee hfee).truthAt sample.2) (worldTapes (P.input fee hfee) sample.2) hp Q (hsum n)
  rw [prefix_actionProgress (P.input fee hfee) C mode accounting rule sample.1 _ _ hp] at hle
  have hh := ENat.natCast_le_natCast.mp hle
  dsimp only [n] at hh
  omega

/-- The source termination conjunct required by D06 follows from the original
finite full actual expectation, without an independent finite-ET premise. -/
theorem paid_finiteExpectedBill_completedHistory (P : PaperProofs.Paid.Parameters)
    {Seed : Type*} [MeasurableSpace Seed]
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C mode accounting Seed) (ν : Measure Seed)
    (hf : expectedBill (P.input fee hfee) C mode accounting policy.rule ν ≠ ⊤) :
    (P.input fee hfee).seededWorldLaw ν {sample |
      completedHistory (P.input fee hfee) C mode accounting policy.rule sample = none} = 0 := by
  have hae : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      completedHistory (P.input fee hfee) C mode accounting policy.rule sample ≠ none := by
    filter_upwards [ae_lt_top (measurable_runActualBill (P.input fee hfee) C mode accounting
      policy.rule policy.measurable_rule) hf] with sample hs
    intro hn
    exact (completedHistory_none_iff (P.input fee hfee) C mode accounting policy.rule sample).mp hn
      (paid_finiteBill_exists_halt P fee hfee C mode accounting policy.rule policy.legal sample
        (ne_of_lt hs))
  simpa only [not_not] using (ae_iff.mp hae)

end PDROC
