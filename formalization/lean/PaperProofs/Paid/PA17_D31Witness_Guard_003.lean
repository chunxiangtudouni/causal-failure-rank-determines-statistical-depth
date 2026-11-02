module

public import PaperProofs.Paid.BridgeClaims
public import PaperProofs.Common.NativeCapTransfer
public import PaperProofs.Common.NativeHorizon

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessGuard003

open Common Common.Native MeasureTheory
open scoped BigOperators ENNReal

variable {I : Instance}

theorem writtenPorts_write (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    writtenPorts (reportedWriteLedger C s stage bit) = insert stage (writtenPorts s.ledger) := by
  classical
  have hw : (reportedWriteLedger C s stage bit).written =
      Function.update s.ledger.written stage (some bit) := by
    simp only [reportedWriteLedger]
    split_ifs <;> rfl
  ext other
  by_cases heq : other = stage
  · subst other
    simp [writtenPorts, hw]
  · simp [writtenPorts, hw, heq]

theorem writtenPorts_write_card (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool)
    (hopen : s.ledger.written stage = none) :
    (writtenPorts (reportedWriteLedger C s stage bit)).card = (writtenPorts s.ledger).card + 1 := by
  rw [writtenPorts_write, Finset.card_insert_of_notMem]
  simp [writtenPorts, hopen]

def blindNormalPotential (s : State I) : ℕ :=
  s.cursor + (writtenPorts s.ledger).card + s.ledger.commitments.length

theorem step_blindNormalPotential (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (tapes : ReviewTapes input) {s next : State I} {action : Action I}
    (hs : Step input C mode (blindCallAccounting I) tapes s action next)
    (hn : s.ledger.normalCalls = (blindNormalPotential s : ℕ∞)) :
    next.ledger.normalCalls = (blindNormalPotential next : ℕ∞) := by
  cases hs with
  | review stage live port resources =>
    simpa only [record, reviewLedger, blindCallAccounting, Nat.cast_zero, add_zero,
      blindNormalPotential, writtenPorts] using hn
  | write stage bit live port resources =>
    have hw := writtenPorts_write_card C s stage bit port
    have hf : (reportedWriteLedger C s stage bit).normalCalls = s.ledger.normalCalls ∧
        (reportedWriteLedger C s stage bit).commitments = s.ledger.commitments := by
      simp only [reportedWriteLedger]
      split_ifs <;> exact ⟨rfl, rfl⟩
    simp only [record, blindCallAccounting, Nat.cast_one, hf.1, blindNormalPotential,
      writtenPorts] at hn ⊢
    change s.ledger.normalCalls + 1 =
      ((s.cursor + (writtenPorts (reportedWriteLedger C s stage bit)).card +
        (reportedWriteLedger C s stage bit).commitments.length : ℕ) : ℕ∞)
    rw [hf.2, hw, hn]
    simp only [Nat.cast_add, Nat.cast_one]
    ac_rfl
  | allocate handle tool active valid compatible unused unallocated window resources =>
    simp only [record, blindCallAccounting, Nat.cast_one, allocateLedger,
      blindNormalPotential, writtenPorts, List.length_append, List.length_singleton,
      Nat.cast_add, Nat.cast_one] at hn ⊢
    rw [hn]
    ac_rfl
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    simpa only [record, executeLedger, blindCallAccounting, Nat.cast_zero, add_zero,
      blindNormalPotential, writtenPorts] using hn
  | advance stage live written resources =>
    simp only [record, advanceLedger, blindCallAccounting, Nat.cast_one,
      blindNormalPotential, writtenPorts, Nat.cast_add, Nat.cast_one] at hn ⊢
    rw [hn]
    ac_rfl
  | stop active => exact hn
  | abandon active => exact hn

theorem prefix_blindNormalPotential (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode (blindCallAccounting I) rule seed truth tapes n s) :
    s.ledger.normalCalls = (blindNormalPotential s : ℕ∞) := by
  induction hp with
  | initial => simp [initial, blindNormalPotential, writtenPorts]
  | next earlier hs ih => exact step_blindNormalPotential input C mode tapes hs ih

theorem prefix_blindNormalCalls_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode (blindCallAccounting I) rule seed truth tapes n s) :
    s.ledger.normalCalls ≤ ((2 * I.stageCount + I.toolCount : ℕ) : ℕ∞) := by
  rw [prefix_blindNormalPotential input C mode rule seed truth tapes hp]
  apply ENat.natCast_le_natCast.mpr
  have hcursor := (prefix_cursorInvariant input C mode (blindCallAccounting I) rule seed truth tapes hp).bound
  have hwritten : (writtenPorts s.ledger).card ≤ I.stageCount := by
    have hh := Finset.card_le_card
      (Finset.filter_subset (fun stage : I.Stage => s.ledger.written stage ≠ none) Finset.univ)
    simpa only [writtenPorts, Finset.card_univ, Instance.Stage, Instance.stageCount,
      Fintype.card_fin] using hh
  have hcommitments : s.ledger.commitments.length ≤ I.toolCount := by
    have hh := (prefix_ledgerWellFormed input C mode (blindCallAccounting I)
      rule seed truth tapes hp).commitment_tools.length_le_card
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hh
  unfold blindNormalPotential
  omega

theorem prefix_blindTotalCalls_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode (blindCallAccounting I) rule seed truth tapes n s)
    (hreviews : ∀ stage, s.ledger.reviews stage = 0) :
    s.ledger.totalCalls ≤ ((2 * I.stageCount + 2 * I.toolCount : ℕ) : ℕ∞) := by
  have hn := prefix_blindNormalCalls_le input C mode rule seed truth tapes hp
  have hex := (Ledger.execution_count_le (prefix_ledgerWellFormed input C mode
    (blindCallAccounting I) rule seed truth tapes hp)).trans (min_le_right _ _)
  have hh := add_le_add hn (ENat.natCast_le_natCast.mpr hex)
  simpa only [Ledger.totalCalls, hreviews, Finset.sum_const_zero, add_zero,
    Nat.cast_add, two_mul, add_assoc] using hh

theorem retainedExample_prefix_caps (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (allocation : Deadline)
    {Seed : Type*} (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .uncapped
      (blindCallAccounting P.sharedInstance) rule seed truth tapes n s)
    (hreviews : ∀ stage, s.ledger.reviews stage = 0) :
    s.ledger.obeysCaps (P.retainedPaymentExampleContract allocation) := by
  refine ⟨?_, ?_⟩
  · intro stage
    simp only [hreviews, Parameters.retainedPaymentExampleContract, Nat.cast_zero, le_refl]
  · have ht := prefix_blindTotalCalls_le (P.input fee hfee)
      (P.retainedPaymentExampleContract allocation) .uncapped rule seed truth tapes hp hreviews
    apply ht.trans
    apply ENat.natCast_le_natCast.mpr
    change 2 * P.sharedInstance.stageCount + 2 * P.tools ≤ 4 * P.certificate.stages + 1
    rw [P.stageCount_eq]
    have hk := P.tools_lt_stages
    omega

theorem retainedExample_prefix_normalCalls (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (allocation : Deadline)
    {Seed : Type*} (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .uncapped
      (blindCallAccounting P.sharedInstance) rule seed truth tapes n s) :
    s.ledger.normalCalls ≤ ((P.retainedPaymentExampleContract allocation).normalCallBound : ℕ∞) := by
  have hn := prefix_blindNormalCalls_le (P.input fee hfee)
    (P.retainedPaymentExampleContract allocation) .uncapped rule seed truth tapes hp
  apply hn.trans
  apply ENat.natCast_le_natCast.mpr
  change 2 * P.sharedInstance.stageCount + P.tools ≤ 3 * P.certificate.stages + 1
  rw [P.stageCount_eq]
  have hk := P.tools_lt_stages
  omega

theorem retainedExample_native_legal (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (allocation : Deadline)
    {Seed : Type*} (rule : PolicyRule P.sharedInstance Seed)
    (hlegal : LegalRule (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .uncapped
      (blindCallAccounting P.sharedInstance) rule)
    (hzero : ∀ seed truth tapes n s,
      Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .uncapped
        (blindCallAccounting P.sharedInstance) rule seed truth tapes n s →
      ∀ stage, s.ledger.reviews stage = 0) :
    LegalRule (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) rule := by
  apply legalRule_native_of_prefix_caps (P.input fee hfee)
    (P.retainedPaymentExampleContract allocation) (blindCallAccounting P.sharedInstance) rule hlegal
  intro seed truth tapes n s hp
  exact retainedExample_prefix_caps P fee hfee allocation rule seed truth tapes hp
    (hzero seed truth tapes n s hp)

end PaperProofs.Paid.PA17D31WitnessGuard003
