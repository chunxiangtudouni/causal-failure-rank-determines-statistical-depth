module

public import PaperProofs.Paid.RootPaidToolTransport002

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal BigOperators

def upImage (k : ℕ) : Finset (Fin (k + 1)) := Finset.univ.image (upTool k)

theorem upTool_mem_upImage (k : ℕ) (tool : Fin k) : upTool k tool ∈ upImage k :=
  Finset.mem_image.mpr ⟨tool, Finset.mem_univ _, rfl⟩

theorem last_not_mem_upImage (k : ℕ) : Fin.last k ∉ upImage k := by
  intro h
  obtain ⟨tool, _, he⟩ := Finset.mem_image.mp h
  have hv : tool.val = k := congrArg (fun t : Fin (k + 1) => t.val) he
  exact (Nat.ne_of_lt tool.isLt) hv

theorem upAction_allocate_image (n k : ℕ) (action : Action (freshInstance n k))
    (handle : MismatchHandle (freshInstance n (k + 1))) (tool : (freshInstance n (k + 1)).Tool)
    (ha : upAction n k action = .allocate handle tool) : tool ∈ upImage k := by
  cases action <;> simp [upAction] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact upTool_mem_upImage k _

theorem upRule_allocate_image {Seed : Type*} (n k : ℕ)
    (rule : PolicyRule (freshInstance n k) Seed) (seed : Seed)
    (history : List (VisibleEvent (freshInstance n (k + 1))))
    (handle : MismatchHandle (freshInstance n (k + 1))) (tool : (freshInstance n (k + 1)).Tool)
    (ha : upRule n k rule seed history = .allocate handle tool) : tool ∈ upImage k :=
  upAction_allocate_image n k (rule seed (downHistory n k history)) handle tool ha

theorem measurable_upRule {Seed : Type*} [MeasurableSpace Seed] (n k : ℕ)
    (rule : PolicyRule (freshInstance n k) Seed) (hrule : MeasurableRule rule) :
    MeasurableRule (upRule n k rule) := by
  apply measurable_from_prod_countable_left
  intro history
  have hm : Measurable (fun seed : Seed => rule seed (downHistory n k history)) :=
    hrule.comp (measurable_id.prodMk measurable_const)
  change Measurable (fun seed : Seed => upAction n k (rule seed (downHistory n k history)))
  exact (measurable_of_countable (upAction n k)).comp
    hm

def upPaidRule {Seed : Type*} (n k : ℕ) (rule : PolicyRule (freshInstance n k) Seed) :
    PolicyRule (freshInstance n (k + 1)) Seed := PDMenu.paidGuardedRule (upImage k) (upRule n k rule)

def upPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed) :
    AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) (zeroAccounting _) (upImage k) Seed :=
  ⟨{ rule := upPaidRule n k policy.rule
     measurable_rule := PDMenu.measurable_paidGuardedRule _ _ (measurable_upRule n k policy.rule policy.measurable_rule)
     legal := PDMenu.paidGuardedRule_legal _ _ rfl _ _ _ },
    PDMenu.paidGuardedRule_usesOnly _ _ _ _ _⟩

theorem upLedger_correctionBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (L : Ledger (freshInstance n k)) :
    (upLedger n k L).correctionBill (P.freshInput n (k + 1) fee hfee).fees =
      L.correctionBill (P.freshInput n k fee hfee).fees := by
  simp only [Ledger.correctionBill, upLedger, List.map_map, StatisticalInput.fees, Parameters.freshInput]
  rfl

theorem upLedger_observationBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (L : Ledger (freshInstance n k)) :
    (upLedger n k L).observationBill (P.freshInput n (k + 1) fee hfee).fees =
      L.observationBill (P.freshInput n k fee hfee).fees := by
  exact (stages n k).symm.sum_comp (fun stage =>
    ENNReal.ofReal ((P.freshInput n k fee hfee).fees.observation stage : ℝ) * (L.reviews stage : ℝ≥0∞))

theorem upLedger_actualBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (L : Ledger (freshInstance n k)) :
    (upLedger n k L).actualBill (P.freshInput n (k + 1) fee hfee).fees =
      L.actualBill (P.freshInput n k fee hfee).fees := by
  unfold Ledger.actualBill
  rw [upLedger_observationBill, upLedger_correctionBill]

theorem upLedger_success (n k : ℕ) (L : Ledger (freshInstance n k))
    (h : L.success (paidRelaxedContract _)) :
    (upLedger n k L).success (paidRelaxedContract _) := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro stage time ht hw
    obtain ⟨ha, he⟩ := h.2.2.1 (downStage n k stage) time ht hw
    constructor
    · intro hc
      obtain ⟨a, hamem, hastage, hatime⟩ := ha hc
      refine ⟨upCommitment n k a, List.mem_map.mpr ⟨a, hamem, rfl⟩, ?_, hatime⟩
      exact (congrArg (upStage n k) hastage).trans (up_down_stage n k stage)
    · intro hc
      obtain ⟨e, hemem, hestage, hetime⟩ := he hc
      refine ⟨upExecution n k e, List.mem_map.mpr ⟨e, hemem, rfl⟩, ?_, hetime⟩
      exact (congrArg (upStage n k) hestage).trans (up_down_stage n k stage)
  · intro stage
    rcases h.2.2.2 (downStage n k stage) with hw | ⟨e, he, hstage⟩
    · exact Or.inl hw
    · refine Or.inr ⟨upExecution n k e, List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
      exact (congrArg (upStage n k) hstage).trans (up_down_stage n k stage)

end RootPaidToolTransport
