module

public import PaperProofs.Paid.PDROC_SimulatorHandles_001
public import PaperProofs.Paid.PDROC_SimulatorProjection_002
public import PaperProofs.Paid.PDROC_SimulatorLaw_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem historyValidHandle_of_validHandle (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (handle : MismatchHandle I) (hv : validHandle s handle) :
    historyValidHandle s.history handle := by
  obtain ⟨time, ht⟩ := hv.2.2
  unfold historyValidHandle
  rw [prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp handle.stage,
    ht, Option.map_some, prefix_historyWritten input C mode accounting rule seed truth tapes hp handle.stage,
    prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp handle.stage]
  exact ⟨hv.1, hv.2.1, hv.2.1.symm⟩

/-- Every genuine step under the original current-payment contract satisfies
the existing public guard. This is completeness, with no new permissions. -/
theorem historyAllowsAction_of_step (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I} {action : Action I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (hs : Step input C mode accounting tapes s action next) : historyAllowsAction s.history action := by
  cases hs with
  | review stage live port resources | write stage bit live port resources =>
    exact ⟨(prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans live.2,
      (prefix_historyWritten input C mode accounting rule seed truth tapes hp stage).trans port⟩
  | advance stage live written resources =>
    exact ⟨(prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans live.2,
      fun h => written ((prefix_historyWritten input C mode accounting rule seed truth tapes hp stage).symm.trans h)⟩
  | allocate handle tool active valid compatible unused unallocated window resources =>
    refine ⟨(prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans (window hpay.1.2),
      historyValidHandle_of_validHandle input C hpay.1.1 mode accounting rule seed truth tapes hp handle valid,
      compatible, (prefix_historyUnused_iff input C mode accounting rule seed truth tapes hp tool).mpr unused, ?_⟩
    intro pair hm
    rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact unallocated a ha
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    refine ⟨(prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans (window hpay.2),
      historyValidHandle_of_validHandle input C hpay.1.1 mode accounting rule seed truth tapes hp handle valid,
      compatible, ?_, ?_, ?_⟩
    · obtain ⟨a, ha, hh, hr⟩ := committed
      rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨a, ha, Prod.ext hh hr⟩
    · intro pair hm
      rw [prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      exact unused e he
    · intro pair hm
      rw [prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      exact uncorrected e he
  | stop | abandon => trivial

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- After a real write, a genuine source-prefix action transports through
the actual simulator guard. All serial/handle/projection premises are
discharged by the concrete fold invariants. -/
theorem simulator_postwrite_rule_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (seed : SimulatorSeed P Seed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) seed truth tapes n s)
    (ha : s.halted = false) (stage : P.sharedInstance.Stage) (hc : s.cursor = stage.val)
    (hw : s.ledger.written stage ≠ none)
    (vtruth : P.sharedInstance.Stage → Bool) (vtapes : ReviewTapes (P.input fee hfee))
    {vn : ℕ} {vs : State P.sharedInstance}
    (vp : Prefix (P.input fee hfee) C.val .uncapped accounting source seed.1 vtruth vtapes vn vs)
    (va : vs.halted = false) (vh : vs.history = simulatorShadow P fee hfee source seed s.history) :
    simulatorRule P fee hfee source seed s.history =
      reserialAction s.history (fun _ bit => bit) (source seed.1 (simulatorShadow P fee hfee source seed s.history)) := by
  obtain ⟨next, hs⟩ := hl seed.1 vtruth vtapes vn vs vp va
  have hvallow := historyAllowsAction_of_step (P.input fee hfee) C.val C.property .uncapped accounting
    source seed.1 vtruth vtapes vp hs
  rw [vh] at hvallow
  have hproj := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) seed s.history
  have hallow := historyAllowsAction_reserial_transport s.history (simulatorShadow P fee hfee source seed s.history)
    (fun _ bit => bit) (source seed.1 (simulatorShadow P fee hfee source seed s.history)) hproj.1 hproj.2.2.2.1
    (simulatorShadow_validHandle_prefix P fee hfee C .uncapped accounting source
      (simulatorRule P fee hfee source) seed truth tapes hp)
    (prefix_simulatorCommitments_reserial (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp (simulatorSeedDraw P fee hfee source) seed)
    (prefix_simulatorExecutions_reserial (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp (simulatorSeedDraw P fee hfee source) seed) hvallow
  have hhalt := prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) seed truth tapes hp
  have hcursor := prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) seed truth tapes hp
  have hwrite := prefix_historyWritten (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) seed truth tapes hp stage
  have hcandidate : simulatorCandidate P fee hfee source seed s.history =
      reserialAction s.history (fun _ bit => bit) (source seed.1 (simulatorShadow P fee hfee source seed s.history)) := by
    have hstage : simulatorStageAt s.history = some stage := by
      simp only [simulatorStageAt, hcursor, hc, stage.isLt, ↓reduceDIte]
    simp only [simulatorCandidate, simulatorCandidateAtCache, simulatorCandidateFromData, hhalt, ha,
      Bool.false_eq_true, ↓reduceIte, hstage, hwrite, hw, simulatorShadow]
  simp only [simulatorRule, hcandidate, hallow, ↓reduceIte]

end PDROC
