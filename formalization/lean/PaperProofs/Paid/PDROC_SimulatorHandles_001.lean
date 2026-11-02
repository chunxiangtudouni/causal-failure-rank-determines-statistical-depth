module

public import PaperProofs.Paid.PDROC_Simulator_004
public import PaperProofs.Paid.PDROC_SimulatorProjection_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def HistoryHandleTransport (actual virtual : List (VisibleEvent I)) : Prop :=
  ∀ handle : MismatchHandle I, historyValidHandle virtual handle →
    historyValidHandle actual (reserialHandle actual handle)

theorem historyHandleTransport_frames
    {actual virtual actual' virtual' : List (VisibleEvent I)} (h : HistoryHandleTransport actual virtual)
    (hwa : ∀ stage, historyWrite actual' stage = historyWrite actual stage)
    (hva : ∀ stage, historyWrite virtual' stage = historyWrite virtual stage)
    (hra : ∀ stage, historyReport actual' stage = historyReport actual stage)
    (hrv : ∀ stage, historyReport virtual' stage = historyReport virtual stage) :
    HistoryHandleTransport actual' virtual' := by
  intro handle hv
  have hv' : historyValidHandle virtual handle := by
    simpa only [historyValidHandle, historyWritten, historyWriteSerial, hva, hrv] using hv
  simpa only [historyValidHandle, historyWritten, historyWriteSerial, reserialHandle, hwa, hra] using h handle hv'

theorem historyWrite_append_simulatorReviews (history : List (VisibleEvent I)) (stage other : I.Stage)
    (record : AuxiliaryRecord) :
    historyWrite (history ++ simulatorReviewPacket stage record) other = historyWrite history other := by
  simp [historyWrite, simulatorReviewPacket, List.filterMap_append, List.filterMap_map, Function.comp_def, eventWrite]

theorem historyReport_append_simulatorReviews (history : List (VisibleEvent I)) (stage other : I.Stage)
    (record : AuxiliaryRecord) :
    historyReport (history ++ simulatorReviewPacket stage record) other = historyReport history other := by
  simp [historyReport, simulatorReviewPacket, List.filterMap_append, List.filterMap_map, Function.comp_def, eventReport]

theorem historyWrite_append_wrote_same (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit : Bool) (serial : ℕ) : historyWrite (history ++ [.wrote stage bit serial]) stage = some (bit, serial) := by
  simp [historyWrite, List.filterMap_append, eventWrite]

theorem historyWrite_append_wrote_other (history : List (VisibleEvent I)) (stage other : I.Stage)
    (hne : stage ≠ other) (bit : Bool) (serial : ℕ) :
    historyWrite (history ++ [.wrote stage bit serial]) other = historyWrite history other := by
  simp [historyWrite, List.filterMap_append, eventWrite, hne]

theorem historyReport_append_wrote (history : List (VisibleEvent I)) (stage other : I.Stage)
    (bit : Bool) (serial : ℕ) : historyReport (history ++ [.wrote stage bit serial]) other = historyReport history other := by
  simp [historyReport, List.filterMap_append, eventReport]

theorem historyWrite_append_report (history : List (VisibleEvent I)) (stage other : I.Stage)
    (bit : Bool) (serial : ℕ) : historyWrite (history ++ [.report stage bit serial]) other = historyWrite history other := by
  simp [historyWrite, List.filterMap_append, eventWrite]

theorem historyReport_append_report_other (history : List (VisibleEvent I)) (stage other : I.Stage)
    (hne : stage ≠ other) (bit : Bool) (serial : ℕ) :
    historyReport (history ++ [.report stage bit serial]) other = historyReport history other := by
  simp [historyReport, List.filterMap_append, eventReport, hne]

/-- The genuine early write/report pair is transported directly. The
intermediate cache need not be a virtual Native execution. -/
theorem historyHandleTransport_writeReport
    {actual virtual : List (VisibleEvent I)} (h : HistoryHandleTransport actual virtual)
    (stage : I.Stage) (actualBit virtualBit actualTruth : Bool) (actualSerial virtualSerial : ℕ)
    (record : AuxiliaryRecord) :
    HistoryHandleTransport
      ((actual ++ [.wrote stage actualBit actualSerial]) ++ [.report stage actualTruth actualSerial])
      (((virtual ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) ++
        [.report stage (Bool.xor actualTruth (Bool.xor virtualBit actualBit)) virtualSerial]) := by
  intro handle hv
  by_cases hstage : stage = handle.stage
  · cases handle with
    | mk other serial =>
      dsimp only at hstage
      subst other
      simp only [historyValidHandle, historyReport_append_report_self, historyWritten,
        historyWriteSerial, historyWrite_append_report, historyWrite_append_wrote_same,
        reserialHandle, Option.map_some, Option.getD_some] at hv ⊢
      cases actualBit <;> cases virtualBit <;> cases actualTruth <;> simp_all
  · have hva : historyValidHandle virtual handle := by
      simpa only [historyValidHandle, historyWritten, historyWriteSerial,
        historyReport_append_report_other _ _ _ hstage, historyReport_append_wrote,
        historyWrite_append_report, historyWrite_append_wrote_other _ _ _ hstage,
        historyWrite_append_simulatorReviews, historyReport_append_simulatorReviews] using hv
    simpa only [historyValidHandle, historyWritten, historyWriteSerial, reserialHandle,
      historyReport_append_report_other _ _ _ hstage, historyReport_append_wrote,
      historyWrite_append_report, historyWrite_append_wrote_other _ _ _ hstage] using h handle hva




theorem simulatorStep_handleTransport_nonwrite {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I)
    (h : HistoryHandleTransport cache.seen cache.shadow)
    (hw : ∀ stage, eventWrite stage event = none) (hr : ∀ stage, eventReport stage event = none) :
    HistoryHandleTransport (simulatorStep draw seed cache event).seen (simulatorStep draw seed cache event).shadow := by
  cases event with
  | wrote stage bit serial => have hh := hw stage; simp [eventWrite] at hh
  | report stage bit serial => have hh := hr stage; simp [eventReport] at hh
  | observation | committed | executed | advanced | stopped | abandoned =>
    dsimp only [simulatorStep, simulatorAppend]
    all_goals (try split_ifs)
    all_goals apply historyHandleTransport_frames h
    all_goals intro other
    all_goals simp [historyWrite, historyReport, simulatorReviewPacket, List.filterMap_append,
      List.filterMap_map, Function.comp_def, eventWrite, eventReport]

theorem simulatorStep_writeReport_handles {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I)
    (h : HistoryHandleTransport cache.seen cache.shadow) (stage : I.Stage) (bit truth : Bool) (serial : ℕ) :
    let next := simulatorStep draw seed (simulatorStep draw seed cache (.wrote stage bit serial)) (.report stage truth serial)
    HistoryHandleTransport next.seen next.shadow := by
  let record := simulatorDrawRecord (draw seed stage cache.shadow)
  let virtualBit := record.decision.getD bit
  let virtualSerial := (historyActions cache.shadow).length + record.observations.length
  have hseen : historyWritten (cache.seen ++ [.wrote stage bit serial]) stage = some bit := by
    simp only [historyWritten, historyWrite_append_wrote_same, Option.map_some]
  have hshadow : historyWritten ((cache.shadow ++ simulatorReviewPacket stage record) ++
      [.wrote stage virtualBit virtualSerial]) stage = some virtualBit := by
    simp only [historyWritten, historyWrite_append_wrote_same, Option.map_some]
  have hserial : historyWriteSerial ((cache.shadow ++ simulatorReviewPacket stage record) ++
      [.wrote stage virtualBit virtualSerial]) stage = virtualSerial := by
    simp only [historyWriteSerial, historyWrite_append_wrote_same, Option.map_some, Option.getD_some]
  have hdup : record.decision.getD virtualBit = virtualBit := by
    dsimp only [virtualBit]
    cases record.decision <;> rfl
  have hshadowEq : (simulatorStep draw seed (simulatorStep draw seed cache (.wrote stage bit serial)) (.report stage truth serial)).shadow =
      (((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) ++
        [.report stage (Bool.xor truth (Bool.xor virtualBit bit)) virtualSerial]) := by
    simp only [simulatorStep, simulatorAppend, Function.update_self, Option.getD_some]
    simp only [← List.append_assoc]
    change (((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) ++
      [.report stage (Bool.xor truth (Bool.xor (record.decision.getD
        ((historyWritten ((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) stage).getD false))
        ((historyWritten (cache.seen ++ [.wrote stage bit serial]) stage).getD false)))
        (historyWriteSerial ((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) stage)]) = _
    rw [hshadow, hseen, hserial]
    simp only [Option.getD_some, hdup]
  dsimp only
  rw [simulatorStep_seen, simulatorStep_seen, hshadowEq]
  exact historyHandleTransport_writeReport h stage bit virtualBit truth serial virtualSerial record

theorem simulatorReplay_append_handleTransport_nonwrite {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (event : VisibleEvent I)
    (h : HistoryHandleTransport history (simulatorReplay draw seed history).shadow)
    (hw : ∀ stage, eventWrite stage event = none) (hr : ∀ stage, eventReport stage event = none) :
    HistoryHandleTransport (history ++ [event]) (simulatorReplay draw seed (history ++ [event])).shadow := by
  have hi : HistoryHandleTransport (simulatorReplay draw seed history).seen (simulatorReplay draw seed history).shadow := by
    simpa only [simulatorReplay_seen] using h
  have hn := simulatorStep_handleTransport_nonwrite draw seed (simulatorReplay draw seed history) event hi hw hr
  rw [simulatorStep_seen, simulatorReplay_seen] at hn
  simpa only [simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil] using hn

/-- Closed concrete-fold invariant on EVERY real early-report Native Prefix.
No input handle-transport or simulator-performance assumption remains. -/
theorem simulatorReplay_validHandle_prefix {SimSeed : Type*} {SourceSeed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I SourceSeed) (sourceSeed : SourceSeed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source sourceSeed truth tapes n s)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (seed : SimSeed) :
    HistoryHandleTransport s.history (simulatorReplay draw seed s.history).shadow := by
  induction hp with
  | initial =>
    intro handle hv
    simp only [initial, simulatorReplay_shadow_empty, historyValidHandle, historyReport,
      List.filterMap_nil, List.getLast?_nil] at hv
  | @next n before after hp hs ih =>
    generalize haction : source sourceSeed before.history = action at hs
    cases hs with
    | write stage bit live port resources =>
      have hi : HistoryHandleTransport (simulatorReplay draw seed before.history).seen
          (simulatorReplay draw seed before.history).shadow := by
        simpa only [simulatorReplay_seen] using ih
      have hn := simulatorStep_writeReport_handles draw seed (simulatorReplay draw seed before.history) hi stage bit (before.ledger.truth stage) before.clock
      dsimp only at hn
      rw [simulatorStep_seen, simulatorStep_seen, simulatorReplay_seen] at hn
      simpa only [record, writeResponses, hearly, ↓reduceIte, writeLedger, List.singleton_append,
        simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc,
        List.singleton_append] using hn
    | review stage live port resources =>
      exact simulatorReplay_append_handleTransport_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | allocate handle tool active valid compatible unused unallocated window resources =>
      exact simulatorReplay_append_handleTransport_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      exact simulatorReplay_append_handleTransport_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | advance stage live written resources =>
      exact simulatorReplay_append_handleTransport_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | stop active => exact simulatorReplay_append_handleTransport_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | abandon active => exact simulatorReplay_append_handleTransport_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)




/-- The exact hvalid interface for the concrete simulator shadow follows
from the closed Prefix induction, with no separate hvalid assumption. -/
theorem simulatorShadow_validHandle_prefix
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type*} [MeasurableSpace SourceSeed]
    (source : PolicyRule P.sharedInstance SourceSeed)
    (actualRule : PolicyRule P.sharedInstance (SimulatorSeed P SourceSeed))
    (seed : SimulatorSeed P SourceSeed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val mode accounting actualRule seed truth tapes n s) :
    ∀ handle : MismatchHandle P.sharedInstance,
      historyValidHandle (simulatorShadow P fee hfee source seed s.history) handle →
        historyValidHandle s.history (reserialHandle s.history handle) := by
  have h := simulatorReplay_validHandle_prefix (P.input fee hfee) C.val C.property.1.1 mode accounting
    actualRule seed truth tapes hp (simulatorSeedDraw P fee hfee source) seed
  simpa only [HistoryHandleTransport, simulatorShadow] using h

/-- In particular every reachable active or halted prefix of the ACTUAL
legal simulator Policy has the required virtual-to-real genuine handle map. -/
theorem simulatorPolicy_validHandle_prefix
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type*} [MeasurableSpace SourceSeed]
    (source : Policy (P.input fee hfee) C.val .uncapped accounting SourceSeed)
    (seed : SimulatorSeed P SourceSeed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting
      (simulatorPolicy P fee hfee C accounting source).rule seed truth tapes n s) :
    ∀ handle : MismatchHandle P.sharedInstance,
      historyValidHandle (simulatorShadow P fee hfee source.rule seed s.history) handle →
        historyValidHandle s.history (reserialHandle s.history handle) :=
  simulatorShadow_validHandle_prefix P fee hfee C .uncapped accounting source.rule
    (simulatorPolicy P fee hfee C accounting source).rule seed truth tapes hp

end PDROC
