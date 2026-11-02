module

public import PaperProofs.Retained.PRet_PaymentPrefix_021
public import PaperProofs.Retained.PRet_ShadowInitial_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetPaymentSelectors031

open Common Common.Native PRetDelayedPolicy010 PRetInformationPackets006
open PRetPublicAdministrativeReplay005 PRetShadowInitial012

variable {I : Instance}

theorem raw_payment {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (history : List (VisibleEvent I)) (startup : Startup I)
    (hshadow : shadow accounting source seed history = some startup)
    (hh : startup.halted = true) (hf : startup.finished = true) (ha : startup.abandoned = false)
    (hc : historyCursor history = I.stageCount) :
    raw accounting source seed history = paymentAction startup history := by
  simp only [raw, hshadow, candidate, hh, hf, ha, Bool.false_eq_true, ↓reduceIte,
    catchUp, hc, Nat.lt_irrefl]

theorem payment_allocate (startup : Startup I) (history : List (VisibleEvent I)) (execution : Execution I)
    (hn : startup.executions[(historyExecutions history).length]? = some execution)
    (hfind : (historyCommitments history).find? (fun pair => pair.1.stage == execution.handle.stage) = none) :
    paymentAction startup history = .allocate
      ⟨execution.handle.stage, historyWriteSerial history execution.handle.stage⟩ execution.tool := by
  simp only [paymentAction, hn, hfind]

theorem payment_execute (startup : Startup I) (history : List (VisibleEvent I)) (execution : Execution I)
    (pair : MismatchHandle I × I.Tool)
    (hn : startup.executions[(historyExecutions history).length]? = some execution)
    (hfind : (historyCommitments history).find? (fun pair => pair.1.stage == execution.handle.stage) = some pair)
    (htool : pair.2 = execution.tool) :
    paymentAction startup history = .execute
      ⟨execution.handle.stage, historyWriteSerial history execution.handle.stage⟩ execution.tool := by
  simp only [paymentAction, hn, hfind, htool, ↓reduceIte]

theorem step_silent_information (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) {before next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes before action next) (ha : silentAction action = true) :
    informationTrace next.history = informationTrace before.history := by
  cases hs <;> simp_all [silentAction, record, stopState, informationTrace, informationEvent,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil]

theorem step_silent_shadow {Seed : Type*} (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (seed : Seed) (tapes : ReviewTapes input)
    {before next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes before action next) (ha : silentAction action = true) :
    shadow accounting source seed next.history = shadow accounting source seed before.history :=
  shadow_congr accounting source seed next.history before.history
    (step_silent_information input C mode accounting tapes hs ha)

end PaperProofs.Retained.PRetPaymentSelectors031
