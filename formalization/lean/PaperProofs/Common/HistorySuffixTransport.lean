module

public import PaperProofs.Common.HistorySuffixReplay
import Lean.Elab.Tactic.Omega

/-!
System-side response transport for B09. The next-response packet below is
computed from the real native state and real system tape, never supplied to a
controller. Its correspondence theorem is a component of the full run relation.
-/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance}

/-- The actual early-report response to an action. This function does not
claim legality: a real `Step` separately supplies that fact. -/
def responsePacket (input : StatisticalInput I) (tapes : ReviewTapes input)
    (s : State I) : Action I → SuffixPacket I
  | .review stage => .review stage (tapes stage (s.ledger.reviews stage).toNat).val
  | .write stage bit => .write stage bit (s.ledger.truth stage) s.clock
  | .allocate handle tool => .allocate handle tool
  | .execute handle tool => .execute handle tool
  | .advance stage => .advance stage
  | .stop => .stop
  | .abandon => .abandon

@[simp] theorem responsePacket_action (input : StatisticalInput I) (tapes : ReviewTapes input)
    (s : State I) (action : Action I) : (responsePacket input tapes s action).action = action := by
  cases action <;> rfl

/-- Exact history identity for every real early native step, including
deferred executions, stopping and failed paths. -/
theorem step_history_responsePacket (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {s next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes s action next) :
    next.history = s.history ++ (responsePacket input tapes s action).events := by
  cases hs <;> try rfl
  simp only [record, responsePacket, SuffixPacket.events, writeResponses,
    hearly, ↓reduceIte, writeLedger, List.singleton_append]

/-- The same real step updates the original public cache by precisely its
canonical response. No next-state or packet oracle is added to the policy. -/
theorem step_publicStartup_responsePacket (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {s next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes s action next) :
    applySuffixPacketPublic accounting (publicStartup s) action (responsePacket input tapes s action) =
      some (publicStartup next) := by
  cases hs with
  | review stage live port resources => exact congrArg some (publicStartup_review accounting s stage _).symm
  | write stage bit live port resources => exact congrArg some (publicStartup_write_early C hearly accounting s stage bit).symm
  | allocate handle tool active valid compatible unused unallocated window resources =>
    exact congrArg some (publicStartup_allocate accounting s handle tool).symm
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    exact congrArg some (publicStartup_execute accounting s handle tool).symm
  | advance stage live written resources => exact congrArg some (publicStartup_advance accounting s stage).symm
  | stop active => exact congrArg some (publicStartup_stop s false).symm
  | abandon active => exact congrArg some (publicStartup_stop s true).symm

/-- Exact correspondence of the next real system response under dynamic
serial rebinding. The only response premises are the actual future truth and
the actual next review letter, which are maintained by the run invariant.
There is no premise equating the response packets. -/
theorem responsePacket_lower (input : StatisticalInput I) (first : ℕ)
    (sourceTapes : ReviewTapes input) (targetTapes : ReviewTapes (input.freshSuffix first))
    (source : State I) (target : State (I.freshSuffix first))
    (sourceAction : Action I) (targetAction : Action (I.freshSuffix first))
    (haction : suffixActionOf first target.history sourceAction = some targetAction)
    (htruth : ∀ stage (hf : first ≤ stage.val),
      target.ledger.truth (suffixStageOf first stage hf) = source.ledger.truth stage)
    (hletter : ∀ stage (hf : first ≤ stage.val),
      (targetTapes (suffixStageOf first stage hf)
        (target.ledger.reviews (suffixStageOf first stage hf)).toNat).val =
      (sourceTapes stage (source.ledger.reviews stage).toNat).val) :
    (responsePacket input sourceTapes source sourceAction).lower first target.clock target.history =
      some (responsePacket (input.freshSuffix first) targetTapes target targetAction) := by
  cases sourceAction <;> simp only [suffixActionOf] at haction
  all_goals try split at haction
  all_goals try cases haction
  all_goals simp_all only [responsePacket, SuffixPacket.lower, ↓reduceDIte]

/-- Restriction retains the same hidden truth at every lifted stage. This
is an operational world identity, independent of any conditional law. -/
theorem restrictFreshWorld_truth (input : StatisticalInput I) (first : ℕ) (world : input.World)
    (stage : (I.freshSuffix first).Stage) :
    (input.freshSuffix first).truthAt (input.restrictFreshWorld first world) stage =
      input.truthAt world (I.freshStageLift first stage) := by
  cases first with
  | zero =>
    change (world stage).1 = (world (I.freshStageLift 0 stage)).1
    have he : I.freshStageLift 0 stage = stage := by apply Fin.ext; simp only [Instance.freshStageLift, Nat.zero_add]
    rw [he]
  | succ first => rfl

/-- Every potential suffix review symbol is exactly the corresponding
original symbol. Neither side samples a second tape. -/
theorem restrictFreshWorld_letter (input : StatisticalInput I) (first : ℕ) (world : input.World)
    (stage : (I.freshSuffix first).Stage) (k : ℕ) :
    (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first world) stage k).val =
      (worldTapes input world (I.freshStageLift first stage) k).val := by
  cases first with
  | zero =>
    change ((world stage).2 k).val = ((world (I.freshStageLift 0 stage)).2 k).val
    have he : I.freshStageLift 0 stage = stage := by apply Fin.ext; simp only [Instance.freshStageLift, Nat.zero_add]
    exact congrArg (fun st : I.Stage => ((world st).2 k).val) he.symm
  | succ first => rfl

/-- Once the genuine review counts agree, real world restriction gives the
entire next-response correspondence. No tape/response alignment is assumed. -/
theorem responsePacket_lower_world (input : StatisticalInput I) (first : ℕ) (world : input.World)
    (source : State I) (target : State (I.freshSuffix first))
    (sourceAction : Action I) (targetAction : Action (I.freshSuffix first))
    (haction : suffixActionOf first target.history sourceAction = some targetAction)
    (hsourceTruth : source.ledger.truth = input.truthAt world)
    (htargetTruth : target.ledger.truth =
      (input.freshSuffix first).truthAt (input.restrictFreshWorld first world))
    (hcounts : ∀ stage (hf : first ≤ stage.val),
      target.ledger.reviews (suffixStageOf first stage hf) = source.ledger.reviews stage) :
    (responsePacket input (worldTapes input world) source sourceAction).lower first target.clock target.history =
      some (responsePacket (input.freshSuffix first)
        (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first world)) target targetAction) := by
  apply responsePacket_lower input first _ _ source target sourceAction targetAction haction
  · intro stage hf
    rw [hsourceTruth, htargetTruth, restrictFreshWorld_truth, freshStageLift_suffixStageOf]
  · intro stage hf
    rw [hcounts, restrictFreshWorld_letter, freshStageLift_suffixStageOf]

/-- A REAL target next step supplies exactly the packet accepted by source
replay. This removes the previous open one-packet response-identification
obligation. The run induction must still establish the two states' review
counts and the accepted target action. -/
theorem replaySuffixPacket_real_target (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (first : ℕ) (rule : PolicyRule I Seed) (seed : Seed)
    (world : input.World) (cache : Startup I)
    (source sourceNext : State I) (target targetNext : State (I.freshSuffix first))
    (targetAction : Action (I.freshSuffix first))
    (hsettled : (settleOldExecutions first accounting rule (I.toolCount + 1) seed cache).1 = publicStartup source)
    (hactive : source.halted = false)
    (hsource : Step input C mode accounting (worldTapes input world) source (rule seed source.history) sourceNext)
    (htarget : Step (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first world)) target targetAction targetNext)
    (haction : suffixActionOf first target.history (rule seed source.history) = some targetAction)
    (hsourceTruth : source.ledger.truth = input.truthAt world)
    (htargetTruth : target.ledger.truth =
      (input.freshSuffix first).truthAt (input.restrictFreshWorld first world))
    (hcounts : ∀ stage (hf : first ≤ stage.val),
      target.ledger.reviews (suffixStageOf first stage hf) = source.ledger.reviews stage) :
    ∃ packet : SuffixPacket (I.freshSuffix first),
      targetNext.history = target.history ++ packet.events ∧
      replaySuffixPacket first accounting rule seed cache target.history packet = some (publicStartup sourceNext) := by
  let packet := responsePacket (input.freshSuffix first)
    (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first world)) target targetAction
  refine ⟨packet, step_history_responsePacket _ _ rfl _ _ _ htarget, ?_⟩
  have hlower := responsePacket_lower_world input first world source target (rule seed source.history) targetAction
    haction hsourceTruth htargetTruth hcounts
  have hup := applySuffixPacketPublic_lower accounting (publicStartup source) first target.clock target.history
    (responsePacket input (worldTapes input world) source (rule seed source.history)) packet hlower
  rw [responsePacket_action] at hup
  have hresponse := step_publicStartup_responsePacket input C hearly mode accounting _ hsource
  unfold replaySuffixPacket
  rw [hsettled]
  change (if source.halted then none else
    if suffixActionOf first target.history (rule seed source.history) = some packet.action then
      applySuffixPacketPublic accounting (publicStartup source) (rule seed source.history) packet else none) = _
  rw [hactive]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hpaction : packet.action = targetAction := responsePacket_action _ _ _ _
  rw [hpaction, haction]
  simp only [↓reduceIte]
  exact hup.trans hresponse

end PaperProofs.Common.Native
