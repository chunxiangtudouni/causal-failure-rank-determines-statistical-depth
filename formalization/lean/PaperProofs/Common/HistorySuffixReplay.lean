module

public import PaperProofs.Common.HistorySuffixController
public import PaperProofs.Common.HistorySuffixWorld
import Lean.Elab.Tactic.Omega

/-!
B09 implementation workpad. Past/fresh-world splitting below is analysis
data only. The executable replay reads the original seed, the public startup,
and the REAL suffix response packets. It never receives the future world.
Old pending executions are simulated before the next packet without releasing
their tools. New suffix commitments may execute later; no current-cursor
execution guard from the reference controller is reused.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

abbrev PastWorldAt (input : StatisticalInput I) (first : ℕ) :=
  ∀ i : {i : I.Stage // i.val < first}, input.StageSample i.val

def pastViewAt (input : StatisticalInput I) (first : ℕ) (world : input.World) : PastWorldAt input first :=
  fun i => world i.val

theorem measurable_pastViewAt (input : StatisticalInput I) (first : ℕ) :
    Measurable (pastViewAt input first) := measurable_pi_iff.mpr fun i => measurable_pi_apply i.val

@[simp] theorem suffixStageOf_freshStageLift (first : ℕ) (stage : (I.freshSuffix first).Stage)
    (hf : first ≤ (I.freshStageLift first stage).val) :
    suffixStageOf first (I.freshStageLift first stage) hf = stage := by
  apply Fin.ext
  change (first + stage.val) - first = stage.val
  omega

private theorem measurable_stageSampleCast (input : StatisticalInput I) (left right : I.Stage)
    (heq : left = right) : Measurable (Eq.mp (congrArg input.StageSample heq)) := by
  subst right
  exact measurable_id

private theorem stageSampleCast_apply (input : StatisticalInput I) (world : input.World)
    (left right : I.Stage) (heq : left = right) :
    Eq.mp (congrArg input.StageSample heq) (world left) = world right := by
  subst right
  rfl

private theorem freshSampleCast_apply (input : StatisticalInput I) (first : ℕ)
    (left right : (I.freshSuffix (first + 1)).Stage) (heq : left = right)
    (fresh : (input.freshSuffix (first + 1)).World) :
    Eq.mp (congrArg input.StageSample (congrArg (I.freshStageLift (first + 1)) heq))
      (fresh left) = fresh right := by
  subst right
  rfl

/-- Join independently supplied OLD data and the complete new fresh world.
The whole first=0 branch is the identity, avoiding any experiment/port change. -/
def joinPastFresh (input : StatisticalInput I) :
    (first : ℕ) → PastWorldAt input first → (input.freshSuffix first).World → input.World
  | 0 => fun _ fresh => fresh
  | first + 1 => fun past fresh stage =>
      if hp : stage.val < first + 1 then past ⟨stage, hp⟩ else
        let hf : first + 1 ≤ stage.val := Nat.le_of_not_gt hp
        Eq.mp (congrArg input.StageSample (freshStageLift_suffixStageOf (first + 1) stage hf))
          (fresh (suffixStageOf (first + 1) stage hf))

theorem measurable_joinPastFresh (input : StatisticalInput I) (first : ℕ) :
    Measurable (fun pair : PastWorldAt input first × (input.freshSuffix first).World =>
      joinPastFresh input first pair.1 pair.2) := by
  cases first with
  | zero => exact measurable_snd
  | succ first =>
    apply measurable_pi_iff.mpr
    intro stage
    by_cases hp : stage.val < first + 1
    · change Measurable (fun pair : PastWorldAt input (first + 1) × (input.freshSuffix (first + 1)).World =>
        (joinPastFresh input (first + 1) pair.1 pair.2) stage)
      simp only [joinPastFresh, hp, ↓reduceDIte]
      exact (measurable_pi_apply (⟨stage, hp⟩ : {i : I.Stage // i.val < first + 1})).comp measurable_fst
    · let hf : first + 1 ≤ stage.val := Nat.le_of_not_gt hp
      simp only [joinPastFresh, hp, ↓reduceDIte]
      apply (measurable_stageSampleCast input _ _
        (freshStageLift_suffixStageOf (first + 1) stage hf)).comp
      change Measurable (fun pair : PastWorldAt input (first + 1) × (input.freshSuffix (first + 1)).World =>
        pair.2 (suffixStageOf (first + 1) stage hf))
      exact (measurable_pi_apply (suffixStageOf (first + 1) stage hf)).comp measurable_snd

theorem joinPastFresh_split (input : StatisticalInput I) (first : ℕ) (world : input.World) :
    joinPastFresh input first (pastViewAt input first world) (input.restrictFreshWorld first world) = world := by
  cases first with
  | zero => rfl
  | succ first =>
    funext stage
    by_cases hp : stage.val < first + 1
    · simp only [joinPastFresh, hp, ↓reduceDIte, pastViewAt]
    · simp only [joinPastFresh, hp, ↓reduceDIte, StatisticalInput.restrictFreshWorld]
      exact stageSampleCast_apply input world _ stage
        (freshStageLift_suffixStageOf (first + 1) stage (Nat.le_of_not_gt hp))

theorem pastViewAt_joinPastFresh (input : StatisticalInput I) (first : ℕ)
    (past : PastWorldAt input first) (fresh : (input.freshSuffix first).World) :
    pastViewAt input first (joinPastFresh input first past fresh) = past := by
  funext stage
  cases first with
  | zero => exact (Nat.not_lt_zero _ stage.property).elim
  | succ first => simp only [pastViewAt, joinPastFresh, stage.property, ↓reduceDIte]

theorem restrictFreshWorld_joinPastFresh (input : StatisticalInput I) (first : ℕ)
    (past : PastWorldAt input first) (fresh : (input.freshSuffix first).World) :
    input.restrictFreshWorld first (joinPastFresh input first past fresh) = fresh := by
  cases first with
  | zero => rfl
  | succ first =>
    funext stage
    have hn : ¬ (I.freshStageLift (first + 1) stage).val < first + 1 := by
      change ¬ first + 1 + stage.val < first + 1
      omega
    simp only [StatisticalInput.restrictFreshWorld, joinPastFresh, hn, ↓reduceDIte]
    exact freshSampleCast_apply input first _ stage
      (suffixStageOf_freshStageLift (first + 1) stage (Nat.le_of_not_gt hn)) fresh

theorem pastViewAt_independent_fresh (input : StatisticalInput I) (first : ℕ) :
    IndepFun (pastViewAt input first) (input.restrictFreshWorld first) input.worldLaw := by
  have hd : Disjoint {i : I.Stage | i.val < first} {i : I.Stage | first ≤ i.val} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact Nat.not_lt_of_ge hj hi
  have h := (input.worldLaw_independent_stages).indepFun_set
    {i : I.Stage | i.val < first} {i : I.Stage | first ≤ i.val} hd (fun i => measurable_pi_apply i)
  have hc := h.comp measurable_id (measurable_renumberFutureWorld input first)
  have heq : input.restrictFreshWorld first =
      renumberFutureWorld input first ∘ (fun world : input.World =>
        fun i : {i : I.Stage // first ≤ i.val} => world i.val) := by
    funext world
    exact restrictFreshWorld_eq_renumberFutureWorld input first world
  rw [heq]
  exact hc

section SeedSplit

variable {Seed : Type*} [MeasurableSpace Seed]

def splitPastFreshSample (input : StatisticalInput I) (first : ℕ) (sample : Seed × input.World) :
    (Seed × PastWorldAt input first) × (input.freshSuffix first).World :=
  ((sample.1, pastViewAt input first sample.2), input.restrictFreshWorld first sample.2)

def joinPastFreshSample (input : StatisticalInput I) (first : ℕ)
    (sample : (Seed × PastWorldAt input first) × (input.freshSuffix first).World) : Seed × input.World :=
  (sample.1.1, joinPastFresh input first sample.1.2 sample.2)

theorem measurable_splitPastFreshSample (input : StatisticalInput I) (first : ℕ) :
    Measurable (splitPastFreshSample (Seed := Seed) input first) :=
  (measurable_fst.prodMk ((measurable_pastViewAt input first).comp measurable_snd)).prodMk
    ((input.measurable_restrictFreshWorld first).comp measurable_snd)

theorem measurable_joinPastFreshSample (input : StatisticalInput I) (first : ℕ) :
    Measurable (joinPastFreshSample (Seed := Seed) input first) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_joinPastFresh input first).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

omit [MeasurableSpace Seed] in
theorem joinPastFreshSample_split (input : StatisticalInput I) (first : ℕ) (sample : Seed × input.World) :
    joinPastFreshSample input first (splitPastFreshSample input first sample) = sample := by
  exact Prod.ext rfl (joinPastFresh_split input first sample.2)

omit [MeasurableSpace Seed] in
theorem splitPastFreshSample_join (input : StatisticalInput I) (first : ℕ)
    (sample : (Seed × PastWorldAt input first) × (input.freshSuffix first).World) :
    splitPastFreshSample input first (joinPastFreshSample input first sample) = sample := by
  rcases sample with ⟨⟨seed, past⟩, fresh⟩
  exact Prod.ext (Prod.ext rfl (pastViewAt_joinPastFresh input first past fresh))
    (restrictFreshWorld_joinPastFresh input first past fresh)

/-- The NEW private seed is (old seed, OLD world), independent of the fresh
truth/tapes. Its whole joint law is proved, not postulated as a Markov input. -/
theorem splitPastFreshSample_law (input : StatisticalInput I) (first : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (input.seededWorldLaw ν).map (splitPastFreshSample input first) =
      (ν.prod (input.worldLaw.map (pastViewAt input first))).prod (input.freshSuffix first).worldLaw := by
  have hp := measurable_pastViewAt input first
  have hf := input.measurable_restrictFreshWorld first
  have hw : input.worldLaw.map (fun world => (pastViewAt input first world, input.restrictFreshWorld first world)) =
      (input.worldLaw.map (pastViewAt input first)).prod (input.freshSuffix first).worldLaw := by
    rw [(pastViewAt_independent_fresh input first).map_prod_eq_prod_map_map hp.aemeasurable hf.aemeasurable,
      input.restrictFreshWorld_worldLaw first]
  have hs : (input.seededWorldLaw ν).map (fun sample =>
      (sample.1, (pastViewAt input first sample.2, input.restrictFreshWorld first sample.2))) =
      ν.prod ((input.worldLaw.map (pastViewAt input first)).prod (input.freshSuffix first).worldLaw) := by
    rw [← hw]
    exact (Measure.map_prod_map ν input.worldLaw measurable_id (hp.prodMk hf)).symm.trans
      (by rw [Measure.map_id])
  apply (MeasurableEquiv.prodAssoc :
    (Seed × PastWorldAt input first) × (input.freshSuffix first).World ≃ᵐ
      Seed × PastWorldAt input first × (input.freshSuffix first).World).map_measurableEquiv_injective
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable (measurable_splitPastFreshSample input first),
    Measure.prodAssoc_prod]
  exact hs

theorem joinPastFreshSample_law (input : StatisticalInput I) (first : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ((ν.prod (input.worldLaw.map (pastViewAt input first))).prod (input.freshSuffix first).worldLaw).map
      (joinPastFreshSample input first) = input.seededWorldLaw ν := by
  rw [← splitPastFreshSample_law input first ν,
    Measure.map_map (measurable_joinPastFreshSample input first) (measurable_splitPastFreshSample input first)]
  have heq : joinPastFreshSample (Seed := Seed) input first ∘ splitPastFreshSample input first = id :=
    funext (joinPastFreshSample_split input first)
  rw [heq, Measure.map_id]

theorem lintegral_joinPastFreshSample (input : StatisticalInput I) (first : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (f : Seed × input.World → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample, f (joinPastFreshSample input first sample)
      ∂(ν.prod (input.worldLaw.map (pastViewAt input first))).prod (input.freshSuffix first).worldLaw) =
      ∫⁻ sample, f sample ∂input.seededWorldLaw ν := by
  rw [← joinPastFreshSample_law input first ν]
  exact (lintegral_map hf (measurable_joinPastFreshSample input first)).symm

end SeedSplit

/-! Public effects, then the actual atomic response-packet decoder. -/

def Startup.reviewPublic (accounting : NormalAccounting I) (startup : Startup I)
    (stage : I.Stage) (symbol : ℕ) : Startup I :=
  { startup with
    reviews := Function.update startup.reviews stage (startup.reviews stage + 1)
    normalCalls := startup.normalCalls + accounting startup.history (.review stage) [.observation stage symbol]
    clock := startup.clock + 1
    history := startup.history ++ [.observation stage symbol]
    halted := false }

/-- The report bit is a real response argument. The write serial and report
time both use the settled ORIGINAL clock, not the suffix packet's clock. -/
def Startup.writePublic (accounting : NormalAccounting I) (startup : Startup I)
    (stage : I.Stage) (bit truth : Bool) : Startup I :=
  let responses := [.wrote stage bit startup.clock, .report stage truth startup.clock]
  { startup with
    written := Function.update startup.written stage (some bit)
    writeSerial := Function.update startup.writeSerial stage startup.clock
    reportTime := Function.update startup.reportTime stage (some startup.clock)
    normalCalls := startup.normalCalls + accounting startup.history (.write stage bit) responses
    clock := startup.clock + 1
    history := startup.history ++ responses
    halted := false }

def Startup.allocatePublic (accounting : NormalAccounting I) (startup : Startup I)
    (handle : MismatchHandle I) (tool : I.Tool) : Startup I :=
  { startup with
    commitments := startup.commitments ++ [⟨handle, tool, startup.clock⟩]
    normalCalls := startup.normalCalls + accounting startup.history (.allocate handle tool) [.committed handle tool]
    clock := startup.clock + 1
    history := startup.history ++ [.committed handle tool]
    halted := false }

def Startup.advancePublic (accounting : NormalAccounting I) (startup : Startup I)
    (stage : I.Stage) : Startup I :=
  { startup with
    advanceTime := Function.update startup.advanceTime stage (some startup.clock)
    normalCalls := startup.normalCalls + accounting startup.history (.advance stage) [.advanced stage]
    cursor := startup.cursor + 1
    clock := startup.clock + 1
    history := startup.history ++ [.advanced stage]
    halted := false }

noncomputable def Startup.stopPublic (startup : Startup I) (abandon : Bool) : Startup I := by
  classical
  exact { startup with
    finished := @decide (∀ stage, startup.written stage ≠ none) (Classical.propDecidable _)
    abandoned := abandon
    clock := startup.clock + 1
    history := startup.history ++ [if abandon then .abandoned else .stopped]
    halted := true }

theorem publicStartup_review (accounting : NormalAccounting I) (s : State I)
    (stage : I.Stage) (symbol : ℕ) :
    publicStartup (record accounting s (.review stage) [.observation stage symbol]
      (reviewLedger s stage) s.cursor false) =
      (publicStartup s).reviewPublic accounting stage symbol := rfl

theorem publicStartup_write_early (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (s : State I) (stage : I.Stage) (bit : Bool) :
    publicStartup (record accounting s (.write stage bit) (writeResponses C s stage bit)
      (reportedWriteLedger C s stage bit) s.cursor false) =
      (publicStartup s).writePublic accounting stage bit (s.ledger.truth stage) := by
  simp only [writeResponses, reportedWriteLedger, hearly, ite_true]
  rfl

theorem publicStartup_allocate (accounting : NormalAccounting I) (s : State I)
    (handle : MismatchHandle I) (tool : I.Tool) :
    publicStartup (record accounting s (.allocate handle tool) [.committed handle tool]
      (allocateLedger s handle tool) s.cursor false) =
      (publicStartup s).allocatePublic accounting handle tool := rfl

theorem publicStartup_advance (accounting : NormalAccounting I) (s : State I) (stage : I.Stage) :
    publicStartup (record accounting s (.advance stage) [.advanced stage]
      (advanceLedger s stage) (s.cursor + 1) false) =
      (publicStartup s).advancePublic accounting stage := rfl

theorem publicStartup_stop (s : State I) (abandon : Bool) :
    publicStartup (stopState s abandon) = (publicStartup s).stopPublic abandon := by
  classical
  simp only [stopState, Startup.stopPublic, publicStartup, allWritten]
  rfl

inductive SuffixPacket (J : Instance) where
  | review (stage : J.Stage) (symbol : ℕ)
  | write (stage : J.Stage) (bit truth : Bool) (serial : ℕ)
  | allocate (handle : MismatchHandle J) (tool : J.Tool)
  | execute (handle : MismatchHandle J) (tool : J.Tool)
  | advance (stage : J.Stage)
  | stop
  | abandon
  deriving DecidableEq, Countable

def SuffixPacket.action {J : Instance} : SuffixPacket J → Action J
  | .review stage _ => .review stage
  | .write stage bit _ _ => .write stage bit
  | .allocate handle tool => .allocate handle tool
  | .execute handle tool => .execute handle tool
  | .advance stage => .advance stage
  | .stop => .stop
  | .abandon => .abandon

def SuffixPacket.events {J : Instance} : SuffixPacket J → List (VisibleEvent J)
  | .review stage symbol => [.observation stage symbol]
  | .write stage bit truth serial => [.wrote stage bit serial, .report stage truth serial]
  | .allocate handle tool => [.committed handle tool]
  | .execute handle tool => [.executed handle tool]
  | .advance stage => [.advanced stage]
  | .stop => [.stopped]
  | .abandon => [.abandoned]

theorem SuffixPacket.historyActions {J : Instance} (packet : SuffixPacket J) :
    historyActions packet.events = [packet.action] := by cases packet <;> rfl

/-- Parse actual early response packets. Standalone reports and partial or
inconsistent wrote/report pairs are rejected, rather than exposed as states. -/
def parseSuffixPackets {J : Instance} : List (VisibleEvent J) → Option (List (SuffixPacket J))
  | [] => some []
  | .observation stage symbol :: rest => (parseSuffixPackets rest).map (.review stage symbol :: ·)
  | .wrote stage bit serial :: .report other truth otherSerial :: rest =>
      if stage = other ∧ serial = otherSerial then
        (parseSuffixPackets rest).map (.write stage bit truth serial :: ·) else none
  | .committed handle tool :: rest => (parseSuffixPackets rest).map (.allocate handle tool :: ·)
  | .executed handle tool :: rest => (parseSuffixPackets rest).map (.execute handle tool :: ·)
  | .advanced stage :: rest => (parseSuffixPackets rest).map (.advance stage :: ·)
  | .stopped :: rest => (parseSuffixPackets rest).map (.stop :: ·)
  | .abandoned :: rest => (parseSuffixPackets rest).map (.abandon :: ·)
  | _ => none

theorem parseSuffixPackets_packet_cons {J : Instance} (packet : SuffixPacket J)
    (rest : List (VisibleEvent J)) :
    parseSuffixPackets (packet.events ++ rest) =
      (parseSuffixPackets rest).map (packet :: ·) := by
  cases packet <;> simp only [SuffixPacket.events, List.cons_append, List.nil_append, parseSuffixPackets,
    true_and, ite_true]

theorem parseSuffixPackets_packets {J : Instance} (packets : List (SuffixPacket J)) :
    parseSuffixPackets (packets.flatMap SuffixPacket.events) = some packets := by
  induction packets with
  | nil => rfl
  | cons packet rest ih =>
    rw [List.flatMap_cons, parseSuffixPackets_packet_cons, ih]
    rfl

/-- Apply a source action to public data using the returned packet's visible
symbol/report. Source handles are kept, including their ORIGINAL serials. -/
noncomputable def applySuffixPacketPublic {J : Instance} (accounting : NormalAccounting I)
    (startup : Startup I) : Action I → SuffixPacket J → Option (Startup I)
  | .review stage, .review _ symbol => some (startup.reviewPublic accounting stage symbol)
  | .write stage bit, .write _ _ truth _ => some (startup.writePublic accounting stage bit truth)
  | .allocate handle tool, .allocate _ _ => some (startup.allocatePublic accounting handle tool)
  | .execute handle tool, .execute _ _ => some (startup.executePublic accounting handle tool)
  | .advance stage, .advance _ => some (startup.advancePublic accounting stage)
  | .stop, .stop => some (startup.stopPublic false)
  | .abandon, .abandon => some (startup.stopPublic true)
  | _, _ => none

/-- Exactly one real suffix response packet, after all selected old pending
executions. The visible action check includes dynamic suffix serial rebinding. -/
noncomputable def replaySuffixPacket {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (startup : Startup I)
    (before : List (VisibleEvent (I.freshSuffix first))) (packet : SuffixPacket (I.freshSuffix first)) :
    Option (Startup I) :=
  let settled := (settleOldExecutions first accounting rule (I.toolCount + 1) seed startup).1
  let action := rule seed settled.history
  if settled.halted then none else
    if suffixActionOf first before action = some packet.action then
      applySuffixPacketPublic accounting settled action packet else none

noncomputable def replaySuffixPackets {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) : Startup I → List (VisibleEvent (I.freshSuffix first)) →
      List (SuffixPacket (I.freshSuffix first)) → Option (Startup I)
  | startup, _, [] => some startup
  | startup, before, packet :: rest =>
      (replaySuffixPacket first accounting rule seed startup before packet).bind fun next =>
        replaySuffixPackets first accounting rule seed next (before ++ packet.events) rest

noncomputable def replaySuffixHistory {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (startup : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first))) : Option (Startup I) :=
  (parseSuffixPackets history).bind (replaySuffixPackets first accounting rule seed startup [])

theorem replaySuffixPackets_append {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (startup : Startup I)
    (before : List (VisibleEvent (I.freshSuffix first)))
    (left right : List (SuffixPacket (I.freshSuffix first))) :
    replaySuffixPackets first accounting rule seed startup before (left ++ right) =
      (replaySuffixPackets first accounting rule seed startup before left).bind fun next =>
        replaySuffixPackets first accounting rule seed next (before ++ left.flatMap SuffixPacket.events) right := by
  induction left generalizing startup before with
  | nil => simp only [List.nil_append, replaySuffixPackets, List.flatMap_nil, List.append_nil, Option.bind_some]
  | cons packet rest ih =>
    simp only [List.cons_append, replaySuffixPackets, ih, Option.bind_assoc,
      List.flatMap_cons, List.append_assoc]

theorem replaySuffixHistory_packets {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (startup : Startup I)
    (packets : List (SuffixPacket (I.freshSuffix first))) :
    replaySuffixHistory first accounting rule seed startup (packets.flatMap SuffixPacket.events) =
      replaySuffixPackets first accounting rule seed startup [] packets := by
  rw [replaySuffixHistory, parseSuffixPackets_packets]
  rfl

section ReplayMeasurable

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_replaySuffixPacket (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hrule : MeasurableRule rule)
    (before : List (VisibleEvent (I.freshSuffix first))) (packet : SuffixPacket (I.freshSuffix first)) :
    Measurable (fun sample : Seed × Startup I =>
      replaySuffixPacket first accounting rule sample.1 sample.2 before packet) := by
  let cache : Seed × Startup I → Startup I := fun sample =>
    (settleOldExecutions first accounting rule (I.toolCount + 1) sample.1 sample.2).1
  have hc : Measurable cache :=
    (measurable_settleOldExecutions first accounting rule hrule (I.toolCount + 1)).fst
  have hh : Measurable (fun sample => (cache sample).history) :=
    (measurable_of_countable (fun startup : Startup I => startup.history)).comp hc
  have ha : Measurable (fun sample => rule sample.1 (cache sample).history) :=
    hrule.comp (measurable_fst.prodMk hh)
  exact (measurable_of_countable (fun pair : Startup I × Action I =>
    if pair.1.halted then none else
      if suffixActionOf first before pair.2 = some packet.action then
        applySuffixPacketPublic accounting pair.1 pair.2 packet else none)).comp (hc.prodMk ha)

theorem measurable_replaySuffixPackets (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hrule : MeasurableRule rule)
    (before : List (VisibleEvent (I.freshSuffix first))) (packets : List (SuffixPacket (I.freshSuffix first))) :
    Measurable (fun sample : Seed × Startup I =>
      replaySuffixPackets first accounting rule sample.1 sample.2 before packets) := by
  induction packets generalizing before with
  | nil => exact (measurable_of_countable (fun startup : Startup I => some startup)).comp measurable_snd
  | cons packet rest ih =>
    have ht : Measurable (fun pair : Seed × Option (Startup I) =>
        pair.2.bind fun next =>
          replaySuffixPackets first accounting rule pair.1 next (before ++ packet.events) rest) := by
      apply measurable_from_prod_countable_left
      intro next
      cases next with
      | none => exact measurable_const
      | some next => exact (ih (before ++ packet.events)).comp (measurable_id.prodMk measurable_const)
    exact ht.comp (measurable_fst.prodMk
      (measurable_replaySuffixPacket first accounting rule hrule before packet))

theorem measurable_replaySuffixHistory (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) :
    Measurable (fun sample : (Seed × Startup I) × List (VisibleEvent (I.freshSuffix first)) =>
      replaySuffixHistory first accounting rule sample.1.1 sample.1.2 sample.2) := by
  apply measurable_from_prod_countable_left
  intro history
  cases hp : parseSuffixPackets history with
  | none => simp only [replaySuffixHistory, hp, Option.bind_none]; exact measurable_const
  | some packets =>
    simpa only [replaySuffixHistory, hp, Option.bind_some] using
      measurable_replaySuffixPackets first accounting rule hrule [] packets

end ReplayMeasurable

/-! The guard is for DEFERRED execution. In particular it does not assert
cursor=handle.stage on an execute action. This applies to new suffix
commitments too, not merely to the old obligations simulated internally. -/

def replayValidHandle (history : List (VisibleEvent I)) (handle : MismatchHandle I) : Prop :=
  match historyReport history handle.stage with
  | none => False
  | some (truth, serial) => historyWritten history handle.stage = some (!truth) ∧
      handle.writeSerial = serial ∧ historyWriteSerial history handle.stage = handle.writeSerial

instance replayValidHandle_decidable (history : List (VisibleEvent I)) (handle : MismatchHandle I) :
    Decidable (replayValidHandle history handle) := by
  unfold replayValidHandle
  cases historyReport history handle.stage <;> infer_instance

def replayAllowsAction (available : Finset I.Tool) (history : List (VisibleEvent I)) : Action I → Prop
  | .review stage | .write stage _ => historyCursor history = stage.val ∧ historyWritten history stage = none
  | .advance stage => historyCursor history = stage.val ∧ historyWritten history stage ≠ none
  | .allocate handle tool => tool ∈ available ∧ historyCursor history = handle.stage.val ∧
      replayValidHandle history handle ∧ tool ∈ I.eligible handle.stage ∧ tool ∉ historyUsed history ∧
      ∀ pair ∈ historyCommitments history, pair.1.stage ≠ handle.stage
  | .execute handle tool => replayValidHandle history handle ∧ tool ∈ I.eligible handle.stage ∧
      (handle, tool) ∈ historyCommitments history ∧
      (∀ pair ∈ historyExecutions history, pair.2 ≠ tool) ∧
      (∀ pair ∈ historyExecutions history, pair.1.stage ≠ handle.stage)
  | .stop | .abandon => True

instance replayAllowsAction_decidable (available : Finset I.Tool) (history : List (VisibleEvent I))
    (action : Action I) : Decidable (replayAllowsAction available history action) := by
  cases action <;> dsimp only [replayAllowsAction] <;> infer_instance

theorem replayValidHandle_sound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (handle : MismatchHandle I) (hhandle : replayValidHandle s.history handle) : validHandle s handle := by
  unfold replayValidHandle at hhandle
  rw [prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp handle.stage] at hhandle
  cases ht : s.ledger.reportTime handle.stage with
  | none => simp only [ht, Option.map_none] at hhandle
  | some time =>
    simp only [ht, Option.map_some] at hhandle
    rw [prefix_historyWritten input C mode accounting rule seed truth tapes hp handle.stage,
      prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp handle.stage] at hhandle
    exact ⟨hhandle.1, hhandle.2.1, time, ht⟩

/-- Sound on EVERY native prefix, for every truth and tape, not only under
the conditional seed law or on a positive-probability source event. -/
theorem replayAllowsAction_sound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n s) (ha : s.halted = false)
    (available : Finset I.Tool) (action : Action I) (hallow : replayAllowsAction available s.history action) :
    ∃ next, Step input C .uncapped accounting tapes s action next := by
  cases action with
  | review stage =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage = none at hallow
    rw [prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp,
      prefix_historyWritten input C .uncapped accounting rule seed truth tapes hp stage] at hallow
    exact ⟨_, .review s stage ⟨ha, hallow.1⟩ hallow.2 (.inl rfl)⟩
  | write stage bit =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage = none at hallow
    rw [prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp,
      prefix_historyWritten input C .uncapped accounting rule seed truth tapes hp stage] at hallow
    exact ⟨_, .write s stage bit ⟨ha, hallow.1⟩ hallow.2 (.inl rfl)⟩
  | advance stage =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage ≠ none at hallow
    rw [prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp,
      prefix_historyWritten input C .uncapped accounting rule seed truth tapes hp stage] at hallow
    exact ⟨_, .advance s stage ⟨ha, hallow.1⟩ hallow.2 (.inl rfl)⟩
  | allocate handle tool =>
    obtain ⟨_, hcursor, hvalid, hcompat, hunused, hstage⟩ := hallow
    have hc : s.cursor = handle.stage.val := by
      simpa only [prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp] using hcursor
    have hv := replayValidHandle_sound input C hearly .uncapped accounting rule seed truth tapes hp handle hvalid
    have hu := (prefix_historyUnused_iff input C .uncapped accounting rule seed truth tapes hp tool).mp hunused
    have hs : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ handle.stage := by
      intro a hm
      apply hstage (a.handle, a.tool)
      rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨a, hm, rfl⟩
    exact ⟨_, .allocate s handle tool ha hv hcompat hu hs (fun _ => hc) (.inl rfl)⟩
  | execute handle tool =>
    obtain ⟨hvalid, hcompat, hcommit, hunused, hstage⟩ := hallow
    have hv := replayValidHandle_sound input C hearly .uncapped accounting rule seed truth tapes hp handle hvalid
    have hc : ∃ a ∈ s.ledger.commitments, a.handle = handle ∧ a.tool = tool := by
      rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp] at hcommit
      obtain ⟨a, hm, heq⟩ := List.mem_map.mp hcommit
      exact ⟨a, hm, congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    have hu : ∀ e ∈ s.ledger.executions, e.tool ≠ tool := by
      intro e hm
      apply hunused (e.handle, e.tool)
      rw [prefix_historyExecutions input C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨e, hm, rfl⟩
    have hs : ∀ e ∈ s.ledger.executions, e.handle.stage ≠ handle.stage := by
      intro e hm
      apply hstage (e.handle, e.tool)
      rw [prefix_historyExecutions input C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨e, hm, rfl⟩
    have hw : executionOpen C s handle.stage := by
      intro hcurrent
      rw [hdeferred] at hcurrent
      cases hcurrent
    exact ⟨_, .execute s handle tool ha hv hcompat hc hu hs hw (.inl rfl)⟩
  | stop => exact ⟨_, .stop s ha⟩
  | abandon => exact ⟨_, .abandon s ha⟩

def guardedReplayRule {Seed : Type*} (available : Finset I.Tool) (raw : PolicyRule I Seed) : PolicyRule I Seed :=
  fun seed history => if replayAllowsAction available history (raw seed history) then raw seed history else .abandon

theorem guardedReplayRule_legal (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) {Seed : Type*} (available : Finset I.Tool) (raw : PolicyRule I Seed) :
    LegalRule input C .uncapped accounting (guardedReplayRule available raw) := by
  intro seed truth tapes n s hp ha
  by_cases hallow : replayAllowsAction available s.history (raw seed s.history)
  · obtain ⟨next, hs⟩ := replayAllowsAction_sound input C hearly hdeferred accounting
      (guardedReplayRule available raw) seed truth tapes hp ha available _ hallow
    exact ⟨next, by simpa only [guardedReplayRule, hallow, ↓reduceIte] using hs⟩
  · exact ⟨stopState s true, by simpa only [guardedReplayRule, hallow, ↓reduceIte] using Step.abandon s ha⟩

theorem guardedReplayRule_usesOnly (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (available : Finset I.Tool) (raw : PolicyRule I Seed) :
    UsesOnly input C accounting (guardedReplayRule available raw) available := by
  intro seed truth tapes n s _ _ handle tool haction
  by_cases hallow : replayAllowsAction available s.history (raw seed s.history)
  · have heq : raw seed s.history = .allocate handle tool := by
      simpa only [guardedReplayRule, hallow, ↓reduceIte] using haction
    rw [heq] at hallow
    exact hallow.1
  · simp only [guardedReplayRule, hallow, ↓reduceIte] at haction
    cases haction

noncomputable def replayedSuffixCandidate {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (startup : Startup I) : PolicyRule (I.freshSuffix first) Seed :=
  fun seed history => match replaySuffixHistory first accounting rule seed startup history with
  | none => .abandon
  | some cache => suffixActionAtPublicCache first accounting rule seed cache history

section CompiledPolicy

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_guardedReplayRule (available : Finset I.Tool) (raw : PolicyRule I Seed)
    (hm : MeasurableRule raw) : MeasurableRule (guardedReplayRule available raw) := by
  exact (measurable_of_countable (fun pair : List (VisibleEvent I) × Action I =>
    if replayAllowsAction available pair.1 pair.2 then pair.2 else .abandon)).comp (measurable_snd.prodMk hm)

theorem measurable_replayedSuffixCandidate (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) (startup : Startup I) :
    MeasurableRule (replayedSuffixCandidate first accounting rule startup) := by
  apply measurable_from_prod_countable_left
  intro history
  have hc : Measurable (fun seed : Seed => replaySuffixHistory first accounting rule seed startup history) :=
    (measurable_replaySuffixHistory first accounting rule hrule).comp
      ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  have ha : Measurable (fun pair : Seed × Option (Startup I) => match pair.2 with
      | none => (Action.abandon : Action (I.freshSuffix first))
      | some cache => suffixActionAtPublicCache first accounting rule pair.1 cache history) := by
    apply measurable_from_prod_countable_left
    intro cache
    cases cache with
    | none => exact measurable_const
    | some cache =>
      exact (measurable_suffixActionAtPublicCache first accounting rule hrule).comp
        ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  exact ha.comp (measurable_id.prodMk hc)

/-- A concrete legal available-tool suffix policy, uniform over every truth,
tape and seed. Correctness on the selected entry event still needs the
source/target replay invariant; legality is NOT assumed from that invariant.
The source policy's pending/new delayed executions are accepted by the guard. -/
noncomputable def replayedSuffixAvailablePolicy (input : StatisticalInput I) (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule)
    (startup : Startup I) :
    AvailablePolicy (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) startup.availableTools Seed := by
  let raw := replayedSuffixCandidate first accounting rule startup
  exact ⟨{
    rule := guardedReplayRule startup.availableTools raw
    measurable_rule := measurable_guardedReplayRule (I := I.freshSuffix first) startup.availableTools raw
      (measurable_replayedSuffixCandidate first accounting rule hrule startup)
    legal := guardedReplayRule_legal (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      rfl rfl (zeroNormalAccounting (I.freshSuffix first)) startup.availableTools raw },
    guardedReplayRule_usesOnly (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) startup.availableTools raw⟩

end CompiledPolicy

/-- Every REAL early Native prefix is a concatenation of atomic packets;
the parser does not reject a source/target prefix because of an artificial
half-written state. No success or termination restriction is used. -/
theorem prefix_suffixPacket_history (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∃ packets : List (SuffixPacket I), packets.flatMap SuffixPacket.events = s.history := by
  induction hp with
  | initial => exact ⟨[], rfl⟩
  | @next n s next earlier hs ih =>
    obtain ⟨packets, hflat⟩ := ih
    generalize ha : rule seed s.history = action at hs
    cases hs with
    | review stage live port resources =>
      refine ⟨packets ++ [.review stage (tapes stage (s.ledger.reviews stage).toNat).val], ?_⟩
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, SuffixPacket.events, hflat]
      rfl
    | write stage bit live port resources =>
      refine ⟨packets ++ [.write stage bit (s.ledger.truth stage) s.clock], ?_⟩
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, SuffixPacket.events, hflat,
        record, writeResponses, hearly, ite_true, writeLedger]
      rfl
    | allocate handle tool active valid compatible unused unallocated window resources =>
      refine ⟨packets ++ [.allocate handle tool], ?_⟩
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, SuffixPacket.events, hflat]
      rfl
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      refine ⟨packets ++ [.execute handle tool], ?_⟩
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_nil, SuffixPacket.events, hflat]
      rfl
    | advance stage live written resources =>
      refine ⟨packets ++ [.advance stage], ?_⟩
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, SuffixPacket.events, hflat]
      rfl
    | stop active =>
      refine ⟨packets ++ [.stop], ?_⟩
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, SuffixPacket.events, hflat]
      rfl
    | abandon active =>
      refine ⟨packets ++ [.abandon], ?_⟩
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, SuffixPacket.events, hflat]
      rfl

theorem prefix_parseSuffixPackets (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∃ packets, parseSuffixPackets s.history = some packets ∧ packets.flatMap SuffixPacket.events = s.history := by
  obtain ⟨packets, hflat⟩ := prefix_suffixPacket_history input C hearly mode accounting rule seed truth tapes hp
  exact ⟨packets, by rw [← hflat, parseSuffixPackets_packets], hflat⟩

section PastSeedPolicy

variable {Seed : Type*} [MeasurableSpace Seed]

/-- The conditional comparison can retain the whole OLD world in its new
seed. The executable source callback only reads the ORIGINAL seed projection;
the fresh world is still solely the native system's hidden world argument. -/
noncomputable def replayedSuffixPastAvailablePolicy (input : StatisticalInput I) (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule)
    (startup : Startup I) :
    AvailablePolicy (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) startup.availableTools (Seed × PastWorldAt input first) := by
  let pastRule : PolicyRule I (Seed × PastWorldAt input first) := fun pair => rule pair.1
  have hm : MeasurableRule pastRule :=
    hrule.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact replayedSuffixAvailablePolicy input first accounting pastRule hm startup

end PastSeedPolicy

section EntryReachability

variable {Seed : Type*}

theorem entryStartupAt_some_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (next : I.Stage) (n : ℕ) (sample : Seed × input.World) (startup : Startup I) :
    entryStartupAt input C mode accounting rule next n sample = some startup ↔
      FirstEntryAt input C mode accounting rule next.val n sample ∧
        publicStartup (run input C mode accounting rule sample n) = startup := by
  classical
  by_cases he : FirstEntryAt input C mode accounting rule next.val n sample <;>
    simp only [entryStartupAt, he, ↓reduceIte, Option.some.injEq, true_and, false_and, reduceCtorEq]

noncomputable def pastEntryGate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (next : I.Stage) (n : ℕ) (startup : Startup I) (gate : Set Seed) : Set (Seed × PastWorldAt input next.val) :=
  {sample | sample.1 ∈ gate ∧ entryStartupAt input C mode accounting rule next n
    (sample.1, completePastWorld input next sample.2) = some startup}

theorem joinPastFresh_old (input : StatisticalInput I) (next : I.Stage)
    (past : PastWorldAt input next.val) (fresh : (input.freshSuffix next.val).World)
    (stage : I.Stage) (hstage : stage.val < next.val) :
    joinPastFresh input next.val past fresh stage = completePastWorld input next past stage := by
  have hp := congrFun (pastViewAt_joinPastFresh input next.val past fresh) ⟨stage, hstage⟩
  exact hp.trans (completePastWorld_apply_past input next past stage hstage).symm

/-- ALL fresh worlds preserve the selected real first entry. This is a
pointwise operational fact, not an almost-sure regular conditional law. -/
theorem pastEntryGate_firstEntry (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (next : I.Stage) (n : ℕ)
    (startup : Startup I) (gate : Set Seed) (sample : Seed × PastWorldAt input next.val)
    (hgate : sample ∈ pastEntryGate input C mode accounting rule next n startup gate)
    (fresh : (input.freshSuffix next.val).World) :
    FirstEntryAt input C mode accounting rule next.val n (joinPastFreshSample input next.val (sample, fresh)) ∧
      publicStartup (run input C mode accounting rule (joinPastFreshSample input next.val (sample, fresh)) n) = startup ∧
      sample.1 ∈ gate := by
  have heq := entryStartupAt_eq_of_past input C mode accounting rule hlegal sample.1
    (completePastWorld input next sample.2) (joinPastFresh input next.val sample.2 fresh) next n
    (fun stage hs => joinPastFresh_old input next sample.2 fresh stage hs)
  have hs : entryStartupAt input C mode accounting rule next n
      (joinPastFreshSample input next.val (sample, fresh)) = some startup := heq.trans hgate.2
  have h := (entryStartupAt_some_iff input C mode accounting rule next n _ startup).mp hs
  exact ⟨h.1, h.2, hgate.1⟩

theorem pastEntryGate_mem_historyGate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (next : I.Stage) (n : ℕ)
    (startup : Startup I) (gate : Set Seed) (sample : Seed × PastWorldAt input next.val)
    (hgate : sample ∈ pastEntryGate input C mode accounting rule next n startup gate)
    (fresh : (input.freshSuffix next.val).World) :
    joinPastFreshSample input next.val (sample, fresh) ∈ historyGate input C mode accounting rule n startup gate := by
  obtain ⟨_, hs, hg⟩ := pastEntryGate_firstEntry input C mode accounting rule hlegal next n startup gate sample hgate fresh
  exact ⟨hs, hg⟩

/-- The fixed PUBLIC cache restores a reachable source state for every new
truth/tape world. The fresh truth remains a SYSTEM argument of this proof. -/
theorem pastEntryGate_sourcePrefix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (next : I.Stage) (n : ℕ)
    (startup : Startup I) (gate : Set Seed) (sample : Seed × PastWorldAt input next.val)
    (hgate : sample ∈ pastEntryGate input C mode accounting rule next n startup gate)
    (fresh : (input.freshSuffix next.val).World) :
    let world := joinPastFresh input next.val sample.2 fresh
    ∃ m ≤ n, Prefix input C mode accounting rule sample.1 (input.truthAt world) (worldTapes input world) m
      (startup.restore (input.truthAt world)) := by
  let world := joinPastFresh input next.val sample.2 fresh
  obtain ⟨_, hs, _⟩ := pastEntryGate_firstEntry input C mode accounting rule hlegal next n startup gate sample hgate fresh
  change publicStartup (run input C mode accounting rule (sample.1, world) n) = startup at hs
  obtain ⟨m, hmn, hp⟩ := run_has_prefix input C mode accounting rule hlegal (sample.1, world) n
  have htruth := run_truth input C mode accounting rule hlegal (sample.1, world) n
  have hstate : run input C mode accounting rule (sample.1, world) n = startup.restore (input.truthAt world) := by
    calc
      _ = (publicStartup (run input C mode accounting rule (sample.1, world) n)).restore
          (run input C mode accounting rule (sample.1, world) n).ledger.truth := (restore_publicStartup _).symm
      _ = _ := by rw [hs, htruth]
  rw [hstate] at hp
  exact ⟨m, hmn, hp⟩

variable [MeasurableSpace Seed]

theorem measurableSet_pastEntryGate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hm : MeasurableRule rule) (next : I.Stage) (n : ℕ) (startup : Startup I)
    (gate : Set Seed) (hgate : MeasurableSet gate) :
    MeasurableSet (pastEntryGate input C mode accounting rule next n startup gate) := by
  have hc : Measurable (fun sample : Seed × PastWorldAt input next.val =>
      (sample.1, completePastWorld input next sample.2)) :=
    measurable_fst.prodMk ((measurable_completePastWorld input next).comp measurable_snd)
  have hr := (measurable_entryStartupAt input C mode accounting rule hm next n).comp hc
  exact (measurable_fst hgate).inter (hr (measurableSet_singleton (some startup)))

end EntryReachability

/-- Every real native step supplies its genuine atomic packet and the
public updater computes EXACTLY that successor. This includes executions
after their allocation stage, and stop/abandon preserve all previous bills. -/
theorem nativeStep_suffixPacket (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {s next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes s action next) :
    ∃ packet : SuffixPacket I, packet.action = action ∧
      next.history = s.history ++ packet.events ∧
      applySuffixPacketPublic accounting (publicStartup s) action packet = some (publicStartup next) := by
  cases hs with
  | review stage live port resources =>
    refine ⟨.review stage (tapes stage (s.ledger.reviews stage).toNat).val, rfl, rfl, ?_⟩
    exact congrArg some (publicStartup_review accounting s stage _).symm
  | write stage bit live port resources =>
    refine ⟨.write stage bit (s.ledger.truth stage) s.clock, rfl, ?_, ?_⟩
    · simp only [record, SuffixPacket.events, writeResponses, hearly, ite_true, writeLedger]
      rfl
    · exact congrArg some (publicStartup_write_early C hearly accounting s stage bit).symm
  | allocate handle tool active valid compatible unused unallocated window resources =>
    refine ⟨.allocate handle tool, rfl, rfl, ?_⟩
    exact congrArg some (publicStartup_allocate accounting s handle tool).symm
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    refine ⟨.execute handle tool, rfl, rfl, ?_⟩
    exact congrArg some (publicStartup_execute accounting s handle tool).symm
  | advance stage live written resources =>
    refine ⟨.advance stage, rfl, rfl, ?_⟩
    exact congrArg some (publicStartup_advance accounting s stage).symm
  | stop active =>
    refine ⟨.stop, rfl, rfl, ?_⟩
    exact congrArg some (publicStartup_stop s false).symm
  | abandon active =>
    refine ⟨.abandon, rfl, rfl, ?_⟩
    exact congrArg some (publicStartup_stop s true).symm

/-- Lower a visible packet using the REAL suffix clock and serial table.
No report is created by this operation; an existing report bit is copied. -/
def SuffixPacket.lower (first : ℕ) (clock : ℕ)
    (before : List (VisibleEvent (I.freshSuffix first))) :
    SuffixPacket I → Option (SuffixPacket (I.freshSuffix first))
  | .review stage symbol => if hf : first ≤ stage.val then
      some (.review (suffixStageOf first stage hf) symbol) else none
  | .write stage bit truth _ => if hf : first ≤ stage.val then
      some (.write (suffixStageOf first stage hf) bit truth clock) else none
  | .allocate handle tool => if hf : first ≤ handle.stage.val then
      some (.allocate (suffixHandleOf first before handle hf) tool) else none
  | .execute handle tool => if hf : first ≤ handle.stage.val then
      some (.execute (suffixHandleOf first before handle hf) tool) else none
  | .advance stage => if hf : first ≤ stage.val then some (.advance (suffixStageOf first stage hf)) else none
  | .stop => some .stop
  | .abandon => some .abandon

theorem SuffixPacket.lower_action (first : ℕ) (clock : ℕ)
    (before : List (VisibleEvent (I.freshSuffix first))) (packet : SuffixPacket I) :
    (packet.lower first clock before).map SuffixPacket.action = suffixActionOf first before packet.action := by
  cases packet <;> simp only [SuffixPacket.lower, SuffixPacket.action, suffixActionOf]
  all_goals first | rfl | (split <;> rfl)

/-- Dynamic serial lowering changes only stage/handle identities. The exact
same real symbol/report therefore gives the exact same original-cache update. -/
theorem applySuffixPacketPublic_lower (accounting : NormalAccounting I) (startup : Startup I)
    (first clock : ℕ) (before : List (VisibleEvent (I.freshSuffix first)))
    (packet : SuffixPacket I) (lowered : SuffixPacket (I.freshSuffix first))
    (hlower : packet.lower first clock before = some lowered) :
    applySuffixPacketPublic accounting startup packet.action lowered =
      applySuffixPacketPublic accounting startup packet.action packet := by
  cases packet <;> simp only [SuffixPacket.lower] at hlower
  all_goals try split at hlower
  all_goals cases hlower
  all_goals rfl

/-- Concrete one-packet correctness on a REAL source continuation. The
source step and its true response packet are constructed from source
legality after bounded old execution simulation. Their dynamically lowered
packet is accepted by the implemented replay and yields exactly the real
source successor's public state. The remaining full-run bridge must show
that this lowered packet is also the next REAL target response packet. -/
theorem replaySuffixPacket_actual (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (first n clock : ℕ)
    (before : List (VisibleEvent (I.freshSuffix first)))
    (hcursor : first ≤ (run input C mode accounting rule sample n).cursor)
    (hactive : (settleOldExecutions first accounting rule (I.toolCount + 1) sample.1
      (publicStartup (run input C mode accounting rule sample n))).1.halted = false) :
    let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1
      (publicStartup (run input C mode accounting rule sample n))
    ∃ (next : State I) (packet : SuffixPacket I) (lowered : SuffixPacket (I.freshSuffix first)),
      Step input C mode accounting (worldTapes input sample.2)
        (run input C mode accounting rule sample (n + result.2)) (rule sample.1 result.1.history) next ∧
      packet.action = rule sample.1 result.1.history ∧
      next.history = (run input C mode accounting rule sample (n + result.2)).history ++ packet.events ∧
      packet.lower first clock before = some lowered ∧
      replaySuffixPacket first accounting rule sample.1 (publicStartup (run input C mode accounting rule sample n))
        before lowered = some (publicStartup next) := by
  let start := publicStartup (run input C mode accounting rule sample n)
  let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1 start
  have hr : result.1 = publicStartup (run input C mode accounting rule sample (n + result.2)) :=
    settleOldExecutions_actual input C mode accounting rule hlegal sample first _ n
  obtain ⟨next, hs, haction⟩ := suffixActionAtPublicCache_actual input C mode accounting rule hlegal hcurrent
    sample first n before hcursor hactive
  obtain ⟨packet, ha, hh, hupdate⟩ := nativeStep_suffixPacket input C hearly mode accounting _ hs
  have hproject := SuffixPacket.lower_action first clock before packet
  cases hlower : packet.lower first clock before with
  | none =>
    rw [hlower, Option.map_none, ha, haction] at hproject
    cases hproject
  | some lowered =>
    refine ⟨next, packet, lowered, hs, ha, hh, hlower, ?_⟩
    have hmatch : suffixActionOf first before (rule sample.1 result.1.history) = some lowered.action := by
      rw [hlower, Option.map_some, ha] at hproject
      exact hproject.symm
    have hup : applySuffixPacketPublic accounting result.1 (rule sample.1 result.1.history) lowered =
        some (publicStartup next) := by
      rw [← ha, applySuffixPacketPublic_lower accounting result.1 first clock before packet lowered hlower, hr]
      rw [← ha] at hupdate
      exact hupdate
    change result.1.halted = false at hactive
    change (if result.1.halted then none else
      if suffixActionOf first before (rule sample.1 result.1.history) = some lowered.action then
        applySuffixPacketPublic accounting result.1 (rule sample.1 result.1.history) lowered else none) = _
    rw [hactive]
    simpa only [Bool.false_eq_true, ↓reduceIte, hmatch, ↓reduceIte] using hup

end PaperProofs.Common.Native
