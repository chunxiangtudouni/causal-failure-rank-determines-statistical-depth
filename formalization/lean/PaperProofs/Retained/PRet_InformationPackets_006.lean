module

public import PaperProofs.Retained.PRet_PublicAdministrativeReplay_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetInformationPackets006

open Common Common.Native PRetPublicAdministrativeReplay005 MeasureTheory

variable {I : Instance}

/-- Source information packets contain only genuine observations and the
ordinary write/early-report pair. No allocation, execution, advance, hidden
truth, future review, or successful-path selector is supplied. -/
inductive Packet (I : Instance) where
  | review (stage : I.Stage) (symbol : ℕ)
  | write (stage : I.Stage) (bit truth : Bool)
  deriving Countable, DecidableEq

instance : MeasurableSpace (Packet I) := ⊤
instance : MeasurableSingletonClass (Packet I) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def Packet.action : Packet I → Action I
  | .review stage _ => .review stage
  | .write stage bit _ => .write stage bit

def Packet.events : Packet I → List (VisibleEvent I)
  | .review stage symbol => [.observation stage symbol]
  | .write stage bit truth => [.wrote stage bit 0, .report stage truth 0]

def parse : List (VisibleEvent I) → Option (List (Packet I))
  | [] => some []
  | .observation stage symbol :: later => (parse later).map (Packet.review stage symbol :: ·)
  | .wrote stage bit _ :: .report stage' truth _ :: later =>
      if stage = stage' then (parse later).map (Packet.write stage bit truth :: ·) else none
  | _ => none

theorem parse_packet_append (packet : Packet I) (history : List (VisibleEvent I)) :
    parse (packet.events ++ history) = (parse history).map (packet :: ·) := by
  cases packet <;> simp [Packet.events, parse]

theorem parse_packets (packets : List (Packet I)) : parse (packets.flatMap Packet.events) = some packets := by
  induction packets with
  | nil => rfl
  | cons packet later ih => simp only [List.flatMap_cons, parse_packet_append, ih, Option.map_some]

noncomputable def Packet.applyPublic (accounting : NormalAccounting I) (startup : Startup I) : Packet I → Startup I
  | .review stage symbol => startup.reviewPublic accounting stage symbol
  | .write stage bit truth => startup.writePublic accounting stage bit truth

theorem Packet.applyPublic_information (accounting : NormalAccounting I) (startup : Startup I) (packet : Packet I) :
    informationTrace (packet.applyPublic accounting startup).history = informationTrace startup.history ++ packet.events := by
  cases packet <;> simp [Packet.applyPublic, Startup.reviewPublic, Startup.writePublic,
    informationTrace, informationEvent, Packet.events, List.filterMap_append,
    List.filterMap_nil]

noncomputable def consume {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (packet : Packet I) : Option (Startup I) :=
  if startup.halted = false ∧ rule seed startup.history = packet.action then
    some (settle accounting rule (I.stageCount + 2 * I.toolCount + 2) seed
      (packet.applyPublic accounting startup)).1
  else none

noncomputable def replay {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) : Option (Startup I) :=
  let empty := publicStartup (initial (I := I) (fun _ => false))
  let started := (settle accounting rule (I.stageCount + 2 * I.toolCount + 2) seed empty).1
  packets.foldlM (consume accounting rule seed) started

noncomputable def shadow {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (history : List (VisibleEvent I)) : Option (Startup I) := do
  let packets ← parse (informationTrace history)
  replay accounting rule seed packets

/-- One consumed source response preserves the existing whole shadow
history and adds exactly the new real information packet. Administrative
closure adds no information even if the source later stops or abandons. -/
theorem consume_information {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (startup next : Startup I) (packet : Packet I)
    (hconsume : consume accounting rule seed startup packet = some next) :
    informationTrace next.history = informationTrace startup.history ++ packet.events := by
  classical
  unfold consume at hconsume
  split at hconsume
  · have heq := Option.some.inj hconsume
    subst next
    rw [settle_information, Packet.applyPublic_information]
  · cases hconsume

theorem fold_packets_information {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) (startup next : Startup I)
    (hfold : packets.foldlM (consume accounting rule seed) startup = some next) :
    informationTrace next.history = informationTrace startup.history ++ packets.flatMap Packet.events := by
  induction packets generalizing startup with
  | nil =>
    have heq : startup = next := Option.some.inj hfold
    subst next
    simp only [List.flatMap_nil, List.append_nil]
  | cons packet later ih =>
    change (consume accounting rule seed startup packet).bind
      (fun next => later.foldlM (consume accounting rule seed) next) = some next at hfold
    obtain ⟨middle, hconsume, htail⟩ := Option.bind_eq_some_iff.mp hfold
    rw [ih middle htail, consume_information accounting rule seed startup middle packet hconsume,
      List.flatMap_cons, List.append_assoc]

theorem replay_information {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) (next : Startup I)
    (hreplay : replay accounting rule seed packets = some next) :
    informationTrace next.history = packets.flatMap Packet.events := by
  have ht := fold_packets_information accounting rule seed packets _ next hreplay
  rw [settle_information] at ht
  simpa only [publicStartup, initial, informationTrace, List.filterMap_nil, List.nil_append] using ht

section Measurable

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_consume (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hrule : MeasurableRule rule) (packet : Packet I) :
    Measurable (fun sample : Seed × Startup I => consume accounting rule sample.1 sample.2 packet) := by
  have hh : Measurable (fun sample : Seed × Startup I => sample.2.history) :=
    (measurable_of_countable (fun startup : Startup I => startup.history)).comp measurable_snd
  have ha := hrule.comp (measurable_fst.prodMk hh)
  have hactive : MeasurableSet {sample : Seed × Startup I | sample.2.halted = false} :=
    (measurable_of_countable (fun startup : Startup I => startup.halted)).comp measurable_snd (measurableSet_singleton false)
  have hcondition : MeasurableSet {sample : Seed × Startup I |
      sample.2.halted = false ∧ rule sample.1 sample.2.history = packet.action} :=
    hactive.inter (ha (measurableSet_singleton packet.action))
  have hinput : Measurable (fun sample : Seed × Startup I =>
      (sample.1, packet.applyPublic accounting sample.2)) :=
    measurable_fst.prodMk ((measurable_of_countable (fun startup : Startup I =>
      packet.applyPublic accounting startup)).comp measurable_snd)
  have hs := (measurable_settle accounting rule hrule (I.stageCount + 2 * I.toolCount + 2)).comp hinput
  have hsome : Measurable (fun sample : Seed × Startup I =>
      some (settle accounting rule (I.stageCount + 2 * I.toolCount + 2) sample.1
        (packet.applyPublic accounting sample.2)).1) :=
    (measurable_of_countable (fun result : Startup I × ℕ => some result.1)).comp hs
  exact Measurable.ite hcondition hsome measurable_const

private theorem measurable_option_bind {α : Type*} [MeasurableSpace α]
    (f : α → Option (Startup I)) (g : α → Startup I → Option (Startup I))
    (hf : Measurable f) (hg : Measurable (fun pair : α × Startup I => g pair.1 pair.2)) :
    Measurable (fun sample => (f sample).bind (g sample)) := by
  have hm : Measurable (fun pair : α × Option (Startup I) => pair.2.bind (g pair.1)) := by
    apply measurable_from_prod_countable_left
    intro option
    cases option with
    | none => exact measurable_const
    | some startup => exact hg.comp (measurable_id.prodMk measurable_const)
  exact hm.comp (measurable_id.prodMk hf)

theorem measurable_fold_packets (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hrule : MeasurableRule rule) (packets : List (Packet I)) :
    Measurable (fun sample : Seed × Startup I => packets.foldlM (consume accounting rule sample.1) sample.2) := by
  induction packets with
  | nil => exact (measurable_of_countable (fun startup : Startup I => some startup)).comp measurable_snd
  | cons packet later ih =>
    apply measurable_option_bind
      (fun sample : Seed × Startup I => consume accounting rule sample.1 sample.2 packet)
      (fun sample next => later.foldlM (consume accounting rule sample.1) next)
      (measurable_consume accounting rule hrule packet)
    exact ih.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem measurable_replay (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hrule : MeasurableRule rule) (packets : List (Packet I)) :
    Measurable (fun seed => replay accounting rule seed packets) := by
  let empty := publicStartup (initial (I := I) (fun _ => false))
  have hs := (measurable_settle accounting rule hrule (I.stageCount + 2 * I.toolCount + 2)).comp
    (measurable_id.prodMk (measurable_const (a := empty)))
  have hstarted : Measurable (fun seed : Seed =>
      (settle accounting rule (I.stageCount + 2 * I.toolCount + 2) seed empty).1) := measurable_fst.comp hs
  exact (measurable_fold_packets accounting rule hrule packets).comp (measurable_id.prodMk hstarted)

/-- Arbitrary measurable private Seed universes are preserved. The shadow
uses only the current finite public history; no source/world oracle occurs. -/
theorem measurable_shadow (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hrule : MeasurableRule rule) :
    Measurable (fun sample : Seed × List (VisibleEvent I) => shadow accounting rule sample.1 sample.2) := by
  apply measurable_from_prod_countable_left
  intro history
  cases hp : parse (informationTrace history) with
  | none => simpa only [shadow, hp, Option.bind_eq_bind, Option.bind_none] using (measurable_const (a := (none : Option (Startup I))) : Measurable (fun _ : Seed => none))
  | some packets => simpa only [shadow, hp, Option.bind_eq_bind, Option.bind_some] using measurable_replay accounting rule hrule packets

end Measurable

end PaperProofs.Retained.PRetInformationPackets006
