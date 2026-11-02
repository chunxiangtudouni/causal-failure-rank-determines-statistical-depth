module

public import PaperProofs.Retained.PRet_ActionOrigins_019
public import PaperProofs.Retained.PRet_ReplayConsequences_017

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetPaymentPrefix021

open Common Common.Native PRetExactTerminal001 PRetInformationPackets006
open PRetDelayedPolicy010 PRetReplayInvariant016 PRetReplayConsequences017 PRetActionOrigins019

variable {I : Instance}

theorem prefix_append_next {α : Type*} (first later : List α) (next : α)
    (hp : first.IsPrefix later) (hn : later[first.length]? = some next) :
    (first ++ [next]).IsPrefix later := by
  obtain ⟨suffix, rfl⟩ := hp
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hn
  cases suffix with
  | nil => cases hn
  | cons head suffix =>
    have heq : head = next := Option.some.inj hn
    subst head
    exact ⟨suffix, by simp only [List.append_assoc, List.cons_append, List.nil_append]⟩

theorem raw_of_replay {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (history : List (VisibleEvent I)) (packets : List (Packet I)) (startup : Startup I)
    (hinfo : informationTrace history = packets.flatMap Packet.events)
    (hreplay : replay accounting source seed packets = some startup) :
    raw accounting source seed history = candidate startup (source seed startup.history) history := by
  have hs : shadow accounting source seed history = some startup := by
    unfold shadow
    rw [hinfo, parse_packets]
    exact hreplay
  rw [raw, hs]

/-- A delayed real execution extends the prefix of the ACTUAL source's paid
stage/tool list. Serial rebinding is harmless; no unused commitment or
alternative matching is inserted into the payment list. -/
theorem payment_prefix (source : Startup I) (history : List (VisibleEvent I))
    (executions : List (Execution I)) (handle : MismatchHandle I) (tool : I.Tool)
    (hcount : (historyExecutions history).length = executions.length)
    (hp : (executions.map executionPair).IsPrefix (source.executions.map executionPair))
    (ha : paymentAction source history = .execute handle tool) :
    ((executions ++ [(⟨handle, tool, 0⟩ : Execution I)]).map executionPair).IsPrefix (source.executions.map executionPair) := by
  obtain ⟨execution, hn, hstage, htool⟩ := paymentAction_execute source history handle tool ha
  have hn' : (source.executions.map executionPair)[(executions.map executionPair).length]? =
      some (handle.stage, tool) := by
    simp only [List.length_map, List.getElem?_map]
    rw [← hcount, hn]
    simp only [Option.map_some, executionPair, hstage, htool]
  simpa only [List.map_append, List.map_cons, List.map_nil, executionPair] using
    prefix_append_next (executions.map executionPair) (source.executions.map executionPair) (handle.stage, tool) hp hn'

theorem candidate_execution_prefix (source : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent I)) (executions : List (Execution I))
    (handle : MismatchHandle I) (tool : I.Tool) (clock : ℕ)
    (hcount : (historyExecutions history).length = executions.length)
    (hp : (executions.map executionPair).IsPrefix (source.executions.map executionPair))
    (ha : candidate source sourceAction history = .execute handle tool) :
    ((executions ++ [(⟨handle, tool, clock⟩ : Execution I)]).map executionPair).IsPrefix (source.executions.map executionPair) := by
  obtain ⟨execution, hn, hstage, htool⟩ := candidate_execute source sourceAction history handle tool ha
  have hn' : (source.executions.map executionPair)[(executions.map executionPair).length]? =
      some (handle.stage, tool) := by
    simp only [List.length_map, List.getElem?_map]
    rw [← hcount, hn]
    simp only [Option.map_some, executionPair, hstage, htool]
  simpa only [List.map_append, List.map_cons, List.map_nil, executionPair] using
    prefix_append_next (executions.map executionPair) (source.executions.map executionPair) (handle.stage, tool) hp hn'

end PaperProofs.Retained.PRetPaymentPrefix021
